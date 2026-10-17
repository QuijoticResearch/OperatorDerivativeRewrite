import Foundation.FourierPathDualGradientSeries

/-! Jointly bounded control/test gradients in the actual conjugate-exponent domain. -/
noncomputable section
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathDualGradient
open L1SeriesSynthesis FourierPathDualControls HigherHeatDyadicLaws HigherHeatFourierBanach
open HigherHeatFourierPathSemigroup FourierPathDirectionalOperator

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def postQuotient (m : ℕ) [Fact (0 < m)] :
    (Control m →L[ℝ] Coeff) →L[ℂ] (Control m →L[ℝ] TestSpace levels ξ) :=
  LinearMap.mkContinuous
    { toFun := fun b => ((kernel levels ξ).mkQL.restrictScalars ℝ).comp b
      map_add' := by intro b c; ext u; exact map_add (kernel levels ξ).mkQ (b u) (c u)
      map_smul' := by intro c b; ext u; exact map_smul (kernel levels ξ).mkQ c (b u) }
    1 (fun b => by
      simp only [one_mul]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg b)
      intro u
      exact (Submodule.Quotient.norm_mk_le (kernel levels ξ) (b u)).trans (b.le_opNorm u))

theorem postQuotient_bound (m : ℕ) [Fact (0 < m)] : ‖postQuotient levels ξ m‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

def coefficientFamily (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T) :
    Coeff →L[ℂ] (Control m →L[ℝ] TestSpace levels ξ) :=
  (postQuotient levels ξ m).comp (FourierPathDualGradientSeries.family levels ξ m T hT)

theorem coefficientFamily_bound (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T) :
    ‖coefficientFamily levels ξ m T hT‖ ≤ 1+(T : ℝ)⁻¹ := by
  calc
    _ ≤ ‖postQuotient levels ξ m‖ * ‖FourierPathDualGradientSeries.family levels ξ m T hT‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*(1+(T : ℝ)⁻¹) := mul_le_mul (postQuotient_bound levels ξ m)
      (FourierPathDualGradientSeries.family_bound levels ξ m T hT) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem kernel_le_family (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T) :
    kernel levels ξ ≤ (coefficientFamily levels ξ m T hT).ker := by
  intro a ha
  apply ContinuousLinearMap.ext
  intro u
  change (kernel levels ξ).mkQ (FourierPathDualGradientSeries.family levels ξ m T hT a u) = 0
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (FourierPathDualGradientSeries.family_preserves_kernel levels ξ m T hT a ha u)

def gradient (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T) :
    TestSpace levels ξ →L[ℂ] (Control m →L[ℝ] TestSpace levels ξ) :=
  (kernel levels ξ).liftQL (coefficientFamily levels ξ m T hT) (kernel_le_family levels ξ m T hT)

theorem gradient_mk (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T) (a : Coeff) (u : Control m) :
    gradient levels ξ m T hT ((kernel levels ξ).mkQ a) u =
      (kernel levels ξ).mkQ (FourierPathDualGradientSeries.family levels ξ m T hT a u) := rfl

theorem gradient_bound (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) : ‖gradient levels ξ m T hT q‖ ≤ (1+(T : ℝ)⁻¹)*‖q‖ := by
  let C := 1+(T : ℝ)⁻¹
  have hC : 0 < C := by dsimp [C]; positivity
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a,ha,hna⟩ := Submodule.Quotient.norm_mk_lt q (div_pos hε hC)
  have he : gradient levels ξ m T hT q = coefficientFamily levels ξ m T hT a := by rw [← ha]; rfl
  rw [he]
  calc
    _ ≤ C*‖a‖ := (coefficientFamily levels ξ m T hT).le_of_opNorm_le
      (coefficientFamily_bound levels ξ m T hT) a
    _ ≤ C*‖q‖+ε := by
      have hh := mul_lt_mul_of_pos_left hna hC
      have hc : C*(ε/C)=ε := by field_simp
      nlinarith

theorem bilinear_bound (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (u : Control m) :
    ‖gradient levels ξ m T hT q u‖ ≤ (1+(T : ℝ)⁻¹)*‖q‖*‖u‖ :=
  (gradient levels ξ m T hT q).le_of_opNorm_le (gradient_bound levels ξ m T hT q) u

theorem gradient_graph (m : ℕ) [h : Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (u : Control m) :
    (evolution levels ξ m h.out T q, gradient levels ξ m T hT q u) ∈
      graph levels ξ (direction m u) := by
  obtain ⟨a,rfl⟩ := (kernel levels ξ).mkQ_surjective q
  rw [evolution_mk, gradient_mk]
  exact ⟨_, FourierPathDualGradientSeries.family_graph levels ξ m T hT a u, rfl⟩

theorem actual_path_derivative (m : ℕ) [h : Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (u : Control m) :
    HasDerivAt (fun t => HigherHeatFourierTranslationContinuity.along levels ξ (direction m u) t
      (evolution levels ξ m h.out T q)) (gradient levels ξ m T hT q u) 0 :=
  graph_deriv levels ξ (direction m u) _ (gradient_graph levels ξ m T hT q u)

theorem gradient_eq_individual (m : ℕ) [h : Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (u : Control m) :
    gradient levels ξ m T hT q u = FourierPathDualDamping.gradient levels ξ m u T hT q := by
  have h₁ := gradient_graph levels ξ m T hT q u
  have h₂ := FourierPathDualDamping.gradient_graph levels ξ m u T hT q
  have he := graph_deriv levels ξ (direction m u) _ h₁
  exact he.unique (graph_deriv levels ξ (direction m u) _ h₂)

end OperatorDerivativeRewrite.Foundation.FourierPathDualGradient
