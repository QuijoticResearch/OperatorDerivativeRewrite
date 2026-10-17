import Foundation.FourierPathDifferentialCommutation

/-! Actual bounded heat gradients from verified spectral damping, with kernel descent. -/
noncomputable section
open scoped lp NNReal ENNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.FourierPathHeatGradient
open L1SeriesSynthesis HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open FourierPathDirectionalCharacters FourierPathDirectionalOperator
open HigherHeatFourierPathSemigroup

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def symbol (h : Path) (m : ℕ) (T : ℝ≥0) (i : ℕ) : ℂ :=
  eigenvalue (frequency levels ξ h i)*multiplier levels ξ m T i

theorem term_bound (h : Path) (m : ℕ) (T : ℝ≥0) (C : ℝ) (hC : 0 < C)
    (hb : ∀ i, ‖symbol levels ξ h m T i‖ ≤ C) (i : ℕ) :
    ‖term (symbol levels ξ h m T) i‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC.le
  intro z
  change ‖z • symbol levels ξ h m T i‖ ≤ C*‖z‖
  rw [norm_smul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hb i) (norm_nonneg z)

def coefficientGradient (h : Path) (m : ℕ) (T : ℝ≥0) (C : ℝ) (hC : 0 < C)
    (hb : ∀ i, ‖symbol levels ξ h m T i‖ ≤ C) : Coeff →L[ℂ] Coeff :=
  lp.mapCLM 1 (term (symbol levels ξ h m T)) hC.le (term_bound levels ξ h m T C hC hb)

theorem coefficientGradient_bound (h : Path) (m : ℕ) (T : ℝ≥0) (C : ℝ) (hC : 0 < C)
    (hb : ∀ i, ‖symbol levels ξ h m T i‖ ≤ C) (a : Coeff) :
    ‖coefficientGradient levels ξ h m T C hC hb a‖ ≤ C*‖a‖ := by
  have hn : ‖coefficientGradient levels ξ h m T C hC hb‖ ≤ C := lp.norm_mapCLM_le 1 _ _ _
  exact (coefficientGradient levels ξ h m T C hC hb).le_of_opNorm_le hn a

theorem coefficientGradient_graph (h : Path) (m : ℕ) (T : ℝ≥0) (C : ℝ) (hC : 0 < C)
    (hb : ∀ i, ‖symbol levels ξ h m T i‖ ≤ C) (a : Coeff) :
    (coefficientEvolution levels ξ m T a,coefficientGradient levels ξ h m T C hC hb a) ∈
      coefficientGraph levels ξ h := by
  intro i
  change a i*(eigenvalue (frequency levels ξ h i)*multiplier levels ξ m T i)=
    (a i*multiplier levels ξ m T i)*eigenvalue (frequency levels ξ h i)
  ring

theorem gradient_preserves_kernel (h : Path) (m : ℕ) (hm : 0 < m) (T : ℝ≥0)
    (C : ℝ) (hC : 0 < C) (hb : ∀ i, ‖symbol levels ξ h m T i‖ ≤ C)
    (a : Coeff) (ha : a ∈ kernel levels ξ) :
    coefficientGradient levels ξ h m T C hC hb a ∈ kernel levels ξ := by
  have hg : ((kernel levels ξ).mkQ (coefficientEvolution levels ξ m T a),
      (kernel levels ξ).mkQ (coefficientGradient levels ξ h m T C hC hb a)) ∈ graph levels ξ h :=
    ⟨_,coefficientGradient_graph levels ξ h m T C hC hb a,rfl⟩
  have hqa : (kernel levels ξ).mkQ (coefficientEvolution levels ξ m T a)=0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (evolution_preserves_kernel levels ξ m hm T a ha)
  rw [hqa] at hg
  have hz := graph_vertical_zero levels ξ h _ hg rfl
  exact (Submodule.Quotient.mk_eq_zero _).mp hz

theorem gradient_kernel (h : Path) (m : ℕ) (hm : 0 < m) (T : ℝ≥0)
    (C : ℝ) (hC : 0 < C) (hb : ∀ i, ‖symbol levels ξ h m T i‖ ≤ C) :
    kernel levels ξ ≤
      (((kernel levels ξ).mkQL).comp (coefficientGradient levels ξ h m T C hC hb)).ker := by
  intro a ha
  change (kernel levels ξ).mkQ (coefficientGradient levels ξ h m T C hC hb a)=0
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (gradient_preserves_kernel levels ξ h m hm T C hC hb a ha)

def gradient (h : Path) (m : ℕ) (hm : 0 < m) (T : ℝ≥0)
    (C : ℝ) (hC : 0 < C) (hb : ∀ i, ‖symbol levels ξ h m T i‖ ≤ C) :
    TestSpace levels ξ →L[ℂ] TestSpace levels ξ :=
  (kernel levels ξ).liftQL (((kernel levels ξ).mkQL).comp
    (coefficientGradient levels ξ h m T C hC hb)) (gradient_kernel levels ξ h m hm T C hC hb)

theorem gradient_mk (h : Path) (m : ℕ) (hm : 0 < m) (T : ℝ≥0)
    (C : ℝ) (hC : 0 < C) (hb : ∀ i, ‖symbol levels ξ h m T i‖ ≤ C) (a : Coeff) :
    gradient levels ξ h m hm T C hC hb ((kernel levels ξ).mkQ a)=
      (kernel levels ξ).mkQ (coefficientGradient levels ξ h m T C hC hb a) := rfl

theorem gradient_graph (h : Path) (m : ℕ) (hm : 0 < m) (T : ℝ≥0)
    (C : ℝ) (hC : 0 < C) (hb : ∀ i, ‖symbol levels ξ h m T i‖ ≤ C) (q : TestSpace levels ξ) :
    (evolution levels ξ m hm T q,gradient levels ξ h m hm T C hC hb q) ∈ graph levels ξ h := by
  obtain ⟨a,rfl⟩ := (kernel levels ξ).mkQ_surjective q
  rw [evolution_mk, gradient_mk]
  exact ⟨_,coefficientGradient_graph levels ξ h m T C hC hb a,rfl⟩

theorem gradient_bound (h : Path) (m : ℕ) (hm : 0 < m) (T : ℝ≥0)
    (C : ℝ) (hC : 0 < C) (hb : ∀ i, ‖symbol levels ξ h m T i‖ ≤ C) (q : TestSpace levels ξ) :
    ‖gradient levels ξ h m hm T C hC hb q‖ ≤ C*‖q‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a,ha,hna⟩ := Submodule.Quotient.norm_mk_lt q (div_pos hε hC)
  have he : gradient levels ξ h m hm T C hC hb q=
      (kernel levels ξ).mkQ (coefficientGradient levels ξ h m T C hC hb a) := by
    rw [← ha]
    rfl
  rw [he]
  calc
    _ ≤ ‖coefficientGradient levels ξ h m T C hC hb a‖ := Submodule.Quotient.norm_mk_le _ _
    _ ≤ C*‖a‖ := coefficientGradient_bound levels ξ h m T C hC hb a
    _ ≤ C*‖q‖+ε := by
      have hh := mul_lt_mul_of_pos_left hna hC
      have hc : C*(ε/C)=ε := by field_simp
      rw [mul_add,hc] at hh
      exact hh.le

end OperatorDerivativeRewrite.Foundation.FourierPathHeatGradient
