import Foundation.FourierPathDirectionalOperator

/-! A genuine bounded unit resolvent for every directional path derivative. -/
noncomputable section
open scoped lp NNReal ENNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.FourierPathDirectionalResolvent
open L1SeriesSynthesis HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open FourierPathDirectionalCharacters FourierPathDirectionalOperator

def weight (w : ℝ) : ℂ := (1-eigenvalue w)⁻¹

theorem denominator_norm (w : ℝ) : 1 ≤ ‖1-eigenvalue w‖ := by
  simpa [eigenvalue, Complex.mul_re] using Complex.re_le_norm (1-eigenvalue w)

theorem denominator_ne_zero (w : ℝ) : 1-eigenvalue w ≠ 0 := by
  intro hw
  have hn := denominator_norm w
  rw [hw, norm_zero] at hn
  norm_num at hn

theorem weight_bound (w : ℝ) : ‖weight w‖ ≤ 1 := by
  rw [weight, norm_inv]
  exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one (denominator_norm w))).mpr (denominator_norm w)

theorem weight_relation (w : ℝ) : weight w-1=weight w*eigenvalue w := by
  unfold weight
  field_simp [denominator_ne_zero w]
  <;> ring

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def coefficientResolvent (h : Path) : Coeff →L[ℂ] Coeff :=
  lp.mapCLM 1 (term (fun i => weight (frequency levels ξ h i))) zero_le_one
    (term_norm_le _ (fun i => weight_bound _))

theorem coefficientResolvent_graph (h : Path) (a : Coeff) :
    (coefficientResolvent levels ξ h a, coefficientResolvent levels ξ h a-a) ∈
      coefficientGraph levels ξ h := by
  intro i
  change a i*weight (frequency levels ξ h i)-a i=
    (a i*weight (frequency levels ξ h i))*eigenvalue (frequency levels ξ h i)
  calc
    _ = a i*(weight (frequency levels ξ h i)-1) := by ring
    _ = _ := by rw [weight_relation]; ring

theorem coefficientResolvent_preserves_kernel (h : Path) (a : Coeff)
    (ha : a ∈ kernel levels ξ) : coefficientResolvent levels ξ h a ∈ kernel levels ξ := by
  have hqa : (kernel levels ξ).mkQ a=0 := (Submodule.Quotient.mk_eq_zero _).mpr ha
  have hg : ((kernel levels ξ).mkQ (coefficientResolvent levels ξ h a),
      (kernel levels ξ).mkQ (coefficientResolvent levels ξ h a-a)) ∈ graph levels ξ h :=
    ⟨_, coefficientResolvent_graph levels ξ h a, rfl⟩
  rw [map_sub, hqa, sub_zero] at hg
  have hb := graph_bound levels ξ h 1 (by norm_num) _ hg
  simp only [one_mul, one_smul, sub_self, norm_zero, norm_le_zero_iff] at hb
  exact (Submodule.Quotient.mk_eq_zero _).mp hb

theorem resolvent_kernel (h : Path) :
    kernel levels ξ ≤ (((kernel levels ξ).mkQL).comp (coefficientResolvent levels ξ h)).ker := by
  intro a ha
  change (kernel levels ξ).mkQ (coefficientResolvent levels ξ h a)=0
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (coefficientResolvent_preserves_kernel levels ξ h a ha)

def resolvent (h : Path) : TestSpace levels ξ →L[ℂ] TestSpace levels ξ :=
  (kernel levels ξ).liftQL (((kernel levels ξ).mkQL).comp (coefficientResolvent levels ξ h))
    (resolvent_kernel levels ξ h)

theorem resolvent_mk (h : Path) (a : Coeff) :
    resolvent levels ξ h ((kernel levels ξ).mkQ a)=
      (kernel levels ξ).mkQ (coefficientResolvent levels ξ h a) := rfl

theorem resolvent_graph (h : Path) (f : TestSpace levels ξ) :
    (resolvent levels ξ h f, resolvent levels ξ h f-f) ∈ graph levels ξ h := by
  obtain ⟨a,rfl⟩ := (kernel levels ξ).mkQ_surjective f
  rw [resolvent_mk, ← map_sub]
  exact ⟨_, coefficientResolvent_graph levels ξ h a, rfl⟩

theorem resolvent_bound (h : Path) (f : TestSpace levels ξ) : ‖resolvent levels ξ h f‖ ≤ ‖f‖ := by
  have hb := graph_bound levels ξ h 1 (by norm_num) _ (resolvent_graph levels ξ h f)
  simpa only [one_mul, one_smul, sub_sub_cancel] using hb

end OperatorDerivativeRewrite.Foundation.FourierPathDirectionalResolvent
