import Foundation.StickyBoundaryMaximumPrinciple
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-! An actual differential boundary relation on C0(R). Its off-boundary
derivatives and one-sided boundary derivatives are hypotheses about functions,
not formal symbols. Closedness, density and surjectivity are separate. -/
noncomputable section
open Set Filter
open scoped NNReal Topology ZeroAtInfty
namespace OperatorDerivativeRewrite.Foundation.StickyGeneratorRelation
open StickyBoundaryMaximumPrinciple
set_option backward.isDefEq.respectTransparency false

theorem second_derivative_nonpositive {F : ℝ → ℝ} {x : ℝ}
    (hc : ContinuousAt F x) (hm : IsLocalMax F x) : deriv (deriv F) x ≤ 0 := by
  by_contra hn
  have hp : 0 < deriv (deriv F) x := lt_of_not_ge hn
  have hmin := isLocalMin_of_deriv_deriv_pos hp hm.deriv_eq_zero hc
  have he : F =ᶠ[𝓝 x] (fun _ => F x) := by
    filter_upwards [hm, hmin] with y hle hge
    exact le_antisymm hle hge
  have hz : deriv (deriv F) x = 0 := by
    calc
      _ = deriv (deriv (fun _ : ℝ => F x)) x := he.deriv.deriv_eq
      _ = 0 := by simp
  linarith

structure Admissible (κ : ℝ≥0) (F G : C₀(ℝ, ℝ)) : Prop where
  differentiable : ∀ x ≠ 0, DifferentiableAt ℝ F x
  twice_differentiable : ∀ x ≠ 0, DifferentiableAt ℝ (deriv F) x
  off_zero : ∀ x ≠ 0, G x = (1/2 : ℝ)*deriv (deriv F) x
  boundary : ∃ r l : ℝ, HasDerivWithinAt F r (Ici 0) 0 ∧
    HasDerivWithinAt F l (Iic 0) 0 ∧ r-l = 2*(κ : ℝ)*G 0

theorem maximum_principle {κ : ℝ≥0} (hκ : 0 < κ) {F G : C₀(ℝ, ℝ)}
    (h : Admissible κ F G) {x : ℝ} (hm : ∀ y, F y ≤ F x) : G x ≤ 0 := by
  by_cases hx : x = 0
  · subst x
    obtain ⟨r,l,hr,hl,hj⟩ := h.boundary
    have hright := right_derivative_nonpositive hr hm
    have hleft := left_derivative_nonnegative hl hm
    have hp : 0 < (κ : ℝ) := hκ
    nlinarith
  · rw [h.off_zero x hx]
    have hmax : IsLocalMax (F : ℝ → ℝ) x := Filter.Eventually.of_forall hm
    have hs := second_derivative_nonpositive
      (show ContinuousAt (F : ℝ → ℝ) x from F.continuous.continuousAt) hmax
    linarith

theorem Admissible.neg {κ : ℝ≥0} {F G : C₀(ℝ, ℝ)} (h : Admissible κ F G) :
    Admissible κ (-F) (-G) := by
  have he : deriv ((-F : C₀(ℝ, ℝ)) : ℝ → ℝ) = -deriv (F : ℝ → ℝ) := by
    funext x
    exact deriv.neg
  refine ⟨fun x hx => (h.differentiable x hx).neg, ?_, ?_, ?_⟩
  · intro x hx
    rw [he]
    exact (h.twice_differentiable x hx).neg
  · intro x hx
    change -G x = (1/2 : ℝ)*deriv (deriv ((-F : C₀(ℝ, ℝ)) : ℝ → ℝ)) x
    rw [he, deriv.neg, h.off_zero x hx]
    ring
  · obtain ⟨r,l,hr,hl,hj⟩ := h.boundary
    refine ⟨-r,-l,hr.neg,hl.neg,?_⟩
    change -r- -l = 2*(κ : ℝ)* -G 0
    nlinarith

theorem minimum_principle {κ : ℝ≥0} (hκ : 0 < κ) {F G : C₀(ℝ, ℝ)}
    (h : Admissible κ F G) {x : ℝ} (hm : ∀ y, F x ≤ F y) : 0 ≤ G x := by
  have hh := maximum_principle hκ h.neg (x := x) (fun y => neg_le_neg (hm y))
  change -G x ≤ 0 at hh
  linarith

theorem norm_attained (F : C₀(ℝ, ℝ)) : ∃ x : ℝ, ‖F x‖ = ‖F‖ := by
  by_cases hz : F = 0
  · subst F
    exact ⟨0,by simp⟩
  · have he : ∃ z, F z ≠ 0 := by
      by_contra hn
      apply hz
      ext z
      simpa using not_exists.mp hn z
    obtain ⟨z,hz⟩ := he
    have hp : 0 < ‖F z‖ := norm_pos_iff.mpr hz
    have ht : Tendsto (fun y => ‖F y‖) (cocompact ℝ) (𝓝 0) := by
      simpa only [norm_zero] using (zero_at_infty F).norm
    obtain ⟨x,hx⟩ := F.continuous.norm.exists_forall_ge' z
      ((ht.eventually (eventually_lt_nhds hp)).mono (fun _ h => h.le))
    refine ⟨x,le_antisymm (F.toBCF.norm_coe_le_norm x) ?_⟩
    exact (BoundedContinuousFunction.norm_le (norm_nonneg (F x))).mpr hx

theorem resolvent_norm_bound {κ : ℝ≥0} (hκ : 0 < κ) {F G : C₀(ℝ, ℝ)}
    (h : Admissible κ F G) {q : ℝ} (hq : 0 < q) :
    q*‖F‖ ≤ ‖q • F-G‖ := by
  obtain ⟨x,hx⟩ := norm_attained F
  have hb := (q • F-G).toBCF.norm_coe_le_norm x
  change ‖q*F x-G x‖ ≤ ‖q • F-G‖ at hb
  by_cases hs : 0 ≤ F x
  · have hm : ∀ y, F y ≤ F x := by
      intro y
      have hy := F.toBCF.norm_coe_le_norm y
      change ‖F y‖ ≤ ‖F‖ at hy
      rw [← hx] at hy
      simp only [Real.norm_eq_abs, abs_of_nonneg hs] at hy
      exact (le_abs_self (F y)).trans hy
    have hg := maximum_principle hκ h hm
    rw [← hx, Real.norm_eq_abs, abs_of_nonneg hs]
    have ha := le_abs_self (q*F x-G x)
    rw [← Real.norm_eq_abs] at ha
    linarith
  · have hs' := le_of_not_ge hs
    have hm : ∀ y, F x ≤ F y := by
      intro y
      have hy := F.toBCF.norm_coe_le_norm y
      change ‖F y‖ ≤ ‖F‖ at hy
      rw [← hx] at hy
      simp only [Real.norm_eq_abs, abs_of_nonpos hs'] at hy
      have ha := neg_abs_le (F y)
      linarith
    have hg := minimum_principle hκ h hm
    rw [← hx, Real.norm_eq_abs, abs_of_nonpos hs']
    have ha := neg_le_abs (q*F x-G x)
    rw [← Real.norm_eq_abs] at ha
    linarith

end OperatorDerivativeRewrite.Foundation.StickyGeneratorRelation
