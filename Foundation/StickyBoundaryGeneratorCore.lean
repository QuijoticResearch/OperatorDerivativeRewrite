import Foundation.StickyC2MartingaleProblem
import Mathlib.Analysis.Calculus.Deriv.Abs

/-! The boundary-test generator matches actual second derivatives away from
zero, and its boundary value satisfies the verified derivative-jump condition.
This is a martingale core calculation, not closed-semigroup identification. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StickyBoundaryGeneratorCore
open InfiniteGaussian BrownianMassRandomTimeChange StickyC2MartingaleProblem
set_option backward.isDefEq.respectTransparency false
variable (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)

def candidateGenerator (x : ℝ) : ℝ := (1/2 : ℝ)*deriv (deriv f) x

include hf in
theorem generator_continuous : Continuous (candidateGenerator f) :=
  continuous_const.mul (GaussianC2Ito.second_continuous f hf)

include hf in
theorem derivative_pos (κ : ℝ≥0) (x : ℝ) (hx : 0 < x) :
    deriv (boundaryTest f κ) x = deriv f x+coefficient f κ := by
  have h := (hf.differentiable (by norm_num) x).hasDerivAt.add
    ((hasDerivAt_abs_pos hx).const_mul (coefficient f κ))
  have he : boundaryTest f κ = f+(fun y => coefficient f κ*|y|) := by funext y; rfl
  rw [he]
  simpa only [mul_one] using h.deriv

include hf in
theorem derivative_neg (κ : ℝ≥0) (x : ℝ) (hx : x < 0) :
    deriv (boundaryTest f κ) x = deriv f x-coefficient f κ := by
  have h := (hf.differentiable (by norm_num) x).hasDerivAt.add
    ((hasDerivAt_abs_neg hx).const_mul (coefficient f κ))
  have he : boundaryTest f κ = f+(fun y => coefficient f κ*|y|) := by funext y; rfl
  rw [he]
  simpa only [mul_neg_one, sub_eq_add_neg] using h.deriv

include hf in
theorem second_derivative_pos (κ : ℝ≥0) (x : ℝ) (hx : 0 < x) :
    deriv (deriv (boundaryTest f κ)) x = deriv (deriv f) x := by
  have he : deriv (boundaryTest f κ) =ᶠ[𝓝 x] (fun y => deriv f y+coefficient f κ) :=
    (eventually_gt_nhds hx).mono (fun y hy => derivative_pos f hf κ y hy)
  rw [he.deriv_eq, deriv_add_const]

include hf in
theorem second_derivative_neg (κ : ℝ≥0) (x : ℝ) (hx : x < 0) :
    deriv (deriv (boundaryTest f κ)) x = deriv (deriv f) x := by
  have he : deriv (boundaryTest f κ) =ᶠ[𝓝 x] (fun y => deriv f y-coefficient f κ) :=
    (eventually_lt_nhds hx).mono (fun y hy => derivative_neg f hf κ y hy)
  rw [he.deriv_eq, deriv_sub_const]

include hf in
theorem generator_off_zero (κ : ℝ≥0) (x : ℝ) (hx : x ≠ 0) :
    candidateGenerator f x = (1/2 : ℝ)*deriv (deriv (boundaryTest f κ)) x := by
  rcases lt_or_gt_of_ne hx with hn | hp
  · rw [second_derivative_neg f hf κ x hn]
    rfl
  · rw [second_derivative_pos f hf κ x hp]
    rfl

theorem generator_boundary_jump (κ : ℝ≥0) :
    (deriv f 0+coefficient f κ)-(deriv f 0-coefficient f κ) =
      2*(κ : ℝ)*candidateGenerator f 0 := boundary_jump f κ

include hf in
theorem generator_martingale (K0 K1 : ℝ≥0)
    (h0 : ∀ x, ‖deriv f x‖₊ ≤ K0) (h1 : ∀ x, ‖deriv (deriv f) x‖₊ ≤ K1) (κ : ℝ≥0) :
    Martingale (fun t ω => boundaryTest f κ (changedPath κ ω t)-boundaryTest f κ 0-
      ∫ s in 0..(t : ℝ), candidateGenerator f (changedPath κ ω s.toNNReal))
      (augmentedPhysicalPast κ) gaussianProduct := by
  have he : (fun t ω => boundaryTest f κ (changedPath κ ω t)-boundaryTest f κ 0-
      ∫ s in 0..(t : ℝ), candidateGenerator f (changedPath κ ω s.toNNReal)) =
      boundaryProcess f κ := by
    funext t ω
    unfold boundaryProcess physicalDrift candidateGenerator
    rw [intervalIntegral.integral_const_mul]
  rw [he]
  exact boundaryProcess_martingale f hf K0 K1 h0 h1 κ

end OperatorDerivativeRewrite.Foundation.StickyBoundaryGeneratorCore
