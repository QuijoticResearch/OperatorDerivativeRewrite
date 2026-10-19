import Foundation.RiemannQuarticGaussianPrefactor
import Foundation.RiemannQuarticPairedSaddle
import Foundation.RiemannQuarticPhaseRemainder
/-! Comparison with a common real-center Gaussian-damped cosine model.
All quantitative errors are relative to nonzero individual channels,
never to a possibly cancelling sum. -/
noncomputable section
open Set Metric Complex
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticCommonProfile
open RiemannQuarticGaussianPrefactor RiemannQuarticPairedSaddle RiemannQuarticPhaseRemainder
open RiemannQuarticSaddleBranch RiemannQuarticSaddleTimes RiemannQuarticFrequencyBranch
open RiemannQuarticSaddleGeometry

def centerContribution (t u : ℝ) (z : ℂ) : ℂ :=
  quadraticSaddleWeight t u z*gaussianFactor t (u : ℂ)

theorem centerContribution_ne_zero (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : phaseSlope t u=0) (z : ℂ) : centerContribution t u z ≠ 0 := by
  apply mul_ne_zero (quadraticSaddleWeight_ne_zero t u ht hu hs z)
  rw [show gaussianFactor t (u : ℂ)=∫ s : ℝ, Complex.exp ((deriv (complexSlope t) (u : ℂ)/2)*(s : ℂ)^2) from
    (quadratic_gaussian_integral t u ht hu hs _ (mem_closedBall_self (by norm_num))).symm]
  exact quadratic_gaussian_integral_ne_zero t u ht hu hs _ (mem_closedBall_self (by norm_num))

theorem product_relative_error (a b : ℂ) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (ha : ‖a-1‖ ≤ α) (hb : ‖b-1‖ ≤ β) :
    ‖a*b-1‖ ≤ α*(1+β)+β := by
  have hbn : ‖b‖ ≤ 1+β := by
    have h := norm_add_le (b-1) (1 : ℂ)
    simp only [sub_add_cancel,norm_one] at h
    linarith
  calc
    _ = ‖(a-1)*b+(b-1)‖ := by congr 1; ring
    _ ≤ ‖(a-1)*b‖+‖b-1‖ := norm_add_le _ _
    _ = ‖a-1‖*‖b‖+‖b-1‖ := by rw [norm_mul]
    _ ≤ α*(1+β)+β := add_le_add (mul_le_mul ha hbn (norm_nonneg _) hα) hb

theorem actual_relative_center (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z : ℂ) (hz : ‖z‖ < (t*u^3+1)/51200)
    (hsmall : (25600/(t*u^3+1)^2)*‖z‖^3 ≤ 1) :
    ‖approxContribution t u ht hu hs z/centerContribution t u z-1‖ ≤
      ((51200/(t*u^3+1)^2)*‖z‖^3)*(1+51200*‖z‖/(t*u^3+1))+
        51200*‖z‖/(t*u^3+1) := by
  have hW := saddleWeight_relative_quadratic_error t u ht hu hs z hz hsmall
  have hG := branch_relative_center t u ht hu hs z hz.le
  have h := product_relative_error _ _ _ _ (by positivity) (by positivity) hW hG
  convert h using 1 <;> simp only [approxContribution,centerContribution,gaussianFactor,mul_div_mul_comm]

theorem center_pair_eq_cosine (t u : ℝ) (z : ℂ) :
    (centerContribution t u z+centerContribution t u (-z))/2=
      saddleWeight t 0 (u : ℂ)*gaussianFactor t (u : ℂ)*
        Complex.exp (z^2/(2*deriv (complexSlope t) (u : ℂ)))*Complex.cos ((u : ℂ)*z) := by
  simp only [centerContribution,quadraticSaddleWeight,neg_sq]
  rw [Complex.cos]
  simp only [Complex.exp_add]
  have h1 : Complex.I*(u : ℂ)*z=((u : ℂ)*z)*Complex.I := by ring
  have h2 : Complex.I*(u : ℂ)*(-z)=-((u : ℂ)*z)*Complex.I := by ring
  rw [h1,h2]
  ring

end OperatorDerivativeRewrite.Foundation.RiemannQuarticCommonProfile
