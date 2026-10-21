import Foundation.EvenEntireCanonicalDerivative
import Foundation.RiemannQuarticDiskDecomposition
import Foundation.RiemannQuarticGlobalSimpleZeros
import Mathlib.Analysis.Calculus.LogDeriv

/-! Actual opposite-zero multiplicities and canonical logarithmic
derivatives. No real-zero assumption or simple-zero assumption is used. -/
noncomputable section
open Set Metric Filter Complex MeromorphicOn
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticCanonicalDerivative
open RiemannQuarticFlow RiemannQuarticEvolution RiemannQuarticReality
open RiemannQuarticZeroCounting

theorem flow_order_neg (t : ℝ) (z : ℂ) :
    meromorphicOrderAt (flow t) (-z) = meromorphicOrderAt (flow t) z := by
  exact EvenEntireCanonicalDerivative.order_neg
    (flow t) (RiemannQuarticEvolution.flow_even t) z

theorem ball_divisor_neg (t R : ℝ) (z : ℂ) :
    divisor (flow t) (ball 0 R) (-z) = divisor (flow t) (ball 0 R) z := by
  exact EvenEntireCanonicalDerivative.ball_divisor_neg
    (flow t) (flow_analytic t) (RiemannQuarticEvolution.flow_even t) R z

theorem ball_divisor_zero_at_origin (t R : ℝ) :
    divisor (flow t) (ball 0 R) 0 = 0 := by
  exact EvenEntireCanonicalDerivative.ball_divisor_zero_at_origin
    (flow t) (flow_analytic t)
    (by simpa using flow_ne_zero_on_imaginary_axis t 0) R

theorem canonical_logDeriv_zero (R : ℝ) (hR : 0 < R) (a : ℂ) (ha : a ≠ 0) :
    logDeriv (canonicalFactor R a) 0 = 1/a - conj a/(R : ℂ)^2 := by
  exact EvenEntireCanonicalDerivative.canonical_logDeriv_zero
    R hR a ha

theorem canonical_logDeriv_sum_zero (t R : ℝ) :
    (∑ᶠ a : ℂ, (divisor (flow t) (ball 0 R) a : ℂ) *
      (1/a-conj a/(R : ℂ)^2)) = 0 := by
  exact EvenEntireCanonicalDerivative.canonical_logDeriv_sum_zero
    (flow t) (flow_analytic t) (RiemannQuarticEvolution.flow_even t) R

theorem canonical_remainder_eq_at_ne_zero (t R : ℝ) (hR : 0 < R)
    (h : ℂ → ℂ) (D : ECanonicalDecomp (flow t) h R)
    (hboundary : divisor (flow t) (sphere 0 R) = 0)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) R) (hne : flow t z ≠ 0) :
    h z = (∏ᶠ a : ℂ, canonicalFactor R a z ^ (divisor (flow t) (ball 0 R) a)) * flow t z := by
  exact EvenEntireCanonicalDerivative.canonical_remainder_eq_at_ne_zero
    (flow t) (flow_analytic t) R hR h D hboundary z hz hne

theorem canonical_remainder_deriv_zero (t R : ℝ) (hR : 0 < R)
    (h : ℂ → ℂ) (D : ECanonicalDecomp (flow t) h R)
    (hboundary : divisor (flow t) (sphere 0 R) = 0) : deriv h 0 = 0 := by
  exact EvenEntireCanonicalDerivative.canonical_remainder_deriv_zero
    (flow t) (flow_analytic t)
    (by simpa using flow_ne_zero_on_imaginary_axis t 0) (RiemannQuarticEvolution.flow_even t) R hR h D hboundary

theorem exists_actual_zero_derivative_log_remainder (t R : ℝ) (hR : 0 ≤ R) :
    ∃ r : ℝ, R < r ∧ r < R+1 ∧
      divisor (flow t) (sphere 0 r) = 0 ∧
      ∃ h g : ℂ → ℂ, ECanonicalDecomp (flow t) h r ∧
        DifferentiableOn ℂ g (ball 0 r) ∧ g 0 = 0 ∧ deriv g 0 = 0 ∧
        (∀ z ∈ ball (0 : ℂ) r, HasDerivAt g (deriv h z / h z) z) ∧
        ∀ z ∈ ball (0 : ℂ) r, Complex.exp (g z) = h z / h 0 := by
  exact EvenEntireCanonicalDerivative.exists_zero_derivative_log_remainder
    (flow t) (flow_analytic t)
    (by simpa using flow_ne_zero_on_imaginary_axis t 0) (RiemannQuarticEvolution.flow_even t) R hR

end OperatorDerivativeRewrite.Foundation.RiemannQuarticCanonicalDerivative
