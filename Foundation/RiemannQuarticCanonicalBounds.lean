import Foundation.EvenEntireCanonicalApproximation
import Foundation.RiemannQuarticCanonicalDerivative
import Mathlib.Analysis.Complex.AbsMax

/-! Actual bounds for the finite-disk zero-free remainder, obtained from
boundary values and the normalization at zero rather than an uncontrolled
division of entire functions. -/
noncomputable section
open Set Metric Filter Complex MeromorphicOn
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticCanonicalBounds
open RiemannQuarticFlow RiemannQuarticReality RiemannQuarticZeroCounting
open RiemannQuarticCanonicalDerivative

theorem canonical_norm_at_origin (R : ℝ) (hR : 0 < R) (a : ℂ) (ha : a ≠ 0) :
    ‖canonicalFactor R a 0‖ = R/‖a‖ := by
  exact EvenEntireCanonicalApproximation.canonical_norm_at_origin
    R hR a ha

theorem canonical_product_boundary_norm (t R : ℝ) (z : ℂ) (hz : z ∈ sphere (0 : ℂ) R) :
    ‖∏ᶠ a : ℂ, canonicalFactor R a z ^ (divisor (flow t) (ball 0 R) a)‖ = 1 := by
  exact EvenEntireCanonicalApproximation.canonical_product_boundary_norm
    (flow t) (RiemannQuarticZeroCounting.flow_analytic t) R z hz

theorem canonical_product_origin_norm_ge_one (t R : ℝ) (hR : 0 < R) :
    1 ≤ ‖∏ᶠ a : ℂ, canonicalFactor R a 0 ^ (divisor (flow t) (ball 0 R) a)‖ := by
  exact EvenEntireCanonicalApproximation.canonical_product_origin_norm_ge_one
    (flow t) (RiemannQuarticZeroCounting.flow_analytic t)
    (by simpa using RiemannQuarticReality.flow_ne_zero_on_imaginary_axis t 0) R hR

theorem remainder_boundary_norm (t R : ℝ) (hR : 0 < R) (h : ℂ → ℂ)
    (D : ECanonicalDecomp (flow t) h R)
    (hne : ∀ z ∈ sphere (0 : ℂ) R, flow t z ≠ 0) :
    ∀ z ∈ sphere (0 : ℂ) R, ‖h z‖ = ‖flow t z‖ := by
  exact EvenEntireCanonicalApproximation.remainder_boundary_norm
    (flow t) (RiemannQuarticZeroCounting.flow_analytic t) R hR h D hne

theorem remainder_origin_norm_lower (t R : ℝ) (hR : 0 < R) (h : ℂ → ℂ)
    (D : ECanonicalDecomp (flow t) h R)
    (hboundary : divisor (flow t) (sphere 0 R) = 0) : ‖flow t 0‖ ≤ ‖h 0‖ := by
  exact EvenEntireCanonicalApproximation.remainder_origin_norm_lower
    (flow t) (RiemannQuarticZeroCounting.flow_analytic t)
    (by simpa using RiemannQuarticReality.flow_ne_zero_on_imaginary_axis t 0) R hR h D hboundary

theorem remainder_norm_bound (t : ℝ) (C : ℝ)
    (hgrowth : ∀ z : ℂ, ‖flow t z‖ ≤ C*Real.exp (‖z‖*Real.sqrt ‖z‖))
    (R : ℝ) (hR : 0 < R) (h : ℂ → ℂ) (D : ECanonicalDecomp (flow t) h R)
    (hne : ∀ z ∈ sphere (0 : ℂ) R, flow t z ≠ 0) :
    ∀ z ∈ closedBall (0 : ℂ) R, ‖h z‖ ≤ C*Real.exp (R*Real.sqrt R) := by
  exact EvenEntireCanonicalApproximation.remainder_norm_bound
    (flow t) (RiemannQuarticZeroCounting.flow_analytic t) C hgrowth R hR h D hne

theorem sphere_zero_free_of_boundary_divisor_zero (t R : ℝ)
    (hboundary : divisor (flow t) (sphere 0 R) = 0) :
    ∀ z ∈ sphere (0 : ℂ) R, flow t z ≠ 0 := by
  exact EvenEntireCanonicalApproximation.sphere_zero_free_of_boundary_divisor_zero
    (flow t) (RiemannQuarticZeroCounting.flow_analytic t)
    (by simpa using RiemannQuarticReality.flow_ne_zero_on_imaginary_axis t 0) R hboundary

theorem exists_normalized_remainder_real_part_bound (t : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ R : ℝ, 1 ≤ R → ∀ r : ℝ, 2*R < r → r < 2*R+1 →
      ∀ h g : ℂ → ℂ, ECanonicalDecomp (flow t) h r →
        divisor (flow t) (sphere 0 r) = 0 →
        (∀ z ∈ ball (0 : ℂ) r, Complex.exp (g z) = h z/h 0) →
        ∀ z ∈ ball (0 : ℂ) (2*R), (g z).re ≤ A+6*(R*Real.sqrt R) := by
  exact EvenEntireCanonicalApproximation.exists_normalized_remainder_real_part_bound
    (flow t) (RiemannQuarticZeroCounting.flow_analytic t)
    (by simpa using RiemannQuarticReality.flow_ne_zero_on_imaginary_axis t 0)
    (RiemannQuarticEntireGrowth.exists_subquadratic_growth t)

end OperatorDerivativeRewrite.Foundation.RiemannQuarticCanonicalBounds
