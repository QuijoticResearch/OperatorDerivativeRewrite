import Foundation.RiemannQuarticZeroCounting
import Foundation.EntireDiskDecomposition
import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Order.Interval.Set.Infinite

/-! Actual finite-disk remainders for the quartic transform. Good radii
avoid boundary zeros. The normalized logarithm is constructed, but its
first derivative and the required uniform growth bound are not asserted. -/
noncomputable section
open Set Metric Filter Complex MeromorphicOn
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticDiskDecomposition
open RiemannQuarticFlow RiemannQuarticZeroCounting

theorem exists_zero_free_sphere (t R : ℝ) (hR : 0 ≤ R) :
    ∃ r : ℝ, R < r ∧ r < R+1 ∧ ∀ z ∈ sphere (0 : ℂ) r, flow t z ≠ 0 := by
  exact EntireDiskDecomposition.exists_zero_free_sphere
    (flow t) (flow_analytic t)
    (by simpa using RiemannQuarticReality.flow_ne_zero_on_imaginary_axis t 0) R hR

theorem boundary_divisor_eq_zero (t r : ℝ)
    (hne : ∀ z ∈ sphere (0 : ℂ) r, flow t z ≠ 0) :
    divisor (flow t) (sphere 0 r) = 0 := by
  exact EntireDiskDecomposition.boundary_divisor_eq_zero
    (flow t) (flow_analytic t) r hne

theorem exists_actual_disk_log_remainder (t R : ℝ) (hR : 0 ≤ R) :
    ∃ r : ℝ, R < r ∧ r < R+1 ∧
      divisor (flow t) (sphere 0 r) = 0 ∧
      ∃ h g : ℂ → ℂ, ECanonicalDecomp (flow t) h r ∧
        DifferentiableOn ℂ g (ball 0 r) ∧ g 0 = 0 ∧
        (∀ z ∈ ball (0 : ℂ) r, HasDerivAt g (deriv h z / h z) z) ∧
        ∀ z ∈ ball (0 : ℂ) r, Complex.exp (g z) = h z / h 0 := by
  exact EntireDiskDecomposition.exists_disk_log_remainder
    (flow t) (flow_analytic t)
    (by simpa using RiemannQuarticReality.flow_ne_zero_on_imaginary_axis t 0) R hR

end OperatorDerivativeRewrite.Foundation.RiemannQuarticDiskDecomposition
