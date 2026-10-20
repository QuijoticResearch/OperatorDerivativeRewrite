import Foundation.RiemannQuarticZeroCounting
import Foundation.EvenDiskLogLimit
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
  let Z : Set ℂ := closedBall 0 (R+1) ∩ (flow t) ⁻¹' {0}
  have hZ : Z.Finite := zeros_in_closedBall_finite t (R+1)
  obtain ⟨r,hr,havoid⟩ := (Ioo_infinite (show R < R+1 by linarith)).exists_notMem_finite
    (hZ.image (fun z : ℂ => ‖z‖))
  refine ⟨r,hr.1,hr.2,?_⟩
  intro z hz hzero
  have hn : ‖z‖ = r := mem_sphere_zero_iff_norm.mp hz
  apply havoid
  exact ⟨z,⟨mem_closedBall_zero_iff.mpr (by linarith [hr.2]),hzero⟩,hn⟩

theorem boundary_divisor_eq_zero (t r : ℝ)
    (hne : ∀ z ∈ sphere (0 : ℂ) r, flow t z ≠ 0) :
    divisor (flow t) (sphere 0 r) = 0 := by
  ext z
  by_cases hz : z ∈ sphere (0 : ℂ) r
  · have ha := flow_analytic t
    rw [((ha.mono (subset_univ (sphere (0 : ℂ) r))).meromorphicOn).divisor_apply hz,
      (ha z (mem_univ _)).meromorphicOrderAt_eq,
      (ha z (mem_univ _)).analyticOrderAt_eq_zero.mpr (hne z hz)]
    simp
  · change divisor (flow t) (sphere 0 r) z = 0
    exact (divisor (flow t) (sphere 0 r)).apply_eq_zero_of_notMem hz

theorem exists_actual_disk_log_remainder (t R : ℝ) (hR : 0 ≤ R) :
    ∃ r : ℝ, R < r ∧ r < R+1 ∧
      divisor (flow t) (sphere 0 r) = 0 ∧
      ∃ h g : ℂ → ℂ, ECanonicalDecomp (flow t) h r ∧
        DifferentiableOn ℂ g (ball 0 r) ∧ g 0 = 0 ∧
        (∀ z ∈ ball (0 : ℂ) r, HasDerivAt g (deriv h z / h z) z) ∧
        ∀ z ∈ ball (0 : ℂ) r, Complex.exp (g z) = h z / h 0 := by
  obtain ⟨r,hr,hr1,hne⟩ := exists_zero_free_sphere t R hR
  have hrp : 0 < r := lt_of_le_of_lt hR hr
  obtain ⟨h,D⟩ := ((flow_analytic t).mono (subset_univ (closedBall (0 : ℂ) r))).meromorphicOn
    |>.exists_ecanonicalDecomp (fun z => flow_zero_order_finite t z)
  have hh : DifferentiableOn ℂ h (ball 0 r) := fun z hz =>
    (D.analyticOnNhd z (ball_subset_closedBall hz)).differentiableAt.differentiableWithinAt
  obtain ⟨g,hg,h0,hd,he⟩ := EvenDiskLogRemainder.exists_normalized_log_on_ball h r hrp hh
    (fun z hz => D.ne_zero z (ball_subset_closedBall hz))
  exact ⟨r,hr,hr1,boundary_divisor_eq_zero t r hne,h,g,D,hg,h0,hd,he⟩

end OperatorDerivativeRewrite.Foundation.RiemannQuarticDiskDecomposition
