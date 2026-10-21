import Foundation.EntireSubquadraticZeroCounting
import Foundation.EvenDiskLogLimit
import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Order.Interval.Set.Infinite

/-! Finite canonical disk decompositions for entire functions nonzero at the origin.
This extracts the established quartic construction without assuming real zeros. -/
noncomputable section
open Set Metric Filter Complex MeromorphicOn
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.EntireDiskDecomposition
variable (f : ℂ → ℂ) (ha : AnalyticOnNhd ℂ f univ) (h0 : f 0 ≠ 0)
include ha h0

theorem exists_zero_free_sphere (R : ℝ) (hR : 0 ≤ R) :
    ∃ r : ℝ, R < r ∧ r < R+1 ∧ ∀ z ∈ sphere (0 : ℂ) r, f z ≠ 0 := by
  let Z : Set ℂ := closedBall 0 (R+1) ∩ f ⁻¹' {0}
  have hZ : Z.Finite := EntireSubquadraticZeroCounting.zeros_in_closedBall_finite f ha h0 (R+1)
  obtain ⟨r,hr,havoid⟩ := (Ioo_infinite (show R < R+1 by linarith)).exists_notMem_finite
    (hZ.image (fun z : ℂ => ‖z‖))
  refine ⟨r,hr.1,hr.2,?_⟩
  intro z hz hzero
  have hn : ‖z‖ = r := mem_sphere_zero_iff_norm.mp hz
  apply havoid
  exact ⟨z,⟨mem_closedBall_zero_iff.mpr (by linarith [hr.2]),hzero⟩,hn⟩

omit h0 in
theorem boundary_divisor_eq_zero (r : ℝ)
    (hne : ∀ z ∈ sphere (0 : ℂ) r, f z ≠ 0) :
    divisor f (sphere 0 r) = 0 := by
  ext z
  by_cases hz : z ∈ sphere (0 : ℂ) r
  · have ha := ha
    rw [((ha.mono (subset_univ (sphere (0 : ℂ) r))).meromorphicOn).divisor_apply hz,
      (ha z (mem_univ _)).meromorphicOrderAt_eq,
      (ha z (mem_univ _)).analyticOrderAt_eq_zero.mpr (hne z hz)]
    simp
  · change divisor f (sphere 0 r) z = 0
    exact (divisor f (sphere 0 r)).apply_eq_zero_of_notMem hz

theorem exists_disk_log_remainder (R : ℝ) (hR : 0 ≤ R) :
    ∃ r : ℝ, R < r ∧ r < R+1 ∧
      divisor f (sphere 0 r) = 0 ∧
      ∃ h g : ℂ → ℂ, ECanonicalDecomp f h r ∧
        DifferentiableOn ℂ g (ball 0 r) ∧ g 0 = 0 ∧
        (∀ z ∈ ball (0 : ℂ) r, HasDerivAt g (deriv h z / h z) z) ∧
        ∀ z ∈ ball (0 : ℂ) r, Complex.exp (g z) = h z / h 0 := by
  obtain ⟨r,hr,hr1,hne⟩ := exists_zero_free_sphere f ha h0 R hR
  have hrp : 0 < r := lt_of_le_of_lt hR hr
  obtain ⟨h,D⟩ := ((ha).mono (subset_univ (closedBall (0 : ℂ) r))).meromorphicOn
    |>.exists_ecanonicalDecomp (fun z => EntireSubquadraticZeroCounting.zero_order_finite f ha h0 z)
  have hh : DifferentiableOn ℂ h (ball 0 r) := fun z hz =>
    (D.analyticOnNhd z (ball_subset_closedBall hz)).differentiableAt.differentiableWithinAt
  obtain ⟨g,hg,h0,hd,he⟩ := EvenDiskLogRemainder.exists_normalized_log_on_ball h r hrp hh
    (fun z hz => D.ne_zero z (ball_subset_closedBall hz))
  exact ⟨r,hr,hr1,boundary_divisor_eq_zero f ha r hne,h,g,D,hg,h0,hd,he⟩

end OperatorDerivativeRewrite.Foundation.EntireDiskDecomposition
