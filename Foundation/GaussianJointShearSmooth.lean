import Foundation.GaussianJointHeatSmooth
import Foundation.GaussianShearShellSeparation

/-! Joint spacetime smoothness of the actual fixed periodic Gaussian NS shear. -/
noncomputable section
open Set
open scoped ContDiff
namespace OperatorDerivativeRewrite.Foundation.GaussianJointShearSmooth
open FiniteFourierSynthesis GaussianInfiniteShear GaussianPeriodicHeat GaussianJointHeatSmooth

def spacetimeDomain (nu : ℝ) : Set (ℝ × Space) := {p | 0 < 1+nu*p.1}

theorem spacetime_open (nu : ℝ) : IsOpen (spacetimeDomain nu) := by
  exact isOpen_lt continuous_const (continuous_const.add (continuous_const.mul continuous_fst))

theorem joint_profile (nu : ℝ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Space => profile nu p.1 (p.2 1)) (spacetimeDomain nu) := by
  have hmap : ContDiff ℝ ∞ (fun p : ℝ × Space => (1+nu*p.1,p.2 1)) := by fun_prop
  exact (joint_smooth 0).comp hmap.contDiffOn (fun p hp => hp)

theorem joint_scalar (nu : ℝ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Space => scalar nu p.1 p.2) (spacetimeDomain nu) := by
  have hr : ContDiff ℝ ∞ (fun p : ℝ × Space => amplitude nu p.1*Real.sin (p.2 2)) := by
    unfold amplitude
    fun_prop
  exact (contDiffOn_const.mul (joint_profile nu)).add hr.contDiffOn

theorem joint_velocity (nu : ℝ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Space => velocity nu p.1 p.2) (spacetimeDomain nu) := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · simpa [velocity] using joint_scalar nu
  · simpa [velocity] using (contDiffOn_const :
      ContDiffOn ℝ ∞ (fun _ : ℝ × Space => (0:ℝ)) (spacetimeDomain nu))
  · simpa [velocity] using (contDiffOn_const :
      ContDiffOn ℝ ∞ (fun _ : ℝ × Space => (0:ℝ)) (spacetimeDomain nu))

theorem joint_at_nonnegative (nu t : ℝ) (hnu : 0 ≤ nu) (ht : 0 ≤ t) (x : Space) :
    ContDiffAt ℝ ∞ (fun p : ℝ × Space => velocity nu p.1 p.2) (t,x) := by
  apply (joint_velocity nu).contDiffAt
  apply (spacetime_open nu).mem_nhds
  change 0 < 1+nu*t
  positivity

end OperatorDerivativeRewrite.Foundation.GaussianJointShearSmooth
