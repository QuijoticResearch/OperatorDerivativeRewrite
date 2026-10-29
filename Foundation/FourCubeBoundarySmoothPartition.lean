import Foundation.FourCubeBoundarySmoothAction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Global fixed-coupling smoothness of the actual three-boundary-axis Haar free energy. -/
noncomputable section
open MeasureTheory
open scoped Topology ContDiff
namespace OperatorDerivativeRewrite.Foundation.FourCubeBoundarySmoothPartition
open FourCubeHaarContinuousIntegral FourCubeBoundarySmoothAction FourCubeHaarParity
open FourCubeIntegratedCubic FourCubeIntegratedResponse FourCubePinnedHaar
open FourCubePinnedConcentration

def partition (β : ℝ) (a : Parameters) : ℝ :=
  haarIntegral (NormedSpace.exp ((-β) • action a))

theorem partition_integral (β : ℝ) (a : Parameters) :
    partition β a=∫ s,Real.exp (-β*cellAction (a 0) (a 1) (a 2) s) ∂interiorHaar := by
  rw [partition,haarIntegral_apply]
  apply integral_congr_ae
  filter_upwards with s
  rw [exp_apply]
  simp only [ContinuousMap.smul_apply,smul_eq_mul,action_apply]

theorem partition_eq_actual (β : ℝ) (a : Parameters) : partition β a=partition3 (a 0) (a 1) (a 2) β := by
  rw [partition_integral,partition3_integral]

theorem partition_contDiff (β : ℝ) : ContDiff ℝ ∞ (partition β) :=
  integrated_exponential_contDiff action action_contDiff β

theorem actual_partition_contDiff (β : ℝ) :
    ContDiff ℝ ∞ (fun a : Parameters => pinnedPartition β (boundaryData (a 0) (a 1) (a 2))) := by
  have he : (fun a : Parameters => pinnedPartition β (boundaryData (a 0) (a 1) (a 2)))=partition β := by
    funext a
    rw [partition_eq_actual,partition3_eq_pinned]
  rw [he]
  exact partition_contDiff β

theorem actual_normalized_contDiff (β : ℝ) :
    ContDiff ℝ ∞ (fun a : Parameters => FourCubeScaledBoundaryControl.normalizedPartition β
      (boundaryData (a 0) (a 1) (a 2))) :=
  (actual_partition_contDiff β).div_const (normalizer β)

theorem actual_normalized_positive (β : ℝ) (a : Parameters) :
    0 < FourCubeScaledBoundaryControl.normalizedPartition β (boundaryData (a 0) (a 1) (a 2)) :=
  div_pos (pinnedPartition_positive _ _) (normalizer_positive _)

def freeEnergy (β : ℝ) (a : Parameters) : ℝ :=
  FourCubeThermalMixedDifference.freeEnergy β (a 0) (a 1) (a 2)

theorem actual_freeEnergy_contDiff (β : ℝ) : ContDiff ℝ ∞ (freeEnergy β) :=
  ((actual_normalized_contDiff β).log (fun a => (actual_normalized_positive β a).ne')).neg

theorem actual_freeEnergy_contDiffAt (β : ℝ) (a : Parameters) :
    ContDiffAt ℝ ∞ (freeEnergy β) a := (actual_freeEnergy_contDiff β).contDiffAt

end OperatorDerivativeRewrite.Foundation.FourCubeBoundarySmoothPartition
