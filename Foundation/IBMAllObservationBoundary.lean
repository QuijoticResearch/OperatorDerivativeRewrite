import Foundation.GaussianAllObservationBracket
import Foundation.IBMObservedClockOccupation

/-! The actual random folded-clock level at any observation time has zero
time occupation on every finite horizon, including observations inside it. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMAllObservationBoundary
open InfiniteGaussian IBMRandomTerminalBoundary IBMClockOverlapEnergy IBMConstructedSources

theorem distance_positive_all_windows (H R : ℝ≥0) :
    ∀ᵐ Y ∂gaussianProduct, ∀ᵐ t ∂window H, 0 < distance R (t,Y) := by
  have hm : MeasurableSet {z : ℝ × SampleSpace | 0 < distance R z} :=
    measurableSet_lt measurable_const (distance_measurable R)
  apply (Measure.ae_ae_comm hm).mp
  have hnot : ∀ᵐ t ∂window H, t ≠ (R:ℝ) := by
    rw [ae_iff]
    have hz : (window H) {(R:ℝ)} = 0 := by
      unfold window
      rw [Measure.restrict_apply (measurableSet_singleton (R:ℝ))]
      exact measure_mono_null inter_subset_left (measure_singleton (R:ℝ))
    simpa using hz
  filter_upwards [ae_restrict_mem measurableSet_Ioc,hnot] with t ht hne
  have hnn : t.toNNReal ≠ R := by
    intro he
    apply hne
    have h := congrArg (fun x : ℝ≥0 => (x:ℝ)) he
    simpa only [Real.coe_toNNReal t ht.1.le] using h
  rcases lt_or_gt_of_ne hnn with hr | hr
  · filter_upwards [path_folded_noncollision_ae t.toNNReal R hr] with Y hY
    exact abs_pos.mpr (sub_ne_zero.mpr hY)
  · filter_upwards [path_folded_noncollision_ae R t.toNNReal hr] with Y hY
    exact abs_pos.mpr (sub_ne_zero.mpr hY.symm)

end OperatorDerivativeRewrite.Foundation.IBMAllObservationBoundary
