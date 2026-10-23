import Foundation.IBMPredictableTimeCutoff
import Foundation.IBMCompletedCoordinates
import Foundation.IBMCompletedNativeCalculus

/-! Actual time stopping on the completed fixed-family stochastic integral,
identified with literal stopped coordinates and observed projections. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology DirectSum
namespace OperatorDerivativeRewrite.Foundation.IBMCompletedTimeCutoff
open IBMTimeAveragedObservable IBMPredictableLpDictionary IBMMultichannelCompletion
open IBMIntrinsicRightGerm IBMObservedTerminalMartingale IBMCompletedCoordinates
open IBMFixedStochasticFamily
set_option backward.isDefEq.respectTransparency false
attribute [local instance] componentAdd componentGroup componentModule componentZeroDec
local instance : DecidableEq basisSet := Classical.decEq _
local instance : MeasurableSpace IBMPredictableRectangles.Space :=
  IBMNaturalFiltrationObstruction.naturalFiltration.predictable

def stop (t : ℝ≥0) : Completed fixedFamily →L[ℝ] Completed fixedFamily :=
  (completedIntegral fixedFamily).toContinuousLinearMap.adjoint.comp
    ((rightPast t).starProjection.comp (completedIntegral fixedFamily).toContinuousLinearMap)

theorem stop_integral (t : ℝ≥0) (z : Completed fixedFamily) :
    completedIntegral fixedFamily (stop t z) = channelClass (completedIntegral fixedFamily z) t := by
  let f : IntrinsicSpace := ⟨channelClass (completedIntegral fixedFamily z) t,
    IBMPredictableIntegralObservable.rightPast_le_intrinsic t (Submodule.starProjection_apply_mem _ _)⟩
  have h0 : channelClass (f : JointL2) 0 = 0 := by
    change (rightPast 0).starProjection (channelClass (completedIntegral fixedFamily z) t) = 0
    rw [project_channel _ (zero_le : (0 : ℝ≥0) ≤ t)]
    exact output_initial_zero z
  have hr := IBMCompletedNativeCalculus.fixed_weak_reconstruction f
  rw [h0, sub_zero] at hr
  exact hr

theorem stop_norm (t : ℝ≥0) (z : Completed fixedFamily) : ‖stop t z‖ ≤ ‖z‖ := by
  rw [← (completedIntegral fixedFamily).norm_map, stop_integral,
    ← (completedIntegral fixedFamily).norm_map z]
  exact channel_norm_bound _ t

theorem stop_comp (s t : ℝ≥0) (z : Completed fixedFamily) :
    stop s (stop t z) = stop (min s t) z := by
  apply (completedIntegral fixedFamily).injective
  simp only [stop_integral]
  exact IBMPredictableTimeCutoff.project_channel_min _ s t

theorem stop_zero (z : Completed fixedFamily) : stop 0 z = 0 := by
  apply (completedIntegral fixedFamily).injective
  rw [stop_integral, map_zero]
  exact output_initial_zero z

theorem stop_right_continuous (z : Completed fixedFamily) (t : ℝ≥0) :
    ContinuousWithinAt (fun s => stop s z) (Ici t) t := by
  apply (completedIntegral fixedFamily).isometry.tendsto_nhds_iff.mpr
  have hc := channel_right_continuous (completedIntegral fixedFamily z) t
  change Tendsto (fun s => channelClass (completedIntegral fixedFamily z) s)
    (𝓝[Ici t] t) (𝓝 (channelClass (completedIntegral fixedFamily z) t)) at hc
  simpa only [Function.comp_def, stop_integral] using hc

theorem stop_horizon_limit (z : Completed fixedFamily) :
    Tendsto (fun n : ℕ => stop n z) atTop (𝓝 z) := by
  apply (completedIntegral fixedFamily).isometry.tendsto_nhds_iff.mpr
  have hc := IBMObservableHorizonLimit.right_projection_tendsto (output z)
  change Tendsto (fun n : ℕ => channelClass (completedIntegral fixedFamily z) n)
    atTop (𝓝 (completedIntegral fixedFamily z)) at hc
  simpa only [Function.comp_def, stop_integral] using hc

def stoppedCoordinates (t : ℝ≥0) (z : Completed fixedFamily) (i : basisSet) :
    PredictableL2 (fixedFamily i) := IBMPredictableTimeCutoff.cutoff (fixedFamily i) t (coordinates z i)

theorem stopped_actual_sum (t : ℝ≥0) (z : Completed fixedFamily) :
    HasSum (fun i => IBMFullPredictableIntegral.integral (fixedFamily i) (stoppedCoordinates t z i))
      (completedIntegral fixedFamily (stop t z)) := by
  change Tendsto (fun s : Finset basisSet => ∑ i ∈ s,
    IBMFullPredictableIntegral.integral (fixedFamily i) (stoppedCoordinates t z i))
    atTop (𝓝 (completedIntegral fixedFamily (stop t z)))
  have hs := (rightPast t).starProjection.continuous.continuousAt.tendsto.comp (coordinates_actual_sum z)
  change Tendsto (fun s : Finset basisSet => (rightPast t).starProjection
    (∑ i ∈ s, IBMFullPredictableIntegral.integral (fixedFamily i) (coordinates z i)))
    atTop (𝓝 ((rightPast t).starProjection (completedIntegral fixedFamily z))) at hs
  simpa only [map_sum, stoppedCoordinates, IBMPredictableTimeCutoff.integral_cutoff, stop_integral, channelClass] using hs

theorem stopped_energy_tails (t : ℝ≥0) (z : Completed fixedFamily) :
    ∀ ε > (0 : ℝ), ∃ s : Finset basisSet, ∀ u, Disjoint u s →
      finiteEnergy fixedFamily u (stoppedCoordinates t z) < ε^2 := by
  intro ε hε
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp (stopped_actual_sum t z).summable ε hε
  refine ⟨s, fun u hu => ?_⟩
  rw [finiteEnergy_actual]
  have hn := hs u hu
  nlinarith [norm_nonneg (∑ i ∈ u, IBMFullPredictableIntegral.integral (fixedFamily i) (stoppedCoordinates t z i))]

theorem stopped_completed_sum (t : ℝ≥0) (z : Completed fixedFamily) :
    HasSum (fun i => IBMMultichannelCompletion.embed fixedFamily
      (DirectSum.lof ℝ basisSet _ i (stoppedCoordinates t z i))) (stop t z) := by
  obtain ⟨w, hw, hi⟩ := series_realization fixedFamily (stoppedCoordinates t z) (stopped_energy_tails t z)
  have he : w = stop t z := (completedIntegral fixedFamily).injective (hi.unique (stopped_actual_sum t z))
  exact he ▸ hw

theorem stopped_single (t : ℝ≥0) (i : basisSet) (H : PredictableL2 (fixedFamily i)) :
    stop t (IBMMultichannelCompletion.embed fixedFamily (DirectSum.lof ℝ basisSet _ i H)) =
      IBMMultichannelCompletion.embed fixedFamily
        (DirectSum.lof ℝ basisSet _ i (IBMPredictableTimeCutoff.cutoff (fixedFamily i) t H)) := by
  apply (completedIntegral fixedFamily).injective
  rw [stop_integral, completedIntegral_embed, rawIntegral_single,
    completedIntegral_embed, rawIntegral_single, IBMPredictableTimeCutoff.integral_cutoff]
  rfl

theorem intrinsic_causal_reconstruction (f : IntrinsicSpace) (t : ℝ≥0) :
    HasSum (fun i => IBMFullPredictableIntegral.integral (fixedFamily i)
      (stoppedCoordinates t ((completedIntegral fixedFamily).toContinuousLinearMap.adjoint (f : JointL2)) i))
      (channelClass (f : JointL2) t-channelClass (f : JointL2) 0) := by
  have hs := stopped_actual_sum t ((completedIntegral fixedFamily).toContinuousLinearMap.adjoint (f : JointL2))
  rw [stop_integral, IBMCompletedNativeCalculus.fixed_weak_reconstruction] at hs
  change HasSum _ ((rightPast t).starProjection
    ((f : JointL2)-channelClass (f : JointL2) 0)) at hs
  rw [map_sub] at hs
  have h0 : (rightPast t).starProjection (channelClass (f : JointL2) 0) = channelClass (f : JointL2) 0 :=
    Submodule.starProjection_eq_self_iff.mpr
      (IBMRightGermFiltration.rightPast_mono (zero_le : (0 : ℝ≥0) ≤ t)
        (Submodule.starProjection_apply_mem _ _))
  rw [h0] at hs
  exact hs



theorem point_causal_reconstruction (T : ℝ≥0) :
    HasSum (fun i => IBMFullPredictableIntegral.integral (fixedFamily i)
      (stoppedCoordinates T ((completedIntegral fixedFamily).toContinuousLinearMap.adjoint
        (intrinsicCurve T : JointL2)) i)) (intrinsicCurve T : JointL2) := by
  have hs := intrinsic_causal_reconstruction (intrinsicCurve T) T
  have hT : channelClass (intrinsicCurve T : JointL2) T = (intrinsicCurve T : JointL2) :=
    terminal_class (intrinsicCurve T : JointL2) (IBMDeterministicRangeObstruction.observed_mem_past T) le_rfl
  have h0 : channelClass (intrinsicCurve T : JointL2) 0 = 0 :=
    IBMObservedInitialGerm.initial_channel_zero T
  rw [hT, h0, sub_zero] at hs
  exact hs

theorem finite_cutoff_actual {ι : Type*} [DecidableEq ι] (F : ι → JointL2)
    (s : Finset ι) (H : ∀ i, PredictableL2 (F i)) (t : ℝ≥0) :
    (∑ i ∈ s, IBMFullPredictableIntegral.integral (F i) (IBMPredictableTimeCutoff.cutoff (F i) t (H i))) =
      (rightPast t).starProjection (∑ i ∈ s, IBMFullPredictableIntegral.integral (F i) (H i)) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => IBMPredictableTimeCutoff.integral_cutoff (F i) t (H i)

theorem finite_joint_energy_cutoff {ι : Type*} [DecidableEq ι] (F : ι → JointL2)
    (s : Finset ι) (H : ∀ i, PredictableL2 (F i)) (t : ℝ≥0) :
    finiteEnergy F s (fun i => IBMPredictableTimeCutoff.cutoff (F i) t (H i)) ≤ finiteEnergy F s H := by
  rw [finiteEnergy_actual, finiteEnergy_actual, finite_cutoff_actual]
  exact pow_le_pow_left₀ (norm_nonneg _) ((rightPast t).norm_starProjection_apply_le _) 2

end OperatorDerivativeRewrite.Foundation.IBMCompletedTimeCutoff
