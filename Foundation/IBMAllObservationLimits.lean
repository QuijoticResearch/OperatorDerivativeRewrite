import Foundation.IBMAllObservationBoundary
import Foundation.IBMObservedClockCap

/-! Actual capped-clock and ORIGINAL intrinsic IBM terminal-square pairing
limits at EVERY observation time, including observations inside the horizon. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMAllObservationLimits
open InfiniteGaussian IBMTerminalBracketWeights IBMObservedClockOccupation IBMObservedClockBracket
open IBMClippedClockStrongLimit IBMAllObservationBoundary IBMObservedClockCap

theorem outer_sampledClass_tendsto_all (H R : ℝ≥0)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun N => sampledClass (outerBand (δ N)) (outerBand_measurable (δ N))
      (outerBand_bound (δ N)) H R N) atTop (𝓝 (0:GaussianL2)) :=
  sampledClass_tendsto_of_path _ (fun N => outerBand_measurable (δ N))
    (fun N => outerBand_bound (δ N)) H R (fun _ => 0) 0 (Lp.coeFn_zero ℝ 2 gaussianProduct)
    (fun Y => by simp only [norm_zero]; exact H.property)
    (outer_sampledPathSum_tendsto_of_noncollision H R (distance_positive_all_windows H R) δ hδ)

theorem interior_sampledClass_tendsto_all (H R : ℝ≥0) :
    Tendsto (sampledClass IBMTerminalBracketWeights.interior interior_measurable interior_bound H R)
      atTop (𝓝 (occupationL2 H R)) :=
  sampledClass_tendsto_of_path (fun _ => IBMTerminalBracketWeights.interior)
    (fun _ => interior_measurable) (fun _ => interior_bound) H R _ _
    (occupationL2_actual H R) (occupation_norm_bound H R)
    (interior_sampledPathSum_tendsto_of_noncollision H R (distance_positive_all_windows H R))

theorem weightedClass_tendsto_all (H R : ℝ≥0) (hH : 0 < H)
    (φ : ℕ → ℝ × ℝ → ℝ) (hm : ∀ N, Measurable (φ N)) (hb : ∀ N x, ‖φ N x‖ ≤ 1)
    (f : GaussianL2) (hf : Tendsto (fun N => sampledClass (φ N) (hm N) (hb N) H R N) atTop (𝓝 f)) :
    Tendsto (fun N => IBMObservedClockBracket.weightedClass (φ N) (hm N) (hb N) H R N) atTop (𝓝 f) := by
  have he := GaussianAllObservationBracket.varying_error_tendsto H hH (fun _ => R)
    (fun N _ => φ N) (fun N _ => hm N) (fun N _ => hb N)
  have h := he.add hf
  simpa only [zero_add,IBMObservedClockBracket.weightedClass] using h

theorem outer_weightedClass_tendsto_all (H R : ℝ≥0) (hH : 0 < H)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun N => IBMObservedClockBracket.weightedClass (outerBand (δ N)) (outerBand_measurable (δ N))
      (outerBand_bound (δ N)) H R N) atTop (𝓝 (0:GaussianL2)) :=
  weightedClass_tendsto_all H R hH _ _ _ 0 (outer_sampledClass_tendsto_all H R δ hδ)

theorem interior_weightedClass_tendsto_all (H R : ℝ≥0) (hH : 0 < H) :
    Tendsto (IBMObservedClockBracket.weightedClass IBMTerminalBracketWeights.interior interior_measurable interior_bound H R)
      atTop (𝓝 (occupationL2 H R)) :=
  weightedClass_tendsto_all H R hH (fun _ => IBMTerminalBracketWeights.interior)
    (fun _ => interior_measurable) (fun _ => interior_bound) _ (interior_sampledClass_tendsto_all H R)

theorem outer_weighted_mean_tendsto_all (H R : ℝ≥0) (hH : 0 < H)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun N => ∫ Y, weightedValue (outerBand (δ N)) H R N Y ∂gaussianProduct) atTop (𝓝 0) := by
  have h := ((innerSL ℝ (gaussianOne:GaussianL2)).continuous.tendsto (0:GaussianL2)).comp
    (outer_weightedClass_tendsto_all H R hH δ hδ)
  simp only [map_zero] at h
  exact h.congr' (Eventually.of_forall fun N => (weighted_mean _ (outerBand_measurable (δ N))
    (outerBand_bound (δ N)) H R N).symm)

theorem differenceClass_tendsto_all (H R : ℝ≥0) (hH : 0 < H) :
    Tendsto (differenceClass H R) atTop (𝓝 0) := by
  have hm := ((IBMOriginBoundaryEnergy.origin_weightedMean_tendsto
    IBMClippedClockTail.width IBMClippedClockTail.width_tendsto H hH).add
    (outer_weighted_mean_tendsto_all H R hH IBMClippedClockTail.width IBMClippedClockTail.width_tendsto)).add
      (IBMClippedClockTail.width_mean_tendsto H)
  simp only [zero_add] at hm
  have hn := squeeze_zero (fun N => norm_nonneg (differenceClass H R N))
    (fun N => differenceClass_norm_bound (IBMClippedClockTail.width N) H R N) hm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero] using hn

theorem cappedClass_tendsto_all (H R : ℝ≥0) (hH : 0 < H) :
    Tendsto (cappedClass H R) atTop (𝓝 (occupationClass H R)) := by
  have h := (differenceClass_tendsto_all H R hH).add
    (clockL1_tendsto _ _ (interior_weightedClass_tendsto_all H R hH))
  simp only [zero_add] at h
  exact h.congr' (Eventually.of_forall fun N => (cappedClass_reconstruction H R N).symm)

theorem actual_absolute_error_tendsto_all (H R : ℝ≥0) (hH : 0 < H) :
    Tendsto (fun N => ∫ Y, |cappedSum H R N Y-occupation H R Y| ∂gaussianProduct) atTop (𝓝 0) := by
  have hn := tendsto_iff_norm_sub_tendsto_zero.mp (cappedClass_tendsto_all H R hH)
  apply hn.congr'
  exact Eventually.of_forall fun N => by
    change ‖cappedClass H R N-occupationClass H R‖ =
      ∫ Y, |cappedSum H R N Y-occupation H R Y| ∂gaussianProduct
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (cappedClass H R N) (occupationClass H R),
      cappedClass_actual H R N,occupationClass_actual H R] with Y hs hc ho
    simp only [hs,Pi.sub_apply,hc,ho,Real.norm_eq_abs]

theorem capped_mean_tendsto_all (H R : ℝ≥0) (hH : 0 < H) :
    Tendsto (fun N => ∫ Y, cappedSum H R N Y ∂gaussianProduct) atTop
      (𝓝 (∫ Y, occupation H R Y ∂gaussianProduct)) := by
  have h := L1.continuous_integral.continuousAt.tendsto.comp (cappedClass_tendsto_all H R hH)
  change Tendsto (fun N => L1.integral (cappedClass H R N)) atTop
    (𝓝 (L1.integral (occupationClass H R))) at h
  simp only [L1.integral_eq_integral] at h
  have he : (∫ Y, occupationClass H R Y ∂gaussianProduct) =
      ∫ Y, occupation H R Y ∂gaussianProduct := integral_congr_ae (occupationClass_actual H R)
  rw [he] at h
  exact h.congr' (Eventually.of_forall fun N => integral_congr_ae (cappedClass_actual H R N))

theorem nativePairing_tendsto_all (H R : ℝ≥0) (hH : 0 < H) :
    Tendsto (nativePairing H R) atTop
      (𝓝 ((∫ Y, (IBMClippedClockCrossing.cap (GaussianTimeProcess.process R Y) (GaussianTimeProcess.process H Y))^2
        ∂gaussianProduct)-∫ Y, occupation H R Y ∂gaussianProduct)) := by
  have h := (tendsto_const_nhds (x:=∫ Y,
    (IBMClippedClockCrossing.cap (GaussianTimeProcess.process R Y) (GaussianTimeProcess.process H Y))^2
      ∂gaussianProduct)).sub (capped_mean_tendsto_all H R hH)
  exact h.congr' (Eventually.of_forall fun N => (nativePairing_identity H R N).symm)

end OperatorDerivativeRewrite.Foundation.IBMAllObservationLimits
