import Foundation.IBMClippedClockTail

/-! Genuine capped-clock quadratic-variation comparison. The limiting mean
is linked to the ORIGINAL IBM observable terminal-square pairing. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClippedClockLimit
open InfiniteGaussian GaussianTimeProcess GaussianBrownianQuadraticVariation
open IBMClippedClockCrossing IBMTerminalRiemannOccupation IBMTerminalBracketWeights
open IBMRandomBoundaryEnergy IBMOriginBoundaryEnergy

def cappedSum (T : ℝ≥0) (N : ℕ) (Y : SampleSpace) : ℝ :=
  ∑ i : Fin (N+1), (cap (process T Y) (process (uniformTime T N i.succ) Y)-
    cap (process T Y) (process (uniformTime T N i.castSucc) Y))^2

private theorem time_grid (T : ℝ≥0) (N : ℕ) (i : Fin (N+2)) :
    uniformTime T N i = IBMUniformClockGridEnergy.grid (T/(N+1)) i.val := by
  unfold uniformTime IBMUniformClockGridEnergy.grid
  push_cast
  ring

theorem cappedSum_eq_original (T : ℝ≥0) (N : ℕ) (Y : SampleSpace) :
    cappedSum T N Y = IBMRawGridObservableTests.clippedSquares (T/(N+1)) (N+1) T Y := by
  unfold cappedSum cap IBMRawGridObservableTests.clippedSquares IBMRawGridObservableTests.overlap
  simp only [time_grid,Fin.val_succ,Fin.val_castSucc]
  exact Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    (min |process (IBMUniformClockGridEnergy.grid (T/(N+1)) (i+1)) Y| |process T Y|-
      min |process (IBMUniformClockGridEnergy.grid (T/(N+1)) i) Y| |process T Y|)^2) (N+1)

theorem cappedSum_integrable (T : ℝ≥0) (N : ℕ) : Integrable (cappedSum T N) gaussianProduct := by
  have he : cappedSum T N = IBMRawGridObservableTests.clippedSquares (T/(N+1)) (N+1) T :=
    funext (cappedSum_eq_original T N)
  rw [he]
  exact IBMRawGridObservableTests.clippedSquares_integrable _ _ _

theorem difference_bound (δ : ℝ) (T : ℝ≥0) (N : ℕ) (Y : SampleSpace) :
    |cappedSum T N Y-weightedValue IBMTerminalBracketWeights.interior T N Y| ≤
      weightedValue (originBand δ) T N Y+weightedValue (outerBand δ) T N Y+
        IBMClippedClockTail.value δ T N Y := by
  have he : cappedSum T N Y-weightedValue IBMTerminalBracketWeights.interior T N Y =
      ∑ i : Fin (N+1), IBMClippedClockCrossing.error (process T Y)
        (process (uniformTime T N i.castSucc) Y) (process (uniformTime T N i.succ) Y) := by
    unfold cappedSum weightedValue
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    unfold IBMClippedClockCrossing.error
    ring
  rw [he]
  calc
    _ ≤ ∑ i : Fin (N+1), |IBMClippedClockCrossing.error (process T Y)
        (process (uniformTime T N i.castSucc) Y) (process (uniformTime T N i.succ) Y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (N+1), (process (uniformTime T N i.succ) Y-process (uniformTime T N i.castSucc) Y)^2*
        (originBand δ (process (uniformTime T N i.castSucc) Y,process T Y)+
          outerBand δ (process (uniformTime T N i.castSucc) Y,process T Y)+
            (if δ < |process (uniformTime T N i.succ) Y-process (uniformTime T N i.castSucc) Y| then 1 else 0)) :=
      Finset.sum_le_sum fun i _ => crossing_bound _ _ _ _
    _ = _ := by
      unfold weightedValue IBMClippedClockTail.value
      rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      unfold IBMClippedClockTail.cell
      split_ifs <;> ring

theorem difference_integrable (T : ℝ≥0) (N : ℕ) :
    Integrable (fun Y => cappedSum T N Y-weightedValue IBMTerminalBracketWeights.interior T N Y)
      gaussianProduct :=
  (cappedSum_integrable T N).sub (weightedValue_integrable _ interior_measurable interior_bound T N)

def differenceClass (T : ℝ≥0) (N : ℕ) : Lp ℝ 1 gaussianProduct :=
  (difference_integrable T N).toL1 _

theorem differenceClass_actual (T : ℝ≥0) (N : ℕ) :
    differenceClass T N =ᵐ[gaussianProduct] fun Y =>
      cappedSum T N Y-weightedValue IBMTerminalBracketWeights.interior T N Y :=
  (difference_integrable T N).coeFn_toL1

theorem differenceClass_norm_bound (δ : ℝ) (T : ℝ≥0) (N : ℕ) :
    ‖differenceClass T N‖ ≤ weightedMean (originBand δ) T N+weightedMean (outerBand δ) T N+
      ∫ Y, IBMClippedClockTail.value δ T N Y ∂gaussianProduct := by
  rw [differenceClass,L1.norm_of_fun_eq_integral_norm]
  calc
    _ ≤ ∫ Y, weightedValue (originBand δ) T N Y+weightedValue (outerBand δ) T N Y+
        IBMClippedClockTail.value δ T N Y ∂gaussianProduct :=
      integral_mono (difference_integrable T N).norm
        (((origin_energy_integrable δ T N).add (outer_energy_integrable δ T N)).add
          (IBMClippedClockTail.value_integrable δ T N))
        (fun Y => by simpa only [Real.norm_eq_abs] using difference_bound δ T N Y)
    _ = _ := by
      calc
        _ = (∫ Y, weightedValue (originBand δ) T N Y+
            weightedValue (outerBand δ) T N Y ∂gaussianProduct)+
            ∫ Y, IBMClippedClockTail.value δ T N Y ∂gaussianProduct :=
          integral_add ((origin_energy_integrable δ T N).add
            (outer_energy_integrable δ T N)) (IBMClippedClockTail.value_integrable δ T N)
        _ = _ := congrArg (fun x => x+
            ∫ Y, IBMClippedClockTail.value δ T N Y ∂gaussianProduct)
          (integral_add (origin_energy_integrable δ T N) (outer_energy_integrable δ T N))

theorem differenceClass_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (differenceClass T) atTop (𝓝 0) := by
  have hm := ((origin_weightedMean_tendsto IBMClippedClockTail.width IBMClippedClockTail.width_tendsto T hT).add
    (outer_weightedMean_tendsto IBMClippedClockTail.width IBMClippedClockTail.width_tendsto T hT)).add
      (IBMClippedClockTail.width_mean_tendsto T)
  simp only [zero_add] at hm
  have hn := squeeze_zero (fun N => norm_nonneg (differenceClass T N))
    (fun N => differenceClass_norm_bound (IBMClippedClockTail.width N) T N) hm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero] using hn

def occupationMean (T : ℝ≥0) : ℝ := ∫ Y, interiorIntegral T Y ∂gaussianProduct

theorem occupationMean_bounds (T : ℝ≥0) : 0 ≤ occupationMean T ∧ occupationMean T ≤ T := by
  have hi := (interior_memLp T).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  constructor
  · exact integral_nonneg fun Y => (interiorIntegral_bounds T Y).1
  · have h := integral_mono hi (integrable_const (T:ℝ)) fun Y => (interiorIntegral_bounds T Y).2
    simpa only [occupationMean,integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul] using h

theorem interiorWeightedMean_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun N => weightedMean IBMTerminalBracketWeights.interior T N) atTop (𝓝 (occupationMean T)) := by
  have h := (interior_error_tendsto T hT).add (interior_mean_tendsto T)
  simp only [zero_add] at h
  exact h.congr' (Eventually.of_forall fun N =>
    (weightedMean_identity _ interior_measurable interior_bound T N).symm)

theorem cappedSum_mean_eq_original (T : ℝ≥0) (N : ℕ) :
    (∫ Y, cappedSum T N Y ∂gaussianProduct) = IBMRawGridObservableTests.terminalClippedMean T N := by
  unfold IBMRawGridObservableTests.terminalClippedMean
  exact integral_congr_ae (ae_of_all _ fun Y => cappedSum_eq_original T N Y)

theorem mean_difference_bound (T : ℝ≥0) (N : ℕ) :
    |IBMRawGridObservableTests.terminalClippedMean T N-weightedMean IBMTerminalBracketWeights.interior T N| ≤
      ‖differenceClass T N‖ := by
  calc
    _ = ‖∫ Y, cappedSum T N Y-weightedValue IBMTerminalBracketWeights.interior T N Y ∂gaussianProduct‖ := by
      simp only [integral_sub (cappedSum_integrable T N)
        (weightedValue_integrable _ interior_measurable interior_bound T N),
        cappedSum_mean_eq_original,weightedMean,Real.norm_eq_abs]
    _ ≤ ∫ Y, ‖cappedSum T N Y-weightedValue IBMTerminalBracketWeights.interior T N Y‖ ∂gaussianProduct :=
      norm_integral_le_integral_norm _
    _ = _ := by rw [differenceClass,L1.norm_of_fun_eq_integral_norm]

theorem terminalClippedMean_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (IBMRawGridObservableTests.terminalClippedMean T) atTop (𝓝 (occupationMean T)) := by
  have hn := (differenceClass_tendsto T hT).norm
  simp only [norm_zero] at hn
  have ha := squeeze_zero (fun N => abs_nonneg
    (IBMRawGridObservableTests.terminalClippedMean T N-weightedMean IBMTerminalBracketWeights.interior T N))
      (mean_difference_bound T) hn
  have hd : Tendsto (fun N => IBMRawGridObservableTests.terminalClippedMean T N-
      weightedMean IBMTerminalBracketWeights.interior T N) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [sub_zero,Real.norm_eq_abs] using ha
  have h := hd.add (interiorWeightedMean_tendsto T hT)
  simpa only [sub_add_cancel,zero_add] using h

theorem nativeTerminalPairing_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (IBMRawGridObservableTests.nativeTerminalPairing T) atTop (𝓝 ((T:ℝ)-occupationMean T)) := by
  have h := (tendsto_const_nhds (x:=(T:ℝ))).sub (terminalClippedMean_tendsto T hT)
  exact h.congr' (Eventually.of_forall fun N =>
    (IBMRawGridObservableTests.nativeTerminalPairing_reduction T N).symm)

end OperatorDerivativeRewrite.Foundation.IBMClippedClockLimit
