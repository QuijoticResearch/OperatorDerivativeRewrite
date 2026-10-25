import Foundation.IBMObservedClockBracket

/-! Actual random-radius capped-clock quadratic variation with horizon H
and future observation R. The original IBM observable pairing is retained. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMObservedClockCap
open InfiniteGaussian GaussianTimeProcess GaussianBrownianQuadraticVariation
open IBMClippedClockCrossing IBMTerminalRiemannOccupation IBMTerminalBracketWeights
open IBMObservedClockOccupation IBMObservedClockBracket IBMOriginBoundaryEnergy
open IBMClippedClockStrongLimit

def cappedSum (H R : ℝ≥0) (N : ℕ) (Y : SampleSpace) : ℝ :=
  ∑ i : Fin (N+1), (cap (process R Y) (process (uniformTime H N i.succ) Y)-
    cap (process R Y) (process (uniformTime H N i.castSucc) Y))^2

private theorem time_grid (H : ℝ≥0) (N : ℕ) (i : Fin (N+2)) :
    uniformTime H N i = IBMUniformClockGridEnergy.grid (H/(N+1)) i.val := by
  unfold uniformTime IBMUniformClockGridEnergy.grid
  push_cast
  ring

theorem cappedSum_eq_original (H R : ℝ≥0) (N : ℕ) (Y : SampleSpace) :
    cappedSum H R N Y = IBMRawGridObservableTests.clippedSquares (H/(N+1)) (N+1) R Y := by
  unfold cappedSum cap IBMRawGridObservableTests.clippedSquares IBMRawGridObservableTests.overlap
  simp only [time_grid,Fin.val_succ,Fin.val_castSucc]
  exact Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    (min |process (IBMUniformClockGridEnergy.grid (H/(N+1)) (i+1)) Y| |process R Y|-
      min |process (IBMUniformClockGridEnergy.grid (H/(N+1)) i) Y| |process R Y|)^2) (N+1)

theorem cappedSum_integrable (H R : ℝ≥0) (N : ℕ) : Integrable (cappedSum H R N) gaussianProduct := by
  have he : cappedSum H R N = IBMRawGridObservableTests.clippedSquares (H/(N+1)) (N+1) R :=
    funext (cappedSum_eq_original H R N)
  rw [he]
  exact IBMRawGridObservableTests.clippedSquares_integrable _ _ _

theorem difference_bound (δ : ℝ) (H R : ℝ≥0) (N : ℕ) (Y : SampleSpace) :
    |cappedSum H R N Y-weightedValue IBMTerminalBracketWeights.interior H R N Y| ≤
      weightedValue (originBand δ) H R N Y+weightedValue (outerBand δ) H R N Y+
        IBMClippedClockTail.value δ H N Y := by
  have he : cappedSum H R N Y-weightedValue IBMTerminalBracketWeights.interior H R N Y =
      ∑ i : Fin (N+1), IBMClippedClockCrossing.error (process R Y)
        (process (uniformTime H N i.castSucc) Y) (process (uniformTime H N i.succ) Y) := by
    unfold cappedSum weightedValue
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    unfold IBMClippedClockCrossing.error
    ring
  rw [he]
  calc
    _ ≤ ∑ i : Fin (N+1), |IBMClippedClockCrossing.error (process R Y)
        (process (uniformTime H N i.castSucc) Y) (process (uniformTime H N i.succ) Y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (N+1), (process (uniformTime H N i.succ) Y-process (uniformTime H N i.castSucc) Y)^2*
        (originBand δ (process (uniformTime H N i.castSucc) Y,process R Y)+
          outerBand δ (process (uniformTime H N i.castSucc) Y,process R Y)+
            (if δ < |process (uniformTime H N i.succ) Y-process (uniformTime H N i.castSucc) Y| then 1 else 0)) :=
      Finset.sum_le_sum fun i _ => crossing_bound _ _ _ _
    _ = _ := by
      unfold weightedValue IBMClippedClockTail.value
      rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      unfold IBMClippedClockTail.cell
      split_ifs <;> ring

private theorem difference_integrable (H R : ℝ≥0) (N : ℕ) :
    Integrable (fun Y => cappedSum H R N Y-weightedValue IBMTerminalBracketWeights.interior H R N Y)
      gaussianProduct :=
  (cappedSum_integrable H R N).sub ((weightedValue_memLp _ interior_measurable interior_bound H R N).integrable (by norm_num))

def differenceClass (H R : ℝ≥0) (N : ℕ) : Lp ℝ 1 gaussianProduct :=
  (difference_integrable H R N).toL1 _

theorem differenceClass_actual (H R : ℝ≥0) (N : ℕ) :
    differenceClass H R N =ᵐ[gaussianProduct] fun Y =>
      cappedSum H R N Y-weightedValue IBMTerminalBracketWeights.interior H R N Y :=
  (difference_integrable H R N).coeFn_toL1

theorem differenceClass_norm_bound (δ : ℝ) (H R : ℝ≥0) (N : ℕ) :
    ‖differenceClass H R N‖ ≤ IBMRandomBoundaryEnergy.weightedMean (originBand δ) H N+
      (∫ Y, weightedValue (outerBand δ) H R N Y ∂gaussianProduct)+
        ∫ Y, IBMClippedClockTail.value δ H N Y ∂gaussianProduct := by
  have ho : Integrable (weightedValue (originBand δ) H R N) gaussianProduct :=
    origin_energy_integrable δ H N
  have hb := (weightedValue_memLp _ (outerBand_measurable δ) (outerBand_bound δ) H R N).integrable (by norm_num)
  rw [differenceClass,L1.norm_of_fun_eq_integral_norm]
  calc
    _ ≤ ∫ Y, weightedValue (originBand δ) H R N Y+weightedValue (outerBand δ) H R N Y+
        IBMClippedClockTail.value δ H N Y ∂gaussianProduct :=
      integral_mono (difference_integrable H R N).norm ((ho.add hb).add (IBMClippedClockTail.value_integrable δ H N))
        (fun Y => by simpa only [Real.norm_eq_abs] using difference_bound δ H R N Y)
    _ = _ := by
      calc
        _ = (∫ Y, weightedValue (originBand δ) H R N Y+weightedValue (outerBand δ) H R N Y ∂gaussianProduct)+
            ∫ Y, IBMClippedClockTail.value δ H N Y ∂gaussianProduct :=
          integral_add (ho.add hb) (IBMClippedClockTail.value_integrable δ H N)
        _ = _ := congrArg (fun x => x+∫ Y, IBMClippedClockTail.value δ H N Y ∂gaussianProduct)
          (integral_add ho hb)

theorem differenceClass_tendsto (H R : ℝ≥0) (hH : 0 < H) (hHR : H < R) :
    Tendsto (differenceClass H R) atTop (𝓝 0) := by
  have hm := ((origin_weightedMean_tendsto IBMClippedClockTail.width IBMClippedClockTail.width_tendsto H hH).add
    (outer_weighted_mean_tendsto H R hHR IBMClippedClockTail.width IBMClippedClockTail.width_tendsto)).add
      (IBMClippedClockTail.width_mean_tendsto H)
  simp only [zero_add] at hm
  have hn := squeeze_zero (fun N => norm_nonneg (differenceClass H R N))
    (fun N => differenceClass_norm_bound (IBMClippedClockTail.width N) H R N) hm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero] using hn

def cappedClass (H R : ℝ≥0) (N : ℕ) : Lp ℝ 1 gaussianProduct :=
  (cappedSum_integrable H R N).toL1 _

theorem cappedClass_actual (H R : ℝ≥0) (N : ℕ) :
    cappedClass H R N =ᵐ[gaussianProduct] cappedSum H R N := (cappedSum_integrable H R N).coeFn_toL1

def occupationClass (H R : ℝ≥0) : Lp ℝ 1 gaussianProduct := clockL1 (occupationL2 H R)

theorem occupationClass_actual (H R : ℝ≥0) :
    occupationClass H R =ᵐ[gaussianProduct] occupation H R :=
  (clockL1_actual (occupationL2 H R)).trans (occupationL2_actual H R)

private theorem cappedClass_decomposition (H R : ℝ≥0) (N : ℕ) :
    cappedClass H R N = differenceClass H R N+
      clockL1 (IBMObservedClockBracket.weightedClass IBMTerminalBracketWeights.interior
        interior_measurable interior_bound H R N) := by
  apply Lp.ext
  filter_upwards [cappedClass_actual H R N,differenceClass_actual H R N,
    Lp.coeFn_add (differenceClass H R N)
      (clockL1 (IBMObservedClockBracket.weightedClass IBMTerminalBracketWeights.interior
        interior_measurable interior_bound H R N)),
    clockL1_actual (IBMObservedClockBracket.weightedClass IBMTerminalBracketWeights.interior
      interior_measurable interior_bound H R N),
    IBMObservedClockBracket.weightedClass_actual _ interior_measurable interior_bound H R N] with Y hc hd ha hl hw
  rw [hc,ha,Pi.add_apply,hd,hl,hw]
  ring

theorem cappedClass_tendsto (H R : ℝ≥0) (hH : 0 < H) (hHR : H < R) :
    Tendsto (cappedClass H R) atTop (𝓝 (occupationClass H R)) := by
  have h := (differenceClass_tendsto H R hH hHR).add
    (clockL1_tendsto _ _ (interior_weightedClass_tendsto H R hHR))
  simp only [zero_add] at h
  exact h.congr' (Eventually.of_forall fun N => (cappedClass_decomposition H R N).symm)

theorem actual_absolute_error_tendsto (H R : ℝ≥0) (hH : 0 < H) (hHR : H < R) :
    Tendsto (fun N => ∫ Y, |cappedSum H R N Y-occupation H R Y| ∂gaussianProduct) atTop (𝓝 0) := by
  have hn := tendsto_iff_norm_sub_tendsto_zero.mp (cappedClass_tendsto H R hH hHR)
  apply hn.congr'
  exact Eventually.of_forall fun N => by
    change ‖cappedClass H R N-occupationClass H R‖ =
      ∫ Y, |cappedSum H R N Y-occupation H R Y| ∂gaussianProduct
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (cappedClass H R N) (occupationClass H R),
      cappedClass_actual H R N,occupationClass_actual H R] with Y hs hc ho
    simp only [hs,Pi.sub_apply,hc,ho,Real.norm_eq_abs]

theorem capped_mean_tendsto (H R : ℝ≥0) (hH : 0 < H) (hHR : H < R) :
    Tendsto (fun N => ∫ Y, cappedSum H R N Y ∂gaussianProduct) atTop
      (𝓝 (∫ Y, occupation H R Y ∂gaussianProduct)) := by
  have h := L1.continuous_integral.continuousAt.tendsto.comp (cappedClass_tendsto H R hH hHR)
  change Tendsto (fun N => L1.integral (cappedClass H R N)) atTop
    (𝓝 (L1.integral (occupationClass H R))) at h
  simp only [L1.integral_eq_integral] at h
  have he : (∫ Y, occupationClass H R Y ∂gaussianProduct) =
      ∫ Y, occupation H R Y ∂gaussianProduct := integral_congr_ae (occupationClass_actual H R)
  rw [he] at h
  exact h.congr' (Eventually.of_forall fun N => integral_congr_ae (cappedClass_actual H R N))

def nativePairing (H R : ℝ≥0) (N : ℕ) : ℝ :=
  inner ℝ (IBMJointIntrinsicDerivative.jointDivergence
    (IBMRawGridCompensation.gridInput (H/(N+1)) (N+1))) (IBMRawGridObservableTests.squareObservation R)

private theorem grid_endpoint (H : ℝ≥0) (N : ℕ) :
    IBMUniformClockGridEnergy.grid (H/(N+1)) (N+1) = H := by
  unfold IBMUniformClockGridEnergy.grid
  have hn : (N+1:ℝ≥0) ≠ 0 := by positivity
  simpa only [Nat.cast_add,Nat.cast_one] using div_mul_cancel₀ H hn

private theorem original_overlap_identity (H R : ℝ≥0) (N : ℕ) (Y : SampleSpace) :
    IBMRawGridObservableTests.overlapEnergy (H/(N+1)) (N+1) R Y =
      (cap (process R Y) (process H Y))^2-cappedSum H R N Y := by
  rw [cappedSum_eq_original]
  change (IBMRawGridObservableTests.overlap R Y (IBMUniformClockGridEnergy.grid (H/(N+1)) (N+1)))^2-
      IBMRawGridObservableTests.clippedSquares (H/(N+1)) (N+1) R Y = _
  rw [grid_endpoint]
  rfl

theorem endpoint_integrable (H R : ℝ≥0) :
    Integrable (fun Y => (cap (process R Y) (process H Y))^2) gaussianProduct := by
  apply ((IBMRawGridObservableTests.overlapEnergy_integrable (H/(0+1)) (0+1) R).add
    (cappedSum_integrable H R 0)).congr
  exact ae_of_all _ fun Y => by
    have h : IBMRawGridObservableTests.overlapEnergy H 1 R Y =
        (cap (process R Y) (process H Y))^2-cappedSum H R 0 Y := by
      simpa using original_overlap_identity H R 0 Y
    simp only [Pi.add_apply,zero_add,div_one]
    rw [h]
    ring

theorem nativePairing_identity (H R : ℝ≥0) (N : ℕ) :
    nativePairing H R N = (∫ Y, (cap (process R Y) (process H Y))^2 ∂gaussianProduct)-
      ∫ Y, cappedSum H R N Y ∂gaussianProduct := by
  rw [nativePairing,IBMRawGridObservableTests.observable_pairing]
  calc
    _ = ∫ Y, (cap (process R Y) (process H Y))^2-cappedSum H R N Y ∂gaussianProduct :=
      integral_congr_ae (ae_of_all _ fun Y => original_overlap_identity H R N Y)
    _ = _ := integral_sub (endpoint_integrable H R) (cappedSum_integrable H R N)

theorem nativePairing_tendsto (H R : ℝ≥0) (hH : 0 < H) (hHR : H < R) :
    Tendsto (nativePairing H R) atTop
      (𝓝 ((∫ Y, (cap (process R Y) (process H Y))^2 ∂gaussianProduct)-
        ∫ Y, occupation H R Y ∂gaussianProduct)) := by
  have h := (tendsto_const_nhds (x:=∫ Y, (cap (process R Y) (process H Y))^2 ∂gaussianProduct)).sub
    (capped_mean_tendsto H R hH hHR)
  exact h.congr' (Eventually.of_forall fun N => (nativePairing_identity H R N).symm)

end OperatorDerivativeRewrite.Foundation.IBMObservedClockCap
