import Foundation.IBMMixedClockSelection

/-! Actual mixed IBM tests: strong original-clock L1 covariation and the
original native divergence pairing. No full-output closure is asserted. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMMixedClockLimit
open InfiniteGaussian GaussianTimeProcess GaussianBrownianQuadraticVariation
open IBMClippedClockCrossing IBMObservedClockCap IBMObservedClockOccupation
open IBMMixedClockSelection IBMRawGridMixedObservable

def mixedOccupation (H R S : ℝ≥0) (Y : SampleSpace) : ℝ :=
  ∫ t : ℝ, (if |IBMConstructedSources.clockPath Y t.toNNReal| <
    min |IBMConstructedSources.clockPath Y R| |IBMConstructedSources.clockPath Y S|
    then 1 else 0) ∂IBMClockOverlapEnergy.window H

theorem selectedOccupation_actual (H R S : ℝ≥0) :
    selectedOccupation H R S =ᵐ[gaussianProduct] mixedOccupation H R S := by
  filter_upwards [IBMConstructedSources.clockPath_coordinate_ae R,
    IBMConstructedSources.clockPath_coordinate_ae S] with Y hr hs
  unfold selectedOccupation select
  rw [← hr,← hs]
  split_ifs with h
  · simp only [mixedOccupation,min_eq_left h,occupation,occupationValue,
      IBMTerminalBracketWeights.interior]
  · simp only [mixedOccupation,min_eq_right (le_of_not_ge h),occupation,occupationValue,
      IBMTerminalBracketWeights.interior]

theorem mixedOccupation_integrable (H R S : ℝ≥0) :
    Integrable (mixedOccupation H R S) gaussianProduct :=
  (selectedOccupation_integrable H R S).congr (selectedOccupation_actual H R S)

def mixedClass (H R S : ℝ≥0) (N : ℕ) : Lp ℝ 1 gaussianProduct :=
  (mixedSum_integrable H R S N).toL1 _

def mixedOccupationClass (H R S : ℝ≥0) : Lp ℝ 1 gaussianProduct :=
  (mixedOccupation_integrable H R S).toL1 _

theorem mixedClass_actual (H R S : ℝ≥0) (N : ℕ) :
    mixedClass H R S N =ᵐ[gaussianProduct] mixedSum H R S N :=
  (mixedSum_integrable H R S N).coeFn_toL1

theorem mixedOccupationClass_actual (H R S : ℝ≥0) :
    mixedOccupationClass H R S =ᵐ[gaussianProduct] mixedOccupation H R S :=
  (mixedOccupation_integrable H R S).coeFn_toL1

theorem mixed_actual_absolute_tendsto (H R S : ℝ≥0) (hH : 0 < H) :
    Tendsto (fun N => ∫ Y, |mixedSum H R S N Y-mixedOccupation H R S Y|
      ∂gaussianProduct) atTop (𝓝 0) := by
  apply (mixed_absolute_error_tendsto H R S hH).congr'
  exact Eventually.of_forall fun N => integral_congr_ae
    ((selectedOccupation_actual H R S).mono fun Y h => by
      change |mixedSum H R S N Y-selectedOccupation H R S Y| = _
      rw [h])

theorem mixedClass_tendsto (H R S : ℝ≥0) (hH : 0 < H) :
    Tendsto (mixedClass H R S) atTop (𝓝 (mixedOccupationClass H R S)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply (mixed_actual_absolute_tendsto H R S hH).congr'
  exact Eventually.of_forall fun N => by
    change (∫ Y, |mixedSum H R S N Y-mixedOccupation H R S Y| ∂gaussianProduct) =
      ‖mixedClass H R S N-mixedOccupationClass H R S‖
    symm
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (mixedClass H R S N) (mixedOccupationClass H R S),
      mixedClass_actual H R S N,mixedOccupationClass_actual H R S] with Y hs hm ho
    simp only [hs,Pi.sub_apply,hm,ho,Real.norm_eq_abs]

theorem mixed_mean_tendsto (H R S : ℝ≥0) (hH : 0 < H) :
    Tendsto (fun N => ∫ Y, mixedSum H R S N Y ∂gaussianProduct) atTop
      (𝓝 (∫ Y, mixedOccupation H R S Y ∂gaussianProduct)) := by
  have h := L1.continuous_integral.continuousAt.tendsto.comp (mixedClass_tendsto H R S hH)
  change Tendsto (fun N => L1.integral (mixedClass H R S N)) atTop
    (𝓝 (L1.integral (mixedOccupationClass H R S))) at h
  simp only [L1.integral_eq_integral] at h
  rw [integral_congr_ae (mixedOccupationClass_actual H R S)] at h
  exact h.congr' (Eventually.of_forall fun N => integral_congr_ae (mixedClass_actual H R S N))

private theorem time_grid (H : ℝ≥0) (N : ℕ) (i : Fin (N+2)) :
    uniformTime H N i = IBMUniformClockGridEnergy.grid (H/(N+1)) i.val := by
  unfold uniformTime IBMUniformClockGridEnergy.grid
  push_cast
  ring

theorem mixedSum_eq_original (H R S : ℝ≥0) (N : ℕ) (Y : SampleSpace) :
    mixedSum H R S N Y = mixedSquares (H/(N+1)) (N+1) R S Y := by
  unfold mixedSum mixedSquares cap IBMRawGridObservableTests.overlap
  simp only [time_grid,Fin.val_succ,Fin.val_castSucc]
  exact Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    (min |process (IBMUniformClockGridEnergy.grid (H/(N+1)) (i+1)) Y| |process R Y|-
      min |process (IBMUniformClockGridEnergy.grid (H/(N+1)) i) Y| |process R Y|)*
    (min |process (IBMUniformClockGridEnergy.grid (H/(N+1)) (i+1)) Y| |process S Y|-
      min |process (IBMUniformClockGridEnergy.grid (H/(N+1)) i) Y| |process S Y|)) (N+1)

private theorem grid_endpoint (H : ℝ≥0) (N : ℕ) :
    IBMUniformClockGridEnergy.grid (H/(N+1)) (N+1) = H := by
  unfold IBMUniformClockGridEnergy.grid
  have hn : (N+1:ℝ≥0) ≠ 0 := by positivity
  simpa only [Nat.cast_add,Nat.cast_one] using div_mul_cancel₀ H hn

theorem mixedEnergy_identity (H R S : ℝ≥0) (N : ℕ) (Y : SampleSpace) :
    mixedEnergy (H/(N+1)) (N+1) R S Y =
      cap (process R Y) (process H Y)*cap (process S Y) (process H Y)-mixedSum H R S N Y := by
  rw [mixedSum_eq_original]
  unfold mixedEnergy
  rw [grid_endpoint]
  rfl

theorem mixed_endpoint_integrable (H R S : ℝ≥0) :
    Integrable (fun Y => cap (process R Y) (process H Y)*cap (process S Y) (process H Y))
      gaussianProduct := by
  apply ((mixedEnergy_integrable (H/(0+1)) (0+1) R S).add
    (mixedSum_integrable H R S 0)).congr
  exact Eventually.of_forall fun Y => by
    have he := mixedEnergy_identity H R S 0 Y
    simp only [Pi.add_apply]
    norm_num only [Nat.cast_zero,zero_add,div_one] at he ⊢
    rw [he]
    ring

def nativeMixedPairing (H R S : ℝ≥0) (N : ℕ) : ℝ :=
  inner ℝ (IBMJointIntrinsicDerivative.jointDivergence
    (IBMRawGridCompensation.gridInput (H/(N+1)) (N+1))) (mixedObservation R S)

theorem nativeMixedPairing_identity (H R S : ℝ≥0) (N : ℕ) :
    nativeMixedPairing H R S N =
      (∫ Y, cap (process R Y) (process H Y)*cap (process S Y) (process H Y) ∂gaussianProduct)-
        ∫ Y, mixedSum H R S N Y ∂gaussianProduct := by
  rw [nativeMixedPairing,observable_mixed_pairing]
  simp_rw [mixedEnergy_identity]
  exact integral_sub (mixed_endpoint_integrable H R S) (mixedSum_integrable H R S N)

theorem nativeMixedPairing_tendsto (H R S : ℝ≥0) (hH : 0 < H) :
    Tendsto (nativeMixedPairing H R S) atTop
      (𝓝 ((∫ Y, cap (process R Y) (process H Y)*cap (process S Y) (process H Y) ∂gaussianProduct)-
        ∫ Y, mixedOccupation H R S Y ∂gaussianProduct)) := by
  have h := (tendsto_const_nhds (x:=∫ Y, cap (process R Y) (process H Y)*
    cap (process S Y) (process H Y) ∂gaussianProduct)).sub (mixed_mean_tendsto H R S hH)
  exact h.congr' (Eventually.of_forall fun N => (nativeMixedPairing_identity H R S N).symm)

end OperatorDerivativeRewrite.Foundation.IBMMixedClockLimit
