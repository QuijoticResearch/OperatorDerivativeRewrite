import Foundation.IBMRidgeNativeLimit

/-! Uniform actual native IBM ridge bounds, independent of observation times
and grid size. The controlling norm uses curvature, not observable L2 alone. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRidgeNativeBound
open InfiniteGaussian IBMRawGridMixedObservable IBMRawGridObservableTests
open IBMClippedClockCovariation IBMClippedClockCrossing IBMUniformClockGridEnergy
open IBMRidgeNativeSource IBMRidgeNativeLimit IBMCorrectionStein

theorem mixedSquares_abs_bound (h : ℝ≥0) (n : ℕ) (R S : ℝ≥0) (Y : SampleSpace) :
    |mixedSquares h n R S Y| ≤ clockSquares h n Y := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  exact mixed_increment_bound _ _ _ _

theorem mixedEnergy_abs_bound (h : ℝ≥0) (n : ℕ) (R S : ℝ≥0) (Y : SampleSpace) :
    |mixedEnergy h n R S Y| ≤ (GaussianTimeProcess.process (grid h n) Y)^2+clockSquares h n Y := by
  have hp (A : ℝ≥0) : 0 ≤ overlap A Y (grid h n) := le_min (abs_nonneg _) (abs_nonneg _)
  have hb (A : ℝ≥0) : overlap A Y (grid h n) ≤ |GaussianTimeProcess.process (grid h n) Y| :=
    min_le_left _ _
  have he : |overlap R Y (grid h n)*overlap S Y (grid h n)| ≤
      (GaussianTimeProcess.process (grid h n) Y)^2 := by
    rw [abs_of_nonneg (mul_nonneg (hp R) (hp S)),← sq_abs,pow_two]
    exact mul_le_mul (hb R) (hb S) (hp S) (abs_nonneg _)
  exact (abs_sub _ _).trans (add_le_add he (mixedSquares_abs_bound h n R S Y))

theorem weighted_energy_mean_bound (w : SampleSpace → ℝ) (hw : Measurable w)
    {C : ℝ} (hC : ∀ Y, ‖w Y‖ ≤ C) (h : ℝ≥0) (n : ℕ) (R S : ℝ≥0) :
    |∫ Y, w Y*mixedEnergy h n R S Y ∂gaussianProduct| ≤ 2*C*(grid h n:ℝ) := by
  have hC0 : 0 ≤ C := (norm_nonneg (w 0)).trans (hC 0)
  have hi := IBMBoundedMixedClockTesting.weighted_integrable w hw hC (mixedEnergy_integrable h n R S)
  have hs := (GaussianTimeProcess.process_memLp (grid h n) 2 (by norm_num)).integrable_sq
  have hc := clockSquares_integrable h n
  calc
    _ ≤ ∫ Y, ‖w Y*mixedEnergy h n R S Y‖ ∂gaussianProduct := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun Y => w Y*mixedEnergy h n R S Y)
    _ ≤ ∫ Y, C*((GaussianTimeProcess.process (grid h n) Y)^2+clockSquares h n Y) ∂gaussianProduct :=
      integral_mono hi.norm ((hs.add hc).const_mul C) fun Y => by
        rw [norm_mul,Real.norm_eq_abs (mixedEnergy h n R S Y)]
        exact mul_le_mul (hC Y) (mixedEnergy_abs_bound h n R S Y) (abs_nonneg _) hC0
    _ = _ := by
      rw [integral_const_mul,integral_add hs hc,clockSquares_mean]
      have he : (∫ Y, (GaussianTimeProcess.process (grid h n) Y)^2 ∂gaussianProduct) = (grid h n:ℝ) := by
        simpa only [pow_two,min_self] using GaussianTimeProcess.process_product_integral (grid h n) (grid h n)
      rw [he]
      ring

theorem observable_ridge_pairing_bound {d : ℕ} (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (c : Fin d → ℝ) (τ : Fin d → ℝ≥0) (h : ℝ≥0) (n : ℕ) :
    |inner ℝ (IBMJointIntrinsicDerivative.jointDivergence (IBMRawGridCompensation.gridInput h n))
      (ridgeObservation g a c τ)| ≤
        (grid h n:ℝ)*SchwartzMap.seminorm ℝ 0 0 (jet g 2)*(∑ i, |c i|)^2 := by
  let C := SchwartzMap.seminorm ℝ 0 0 (jet g 2)
  have hb (i j : Fin d) := weighted_energy_mean_bound (curvature g a c τ)
    (curvature_measurable g a c τ) (curvature_bound g a c τ) h n (τ i) (τ j)
  rw [observable_ridge_pairing,abs_mul]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  calc
    _ ≤ (1/2:ℝ)*∑ i, ∑ j, |c i*c j| * (2*C*(grid h n:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hb i j) (abs_nonneg _)
    _ = _ := by
      simp_rw [abs_mul,mul_assoc,← Finset.mul_sum,← Finset.sum_mul]
      ring

theorem nativeRidgePairing_bound {d : ℕ} (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (c : Fin d → ℝ) (τ : Fin d → ℝ≥0) (H : ℝ≥0) (N : ℕ) :
    |nativeRidgePairing g a c τ H N| ≤
      (H:ℝ)*SchwartzMap.seminorm ℝ 0 0 (jet g 2)*(∑ i, |c i|)^2 := by
  have he : grid (H/(N+1)) (N+1) = H := by
    unfold grid
    have hn : (N+1:ℝ≥0) ≠ 0 := by positivity
    simpa only [Nat.cast_add,Nat.cast_one] using div_mul_cancel₀ H hn
  simpa only [nativeRidgePairing,he] using observable_ridge_pairing_bound g a c τ (H/(N+1)) (N+1)

theorem ridgeLimit_bound {d : ℕ} (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (c : Fin d → ℝ) (τ : Fin d → ℝ≥0) (H : ℝ≥0) (hH : 0 < H) :
    |ridgeLimit g a c τ H| ≤ (H:ℝ)*SchwartzMap.seminorm ℝ 0 0 (jet g 2)*(∑ i, |c i|)^2 :=
  le_of_tendsto (nativeRidgePairing_tendsto g a c τ H hH).abs
    (Eventually.of_forall fun N => nativeRidgePairing_bound g a c τ H N)

end OperatorDerivativeRewrite.Foundation.IBMRidgeNativeBound
