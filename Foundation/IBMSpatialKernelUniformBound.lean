import Foundation.IBMSpatialKernelOccupation

/-! Uniform supremum-test bounds for actual spatial-kernel actions and their
clock occupation limits. The constants do not depend on grid or Lipschitz size. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialKernelUniformBound
open InfiniteGaussian GaussianTimeProcess GaussianBrownianQuadraticVariation
open IBMSpatialKernelTesting IBMSpatialIncrementKernel IBMSpatialKernelOccupation
open IBMFoldedClockQuadraticVariation

theorem cell_norm_bound (F : ℝ × ℝ → ℝ) (hF : Measurable F) (C : ℝ)
    (hC : ∀ z, ‖F z‖ ≤ C) (x y : ℝ) : ‖cellPair F x y‖ ≤ C*(y-x)^2 := by
  have hr := cell_rectangle_integrable x y
  have hi := cell_pair_integrable F hF C hC x y
  unfold cellPair
  calc
    _ ≤ ∫ z, ‖rectangle (cellSet x y) z*F z‖ ∂(volume.prod volume) := norm_integral_le_integral_norm _
    _ ≤ ∫ z, C*rectangle (cellSet x y) z ∂(volume.prod volume) := by
      apply integral_mono hi.norm (hr.const_mul C)
      intro z
      by_cases hz : z ∈ cellSet x y ×ˢ cellSet x y
      · simpa only [rectangle,indicator_of_mem hz,one_mul,mul_one] using hC z
      · simp only [rectangle,indicator_of_notMem hz,zero_mul,norm_zero,mul_zero,le_refl]
    _ = _ := by rw [integral_const_mul,cell_area]

theorem raw_mean (T : ℝ≥0) (N : ℕ) :
    (∫ Y, rawSum T N Y ∂gaussianProduct) = (T:ℝ) := by
  unfold rawSum
  rw [integral_finsetSum _ (fun i _ =>
    (GaussianPredictableStep.increment_memLp process_isPreBrownian
      (uniformTime T N i.castSucc) (uniformTime T N i.succ)).integrable_sq)]
  have he (i : Fin (N+1)) :
      (∫ Y, (process (uniformTime T N i.succ) Y-process (uniformTime T N i.castSucc) Y)^2 ∂gaussianProduct) =
        (uniformTime T N i.succ:ℝ)-uniformTime T N i.castSucc :=
    GaussianPredictableStep.integral_increment_sq process_isPreBrownian
      (uniformTime_monotone T N (Fin.castSucc_le_succ i))
  simp_rw [he]
  rw [sum_fin_differences (fun i => (uniformTime T N i:ℝ)),
    (uniformTime_endpoints T N).1,(uniformTime_endpoints T N).2]
  simp

theorem folded_mean_le (T : ℝ≥0) (N : ℕ) :
    (∫ Y, foldedSum T N Y ∂gaussianProduct) ≤ (T:ℝ) := by
  rw [← raw_mean T N]
  apply integral_mono (foldedSum_integrable T N) (rawSum_integrable T N)
  intro Y
  have h := lossValue_nonneg T N Y
  unfold lossValue at h
  linarith

theorem action_norm_bound (F : ℝ × ℝ → ℝ) {K : ℝ≥0} (hF : LipschitzWith K F)
    (C : ℝ) (hC : ∀ z, ‖F z‖ ≤ C) (T : ℝ≥0) (N : ℕ) :
    ‖action F hF C hC T N‖ ≤ C*(T:ℝ) := by
  have hCn : 0 ≤ C := (norm_nonneg (F (0,0))).trans (hC _)
  have hb : ∀ᵐ Y ∂gaussianProduct, ‖action F hF C hC T N Y‖ ≤ C*foldedSum T N Y := by
    filter_upwards [action_actual F hF C hC T N] with Y ha
    rw [ha]
    calc
      _ ≤ ∑ i : Fin (N+1), ‖cellPair F |process (uniformTime T N i.castSucc) Y|
          |process (uniformTime T N i.succ) Y|‖ := norm_sum_le _ _
      _ ≤ _ := by
        unfold foldedSum
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun i _ => cell_norm_bound F hF.continuous.measurable C hC _ _
  have hi := integral_mono_ae ((Lp.memLp (action F hF C hC T N)).integrable (by norm_num)).norm
    ((foldedSum_integrable T N).const_mul C) hb
  rw [← L1.norm_eq_integral_norm,integral_const_mul] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left (folded_mean_le T N) hCn)

theorem occupation_norm_bound (F : ℝ × ℝ → ℝ) {K : ℝ≥0} (hF : LipschitzWith K F)
    (C : ℝ) (hC : ∀ z, ‖F z‖ ≤ C) (T : ℝ≥0) (hT : 0 < T) :
    ‖occupation F hF T‖ ≤ C*(T:ℝ) :=
  le_of_tendsto (action_tendsto F hF C hC T hT).norm
    (Eventually.of_forall (action_norm_bound F hF C hC T))

end OperatorDerivativeRewrite.Foundation.IBMSpatialKernelUniformBound
