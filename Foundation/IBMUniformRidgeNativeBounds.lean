import Foundation.IBMFiniteRidgeNativeReconstruction

/-! Grid-uniform, observation-time-independent bounds for actual ridge tests.
The frequency weight is the square of the finite coefficient l1 norm. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMUniformRidgeNativeBounds
open InfiniteGaussian GaussianTimeProcess GaussianBrownianQuadraticVariation
open IBMClippedClockCrossing IBMFiniteRidgeObservation

theorem mixed_norm_bound (H R S : ℝ≥0) (N : ℕ) :
    ‖IBMMixedClockStrongL2.mixedL2 H R S N‖ ≤ 3*(H:ℝ) := by
  apply le_trans (b := ‖quadraticVariation (uniformTime H N)‖)
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [IBMMixedClockStrongL2.mixedL2_actual H R S N,
      IBMMixedClockStrongL2.mixedSum_raw_bound H R S N] with Y ha hb
    rwa [ha]
  · exact IBMSpatialRandomTestBounds.quadraticVariation_norm_bound H N

theorem endpoint_norm_bound (H R S : ℝ≥0) :
    ‖IBMActualQuadraticL2Reconstruction.endpoint H R S‖ ≤ 3*(H:ℝ) := by
  apply le_trans (b := ‖IBMSpatialSignedRandomTests.endpointWeight H‖)
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [IBMActualQuadraticL2Reconstruction.endpoint_actual H R S,
      (IBMSpatialSignedRandomTests.clock_square_memLp H).coeFn_toLp,
      IBMConstructedSources.clockPath_coordinate_ae H] with Y ha he hc
    change IBMSpatialSignedRandomTests.endpointWeight H Y = _ at he
    have hp (r : ℝ) : 0 ≤ cap r (process H Y) := le_min (abs_nonneg _) (abs_nonneg _)
    rw [ha,he,hc,norm_mul,Real.norm_of_nonneg (hp _),Real.norm_of_nonneg (hp _),
      Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [cap,← pow_two,sq_abs] using mul_le_mul
      (min_le_left |process H Y| |process R Y|)
      (min_le_left |process H Y| |process S Y|) (hp _) (abs_nonneg _)
  · exact IBMJointTestNormBounds.endpointWeight_norm_bound H

theorem quadratic_native_bound (H R S : ℝ≥0) (N : ℕ) :
    ‖IBMActualQuadraticL2Reconstruction.native H R S N‖ ≤ 6*(H:ℝ) := by
  exact (norm_sub_le _ _).trans (by
    have he := endpoint_norm_bound H R S
    have hm := mixed_norm_bound H R S N
    linarith)

variable {ι : Type*} [Fintype ι] (a : ι → ℝ) (r : ι → ℝ≥0)

def amplitude : ℝ := ∑ i, |a i|

theorem quadratic_ridge_bound (H : ℝ≥0) (N : ℕ) :
    ‖IBMFiniteRidgeQuadraticTesting.native a r H N‖ ≤ 6*(H:ℝ)*(amplitude a)^2 := by
  calc
    _ ≤ ∑ i, ‖∑ j, (a i*a j) • IBMActualQuadraticL2Reconstruction.native H (r i) (r j) N‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, |a i| * |a j| * (6*(H:ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul,Real.norm_eq_abs,abs_mul]
      exact mul_le_mul_of_nonneg_left (quadratic_native_bound H (r i) (r j) N)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by
      simp only [amplitude,pow_two,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl fun j _ => by ring

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) {C : ℝ}
  (hC : ∀ x, ‖deriv (deriv φ) x‖ ≤ C)

theorem multiplier_bound (u : GaussianL2) :
    ‖IBMFiniteRidgeNativeReconstruction.multiplier a r hφ hC u‖ ≤ (C/2)*‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [IBMFiniteRidgeNativeReconstruction.multiplier_actual a r hφ hC u] with Y hY
  rw [hY,norm_mul]
  exact mul_le_mul_of_nonneg_right (IBMBoundedC2SecondProjection.coefficient_bound hC _)
    (norm_nonneg _)

theorem native_bound (H : ℝ≥0) (N : ℕ) :
    ‖IBMFiniteRidgeNativeReconstruction.native a r hφ hC H N‖ ≤
      3*(H:ℝ)*C*(amplitude a)^2 := by
  have hCn : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hb := (multiplier_bound a r hφ hC
    (IBMFiniteRidgeQuadraticTesting.native a r H N)).trans
      (mul_le_mul_of_nonneg_left (quadratic_ridge_bound a r H N) (by positivity : 0 ≤ C/2))
  change ‖IBMFiniteRidgeNativeReconstruction.native a r hφ hC H N‖ ≤ _ at hb
  nlinarith

theorem reconstruction_bound (H : ℝ≥0) (hH : 0 < H) :
    ‖IBMFiniteRidgeNativeReconstruction.reconstruction a r hφ hC H‖ ≤
      3*(H:ℝ)*C*(amplitude a)^2 :=
  le_of_tendsto (IBMFiniteRidgeNativeReconstruction.native_tendsto a r hφ hC H hH).norm
    (Eventually.of_forall fun N => native_bound a r hφ hC H N)

end OperatorDerivativeRewrite.Foundation.IBMUniformRidgeNativeBounds
