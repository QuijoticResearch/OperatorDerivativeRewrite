import Foundation.IBMSpatialEndpointOperator
import Foundation.IBMSpatialCompletedKernelIdentity

/-! Signed endpoint-minus-kernel reconstruction on the completed spatial test
domain. These are clock-L1-valued operators, not an asserted random dual element. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialSignedReconstruction
open InfiniteGaussian GaussianTimeProcess IBMSpatialBoundedTestOperator
open IBMSpatialKernelTesting IBMSpatialIncrementKernel IBMSpatialClockEnergy
open IBMSpatialCompletedTestLimit IBMSpatialCompletedKernelIdentity

def endpoint (T : ℝ≥0) : Completed →L[ℝ] Values :=
  (IBMSpatialEndpointOperator.operator T).comp realize.toContinuousLinearMap

def finiteOperator (T : ℝ≥0) (N : ℕ) : Completed →L[ℝ] Values :=
  endpoint T-IBMSpatialCompletedTestLimit.finiteOperator T N

def limitOperator (T : ℝ≥0) (hT : 0 < T) : Completed →L[ℝ] Values :=
  endpoint T-IBMSpatialCompletedTestLimit.limitOperator T hT

theorem endpoint_actual (T : ℝ≥0) (z : Completed) :
    endpoint T z =ᵐ[gaussianProduct] fun Y => cellPair (realize z) 0 |process T Y| :=
  IBMSpatialEndpointOperator.value_actual (realize z) T

theorem endpoint_bound (T : ℝ≥0) (z : Completed) : ‖endpoint T z‖ ≤ (T:ℝ)*‖z‖ := by
  have hb := IBMSpatialEndpointOperator.value_norm_bound (realize z) T
  rwa [realize.norm_map] at hb

theorem finite_bound (T : ℝ≥0) (N : ℕ) (z : Completed) :
    ‖finiteOperator T N z‖ ≤ 2*(T:ℝ)*‖z‖ := by
  have hb := norm_sub_le (endpoint T z) (IBMSpatialCompletedTestLimit.finiteOperator T N z)
  have he := endpoint_bound T z
  have hf := IBMSpatialCompletedTestLimit.finite_bound T N z
  change ‖endpoint T z-IBMSpatialCompletedTestLimit.finiteOperator T N z‖ ≤ _
  linarith

theorem limit_bound (T : ℝ≥0) (hT : 0 < T) (z : Completed) :
    ‖limitOperator T hT z‖ ≤ 2*(T:ℝ)*‖z‖ := by
  have hb := norm_sub_le (endpoint T z) (IBMSpatialCompletedTestLimit.limitOperator T hT z)
  have he := endpoint_bound T z
  have hf := IBMSpatialCompletedTestLimit.limit_bound T hT z
  change ‖endpoint T z-IBMSpatialCompletedTestLimit.limitOperator T hT z‖ ≤ _
  linarith

theorem signed_tendsto (T : ℝ≥0) (hT : 0 < T) (z : Completed) :
    Tendsto (fun N => finiteOperator T N z) atTop (𝓝 (limitOperator T hT z)) :=
  tendsto_const_nhds.sub (completed_tendsto T hT z)

theorem finite_actual (T : ℝ≥0) (N : ℕ) (z : Completed) :
    finiteOperator T N z =ᵐ[gaussianProduct] fun Y =>
      cellPair (realize z) 0 |process T Y|-finiteValue (realize z) T N Y := by
  filter_upwards [endpoint_actual T z,IBMSpatialCompletedTestLimit.finite_actual T N z,
    Lp.coeFn_sub (endpoint T z) (IBMSpatialCompletedTestLimit.finiteOperator T N z)] with Y he hf hs
  change finiteOperator T N z Y = _ at hs
  rw [hs,Pi.sub_apply,he,hf]

theorem signed_kernel_actual (T : ℝ≥0) (N : ℕ) (z : Completed) :
    finiteOperator T N z =ᵐ[gaussianProduct] fun Y =>
      ∫ a, (rectangle (cellSet 0 |process T Y|) a-
        kernel (radius (T/(N+1)) Y) (N+1) a)*realize z a ∂(volume.prod volume) := by
  filter_upwards [finite_actual T N z] with Y hY
  rw [hY,finiteValue_kernel]
  have hi := IBMSpatialKernelTesting.cell_pair_integrable (realize z)
    (realize z).continuous.measurable ‖realize z‖ (realize z).norm_coe_le_norm 0 |process T Y|
  have hk : Integrable (fun a => kernel (radius (T/(N+1)) Y) (N+1) a*realize z a)
      (volume.prod volume) := by
    unfold kernel
    simp_rw [Finset.sum_mul]
    apply integrable_finsetSum
    intro i hi
    exact IBMSpatialKernelTesting.cell_pair_integrable (realize z)
      (realize z).continuous.measurable ‖realize z‖ (realize z).norm_coe_le_norm _ _
  unfold cellPair
  rw [← integral_sub hi hk]
  apply integral_congr_ae
  exact ae_of_all _ fun a => (sub_mul _ _ _).symm

end OperatorDerivativeRewrite.Foundation.IBMSpatialSignedReconstruction
