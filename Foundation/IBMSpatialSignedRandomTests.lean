import Foundation.IBMSpatialRandomTestConvergence

/-! Actual signed spatial reconstruction for arbitrary Bochner-L2 random
completed tests on the SAME clock space, with no independence assumption. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialSignedRandomTests
open InfiniteGaussian GaussianTimeProcess IBMConstructedSources
open IBMSpatialCompletedTestLimit IBMSpatialRandomTestBounds

theorem clock_square_memLp (T : ℝ≥0) :
    MemLp (fun Y => (clockPath Y T)^2) 2 gaussianProduct := by
  have hp : MemLp (fun Y => (process T Y)^2) 2 gaussianProduct := by
    simpa only [pow_two] using (process_memLp T 4 (by norm_num)).fun_mul
      (process_memLp T 4 (by norm_num))
  exact hp.ae_eq ((clockPath_coordinate_ae T).symm.mono fun Y hY => congrArg (fun x : ℝ => x^2) hY)

def endpointWeight (T : ℝ≥0) : GaussianL2 := (clock_square_memLp T).toLp _

def endpointPath (T : ℝ≥0) (Y : SampleSpace) : Completed →L[ℝ] ℝ :=
  (IBMSpatialPathReconstruction.endpointPath T Y).comp realize.toContinuousLinearMap

theorem endpointPath_measurable (T : ℝ≥0) (z : Completed) :
    Measurable (fun Y => endpointPath T Y z) := by
  have hc := ((ContinuousMap.measurable_eval T).comp clockPath_measurable).norm
  exact (IBMSpatialClockKernelError.cellPair_measurable (realize z) (realize z).continuous.measurable).comp
    (measurable_const.prodMk hc)

theorem endpointPath_bound (T : ℝ≥0) : ∀ᵐ Y ∂gaussianProduct, ∀ z : Completed,
    ‖endpointPath T Y z‖ ≤ ‖endpointWeight T Y‖*‖z‖ := by
  filter_upwards [(clock_square_memLp T).coeFn_toLp] with Y hY
  intro z
  change endpointWeight T Y = _ at hY
  rw [hY,Real.norm_of_nonneg (sq_nonneg _)]
  change ‖IBMSpatialKernelTesting.cellPair (realize z) 0 |clockPath Y T|‖ ≤ (clockPath Y T)^2*‖z‖
  have hb := IBMSpatialKernelUniformBound.cell_norm_bound (realize z)
    (realize z).continuous.measurable ‖realize z‖ (realize z).norm_coe_le_norm 0 |clockPath Y T|
  simpa only [sub_zero,sq_abs,realize.norm_map,mul_comm] using hb

def endpointOperator (T : ℝ≥0) : RandomTests →L[ℝ] IBMSpatialBoundedTestOperator.Values :=
  IBMWeakRandomEvaluation.operator (endpointPath T) (endpointPath_measurable T)
    (endpointWeight T) (endpointPath_bound T)

def finiteOperator (T : ℝ≥0) (N : ℕ) : RandomTests →L[ℝ] IBMSpatialBoundedTestOperator.Values :=
  endpointOperator T-IBMSpatialRandomTestBounds.finiteOperator T N

def limitOperator (T : ℝ≥0) : RandomTests →L[ℝ] IBMSpatialBoundedTestOperator.Values :=
  endpointOperator T-IBMSpatialRandomTestBounds.limitOperator T

theorem finite_actual (T : ℝ≥0) (N : ℕ) (u : RandomTests) :
    finiteOperator T N u =ᵐ[gaussianProduct] fun Y =>
      IBMSpatialKernelTesting.cellPair (realize (u Y)) 0 |clockPath Y T|-
        IBMSpatialBoundedTestOperator.finiteValue (realize (u Y)) T N Y := by
  filter_upwards [IBMWeakRandomEvaluation.value_actual (endpointPath T) (endpointPath_measurable T)
    (endpointWeight T) (endpointPath_bound T) u,IBMSpatialRandomTestBounds.finite_actual T N u,
    Lp.coeFn_sub (endpointOperator T u) (IBMSpatialRandomTestBounds.finiteOperator T N u)] with Y he hf hs
  change finiteOperator T N u Y = _ at hs
  change endpointOperator T u Y = endpointPath T Y (u Y) at he
  rw [hs,Pi.sub_apply,he,hf]
  rfl

theorem limit_actual (T : ℝ≥0) (u : RandomTests) :
    limitOperator T u =ᵐ[gaussianProduct] fun Y =>
      IBMSpatialPathReconstruction.signedPath T Y (realize (u Y)) := by
  filter_upwards [IBMWeakRandomEvaluation.value_actual (endpointPath T) (endpointPath_measurable T)
    (endpointWeight T) (endpointPath_bound T) u,IBMSpatialRandomTestBounds.limit_actual T u,
    Lp.coeFn_sub (endpointOperator T u) (IBMSpatialRandomTestBounds.limitOperator T u)] with Y he hf hs
  change limitOperator T u Y = _ at hs
  change endpointOperator T u Y = endpointPath T Y (u Y) at he
  rw [hs,Pi.sub_apply,he,hf]
  rfl

theorem signed_random_tendsto (T : ℝ≥0) (hT : 0 < T) (u : RandomTests) :
    Tendsto (fun N => finiteOperator T N u) atTop (𝓝 (limitOperator T u)) :=
  tendsto_const_nhds.sub (IBMSpatialRandomTestConvergence.random_tendsto T hT u)

end OperatorDerivativeRewrite.Foundation.IBMSpatialSignedRandomTests
