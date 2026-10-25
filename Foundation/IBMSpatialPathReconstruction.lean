import Foundation.IBMSpatialPathOccupation

/-! A single pathwise bounded linear action with measurable scalar evaluations,
and its exact agreement with the completed signed spatial reconstruction.
No strong measurability in the full norm-dual is inferred. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialPathReconstruction
open InfiniteGaussian IBMConstructedSources IBMSpatialBoundedTestOperator
open IBMSpatialKernelTesting IBMSpatialLipschitzTestLimit IBMSpatialCompletedTestLimit

theorem completed_occupation_eq (T : ℝ≥0) (hT : 0 < T) (z : Completed) :
    IBMSpatialCompletedTestLimit.limitOperator T hT z =
      IBMSpatialPathOccupation.operator T (realize z) := by
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · exact isClosed_eq (IBMSpatialCompletedTestLimit.limitOperator T hT).continuous
      ((IBMSpatialPathOccupation.operator T).continuous.comp realize.continuous)
  · intro F
    rw [limit_coe,realize_coe,IBMSpatialLipschitzTestLimit.limit_apply]
    exact IBMSpatialPathOccupation.old_occupation_eq (F:Tests) (bound_lipschitz F) T

def endpointPath (T : ℝ≥0) (Y : SampleSpace) : Tests →L[ℝ] ℝ :=
  ({ toFun := fun F => cellPair F 0 |clockPath Y T|
     map_add' := fun F G => cellPair_add F G _ _
     map_smul' := fun c F => cellPair_smul c F _ _ } : Tests →ₗ[ℝ] ℝ).mkContinuous
    ((clockPath Y T)^2) (fun F => by
      change ‖cellPair F 0 |clockPath Y T|‖ ≤ (clockPath Y T)^2*‖F‖
      simpa only [sub_zero,sq_abs,mul_comm] using
        IBMSpatialKernelUniformBound.cell_norm_bound F F.continuous.measurable
          ‖F‖ F.norm_coe_le_norm 0 |clockPath Y T|)

def signedPath (T : ℝ≥0) (Y : SampleSpace) : Tests →L[ℝ] ℝ :=
  endpointPath T Y-IBMSpatialPathOccupation.pathOperator T Y

theorem signedPath_apply (T : ℝ≥0) (Y : SampleSpace) (F : Tests) :
    signedPath T Y F = cellPair F 0 |clockPath Y T|-IBMSpatialPathOccupation.pathValue F T Y := rfl

theorem signedPath_bound (T : ℝ≥0) (Y : SampleSpace) (F : Tests) :
    ‖signedPath T Y F‖ ≤ ((clockPath Y T)^2+(T:ℝ))*‖F‖ := by
  rw [signedPath_apply]
  have he : ‖cellPair F 0 |clockPath Y T|‖ ≤ (clockPath Y T)^2*‖F‖ := by
    simpa only [sub_zero,sq_abs,mul_comm] using
      IBMSpatialKernelUniformBound.cell_norm_bound F F.continuous.measurable
        ‖F‖ F.norm_coe_le_norm 0 |clockPath Y T|
  have hp := IBMSpatialPathOccupation.pathValue_bound F T Y
  have hs := norm_sub_le (cellPair F 0 |clockPath Y T|) (IBMSpatialPathOccupation.pathValue F T Y)
  nlinarith

theorem signedPath_norm (T : ℝ≥0) (Y : SampleSpace) :
    ‖signedPath T Y‖ ≤ (clockPath Y T)^2+(T:ℝ) :=
  (signedPath T Y).opNorm_le_bound (by positivity) (signedPath_bound T Y)

theorem signedPath_evaluation_measurable (T : ℝ≥0) (F : Tests) :
    Measurable (fun Y => signedPath T Y F) := by
  have hc : Measurable (fun Y => |clockPath Y T|) :=
    ((ContinuousMap.measurable_eval T).comp clockPath_measurable).norm
  exact ((IBMSpatialClockKernelError.cellPair_measurable F F.continuous.measurable).comp
    (measurable_const.prodMk hc)).sub (IBMSpatialPathOccupation.pathValue_measurable F T)

theorem completed_signed_actual (T : ℝ≥0) (hT : 0 < T) (z : Completed) :
    IBMSpatialSignedReconstruction.limitOperator T hT z =ᵐ[gaussianProduct]
      fun Y => signedPath T Y (realize z) := by
  have hp : IBMSpatialCompletedTestLimit.limitOperator T hT z =ᵐ[gaussianProduct]
      IBMSpatialPathOccupation.pathValue (realize z) T := by
    rw [completed_occupation_eq]
    exact IBMSpatialPathOccupation.value_actual (realize z) T
  filter_upwards [IBMSpatialSignedReconstruction.endpoint_actual T z,hp,
    Lp.coeFn_sub (IBMSpatialSignedReconstruction.endpoint T z)
      (IBMSpatialCompletedTestLimit.limitOperator T hT z),clockPath_coordinate_ae T] with Y he hp hs hc
  change IBMSpatialSignedReconstruction.limitOperator T hT z Y = _ at hs
  rw [hs,Pi.sub_apply,he,hp,signedPath_apply,hc]

theorem completed_occupation_actual (T : ℝ≥0) (hT : 0 < T) (z : Completed) :
    IBMSpatialCompletedTestLimit.limitOperator T hT z =ᵐ[gaussianProduct]
      IBMSpatialPathOccupation.pathValue (realize z) T := by
  rw [completed_occupation_eq]
  exact IBMSpatialPathOccupation.value_actual (realize z) T

end OperatorDerivativeRewrite.Foundation.IBMSpatialPathReconstruction
