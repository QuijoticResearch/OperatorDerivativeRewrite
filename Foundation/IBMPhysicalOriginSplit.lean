import Foundation.IBMPhysicalCorrectedVariation
import Foundation.IBMPhysicalClockItoTensor
import Foundation.BrownianMassLimitIdentification

/-! The genuine origin term in the ORIGINAL signed-Dirac running integral.
All sign-domain and finite-horizon identifications are proved. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalOriginSplit
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianPredictableFull
open IBMPhysicalWeakWiener IBMPhysicalReflectedPrimitive IBMPhysicalDirac
open IBMPhysicalCorrectedRunning IBMPhysicalCellSlope BrownianClockWeightedEnergy
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _
attribute [local instance] IBMPhysicalNegativeEmbedding.realNormSMul
  IBMPhysicalNegativeEmbedding.realContinuousSMul
attribute [local irreducible] IBMPhysicalReflectedPrimitive.slope

def signDomain (T : ℝ≥0) : GaussianPredictableHorizon.PredictableDomain T :=
  ⟨restriction T (BrownianSignIntegral.predictableField T),
    restriction_predictable T (BrownianSignIntegral.predictableField T)⟩

theorem signDomain_ae (T : ℝ≥0) : (signDomain T).val =ᵐ[
    PredictableRealL2.horizonMeasure T gaussianProduct] fun z => BrownianSignIntegral.signum (sigma z) := by
  filter_upwards [LpToLpRestrictCLM_coeFn ℝ (PredictableRealL2.horizon T)
    (BrownianSignIntegral.field T), ae_restrict_of_ae (BrownianSignIntegral.field_coeFn T),
    ae_restrict_mem (PredictableRealL2.horizon_measurable T)] with z hr hf hz
  change (signDomain T).val z = BrownianSignIntegral.field T z at hr
  rw [hr, hf, indicator_of_mem hz]

theorem signDomain_integral (T : ℝ≥0) :
    GaussianPredictableHorizon.itoIntegral T (signDomain T) = BrownianSignIntegral.terminal T := by
  have he : GaussianPredictableHorizon.horizonEmbedding T (signDomain T) =
      domainEquiv (BrownianSignIntegral.predictableField T) := by
    apply Subtype.ext
    apply Lp.ext
    have hz := (ae_eq_restrict_iff_indicator_ae_eq (PredictableRealL2.horizon_measurable T)).mp
      (signDomain_ae T)
    filter_upwards [L2ZeroExtension_coeFn (PredictableRealL2.horizon_measurable T)
      (signDomain T).val, hz, BrownianSignIntegral.field_coeFn T] with z he hz hf
    change L2ZeroExtension (PredictableRealL2.horizon_measurable T) (signDomain T).val z =
      BrownianSignIntegral.field T z
    rw [he, hz, hf]
  change GaussianPredictableL2Completion.productIntegral _ =
    GaussianPredictableL2Completion.productIntegral _
  exact congrArg GaussianPredictableL2Completion.productIntegral he

def originDomain (T : ℝ≥0) : IBMPhysicalClockIto.Domain T :=
  IBMPhysicalClockItoTensor.tensor T (GaussianComplexHorizonIto.trimEquiv T (signDomain T)) (dirac 0)

theorem originDomain_ae (T : ℝ≥0) : (originDomain T).val =ᵐ[
    PredictableRealL2.horizonMeasure T gaussianProduct] fun z =>
      BrownianSignIntegral.signum (sigma z) • dirac 0 := by
  filter_upwards [IBMPhysicalClockItoTensor.tensor_native_ae T (signDomain T) (dirac 0),
    signDomain_ae T] with z ht hs
  change (originDomain T).val z = ((signDomain T).val z : ℂ) • dirac 0 at ht
  rw [ht, hs, Complex.coe_smul]
  module

theorem origin_integral (T : ℝ≥0) : IBMPhysicalClockIto.integral T (originDomain T) =
    IBMPhysicalClockItoTensor.coefficientTensor (BrownianSignIntegral.terminal T) (dirac 0) := by
  rw [originDomain, IBMPhysicalClockItoTensor.integral_native_tensor, signDomain_integral]

theorem original_domain_split (T : ℝ≥0) : IBMPhysicalPointClockIntegral.limitIntegrand T =
    stopped T T+originDomain T := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [IBMPhysicalPointClockIntegral.limitIntegrand_ae T, stopped_ae T T,
    originDomain_ae T, Lp.coeFn_add (stopped T T).val (originDomain T).val,
    ae_restrict_mem (PredictableRealL2.horizon_measurable T)] with z hp hs ho ha hz
  simp only [Pi.add_apply] at ha
  change (IBMPhysicalPointClockIntegral.limitIntegrand T).val z =
    ((stopped T T).val+(originDomain T).val) z
  rw [hp, ha, hs, ho, indicator_of_mem hz]
  change BrownianSignIntegral.signum (sigma z) • dirac |sigma z| = _
  rw [slope_sign_identity]
  module

theorem original_integral_split (T : ℝ≥0) :
    IBMPhysicalPointClockIntegral.limitIntegralValue T = running T+
      IBMPhysicalClockItoTensor.coefficientTensor (BrownianSignIntegral.terminal T) (dirac 0) := by
  change IBMPhysicalClockIto.integral T (IBMPhysicalPointClockIntegral.limitIntegrand T) = _
  rw [original_domain_split]
  change IBMPhysicalClockIto.integralIsometry T (stopped T T+originDomain T) = _
  rw [map_add]
  exact congrArg₂ (fun x y : Lp Kernel 2 gaussianProduct => x+y)
    (stopped_integral T T le_rfl) (origin_integral T)

end OperatorDerivativeRewrite.Foundation.IBMPhysicalOriginSplit
