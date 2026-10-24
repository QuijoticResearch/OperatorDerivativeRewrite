import Foundation.IBMSpatialPointClockEnergy

/-! The ordinary spatial-L2 clock integrals embed into the ORIGINAL physical
H^-1 integrals. This is agreement of actual operators, not a new realization. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialPointClockRealization
open InfiniteGaussian GaussianTimeProcess GaussianTimeHilbert IBMSpatialPointClockEnergy
open IBMPhysicalWeakWiener IBMPhysicalNegativeEmbedding GaussianComplexHorizonIto
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable

theorem spatial_embedding (n : ℕ) (r : ℝ) :
    embedding (IBMSpatialPointClockEnergy.spatial n r) = IBMPhysicalPointClockField.spatial n r := by
  rw [IBMSpatialPointClockEnergy.spatial, map_smul, IBMPhysicalPointClockField.spatial]
  rfl

private theorem trim_scalar_match (n : ℕ) (T : ℝ≥0) (L : Tests) :
    (L.comp embedding).compLpL 2 (predictableMeasure T) (trim n T) =
      L.compLpL 2 (predictableMeasure T)
        (IBMPhysicalClockIto.trimEquiv T (IBMPhysicalPointClockIntegral.integrand n T)) := by
  letI : MeasurableSpace (ℝ × SampleSpace) := PredictableRealL2.predictable naturalFiltration
  apply Lp.ext
  apply ae_eq_trim_of_measurable (PredictableRealL2.predictable_le naturalFiltration)
    (Lp.stronglyMeasurable _).measurable (Lp.stronglyMeasurable _).measurable
  have ho := lpMeasToLpTrim_ae_eq (PredictableRealL2.predictable_le naturalFiltration)
    (input n T)
  have hp := lpMeasToLpTrim_ae_eq (PredictableRealL2.predictable_le naturalFiltration)
    (IBMPhysicalPointClockIntegral.integrand n T)
  filter_upwards [ae_eq_of_ae_eq_trim ((L.comp embedding).coeFn_compLpL (trim n T)),
    ae_eq_of_ae_eq_trim (L.coeFn_compLpL
      (IBMPhysicalClockIto.trimEquiv T (IBMPhysicalPointClockIntegral.integrand n T))),
    ho, hp, input_ae n T, IBMPhysicalPointClockIntegral.integrand_ae n T]
    with z hl hr ho hp hi hj
  change trim n T z = _ at ho
  change IBMPhysicalClockIto.trimEquiv T (IBMPhysicalPointClockIntegral.integrand n T) z = _ at hp
  rw [hl, hr, ho, hp, hi, hj]
  exact congrArg L (spatial_embedding n (BrownianClockWeightedEnergy.sigma z))

theorem integral_embedding (n : ℕ) (T : ℝ≥0) :
    embedding.compLpL 2 gaussianProduct (integralValue n T) =
      IBMPhysicalPointClockIntegral.integralValue n T := by
  apply IBMPhysicalLpSeparation.ext
  intro L
  have hc : L.compLpL 2 gaussianProduct (embedding.compLpL 2 gaussianProduct (integralValue n T)) =
      (L.comp embedding).compLpL 2 gaussianProduct (integralValue n T) := by
    apply Lp.ext
    filter_upwards [L.coeFn_compLpL (embedding.compLpL 2 gaussianProduct (integralValue n T)),
      embedding.coeFn_compLpL (integralValue n T),
      (L.comp embedding).coeFn_compLpL (integralValue n T)] with Y hl he hr
    rw [hl, he, hr]
    rfl
  rw [hc]
  change (L.comp embedding).compLpL 2 gaussianProduct
    (GaussianParameterizedIto.realIntegral volume T (trim n T)) = _
  rw [GaussianRealParameterizedItoScalar.realIntegral_scalarization,
    trim_scalar_match, ← IBMPhysicalClockItoScalar.native_scalarization]
  rfl

end OperatorDerivativeRewrite.Foundation.IBMSpatialPointClockRealization
