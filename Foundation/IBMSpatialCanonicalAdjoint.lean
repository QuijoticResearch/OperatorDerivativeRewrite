import Foundation.IBMSpatialPredictableSteps
import Foundation.GaussianFiniteHorizonAdjoint

/-! The bounded adjoint of the ORIGINAL ordinary spatial parameter-Ito map.
This is a terminal representer, not the unprojected running signed slope. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialCanonicalAdjoint
open InfiniteGaussian GaussianTimeHilbert GaussianComplexHorizonIto
local instance : MeasurableSpace (ℝ × SampleSpace) :=
  PredictableRealL2.predictable GaussianTimeProcess.naturalFiltration
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
attribute [local irreducible] GaussianParameterizedIto.realIntegral
local instance (T : ℝ≥0) : CompleteSpace (GaussianPredictableHorizon.PredictableDomain T) :=
  (isClosed_aestronglyMeasurable
    (PredictableRealL2.predictable_le GaussianTimeProcess.naturalFiltration)).completeSpace_coe

def representer (T : ℝ≥0) : Lp TimeHilbert 2 gaussianProduct →L[ℝ]
    Lp TimeHilbert 2 (predictableMeasure T) :=
  (GaussianParameterizedIto.realIntegral (volume : Measure ℝ) T).toContinuousLinearMap.adjoint

def scalarAdjoint (T : ℝ≥0) : GaussianL2 →L[ℝ] Lp ℝ 2 (predictableMeasure T) :=
  (realIto T).toContinuousLinearMap.adjoint

theorem representer_norm_le (T : ℝ≥0) (U : Lp TimeHilbert 2 gaussianProduct) :
    ‖representer T U‖ ≤ ‖U‖ := by
  have hi : ‖(GaussianParameterizedIto.realIntegral (volume : Measure ℝ) T).toContinuousLinearMap‖ ≤ 1 := by
    apply (GaussianParameterizedIto.realIntegral (volume : Measure ℝ) T).toContinuousLinearMap.opNorm_le_bound
      (by norm_num)
    intro u
    change ‖GaussianParameterizedIto.realIntegral (volume : Measure ℝ) T u‖ ≤ 1*‖u‖
    rw [(GaussianParameterizedIto.realIntegral (volume : Measure ℝ) T).norm_map, one_mul]
  have h := (representer T).le_opNorm U
  have hn : ‖representer T‖ =
      ‖(GaussianParameterizedIto.realIntegral (volume : Measure ℝ) T).toContinuousLinearMap‖ :=
    ContinuousLinearMap.adjoint.norm_map _
  rw [hn] at h
  exact h.trans (by nlinarith [norm_nonneg U])

private theorem tensor_inner {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (a : Lp ℝ 2 μ) (h : TimeHilbert) (U : Lp TimeHilbert 2 μ) :
    inner ℝ (BochnerClosedOperator.tensor μ a h) U =
      inner ℝ a ((innerSL ℝ h).compLpL 2 μ U) := by
  rw [L2_inner_eq_integral, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [BochnerClosedOperator.tensor_coeFn μ a h,
    (innerSL ℝ h).coeFn_compLpL U] with x ht hu
  rw [ht, hu, real_inner_smul_left, innerSL_apply_apply, Real.inner_apply]

theorem representer_tensor (T : ℝ≥0) (a : GaussianL2) (h : TimeHilbert) :
    representer T (BochnerClosedOperator.tensor gaussianProduct a h) =
      BochnerClosedOperator.tensor (predictableMeasure T) (scalarAdjoint T a) h := by
  apply ext_inner_right ℝ
  intro u
  change inner ℝ
    ((GaussianParameterizedIto.realIntegral (volume : Measure ℝ) T).toContinuousLinearMap.adjoint
      (BochnerClosedOperator.tensor gaussianProduct a h)) u = _
  rw [ContinuousLinearMap.adjoint_inner_left, tensor_inner]
  change inner ℝ a ((innerSL ℝ h).compLpL 2 gaussianProduct
    (GaussianParameterizedIto.realIntegral (volume : Measure ℝ) T u)) = _
  rw [GaussianRealParameterizedItoScalar.realIntegral_scalarization, tensor_inner]
  exact (ContinuousLinearMap.adjoint_inner_left (realIto T).toContinuousLinearMap _ a).symm

theorem representer_scalarization (T : ℝ≥0) (U : Lp TimeHilbert 2 gaussianProduct)
    (h : TimeHilbert) :
    (innerSL ℝ h).compLpL 2 (predictableMeasure T) (representer T U) =
      scalarAdjoint T ((innerSL ℝ h).compLpL 2 gaussianProduct U) := by
  apply ext_inner_left ℝ
  intro a
  rw [← tensor_inner, real_inner_comm]
  change inner ℝ
    ((GaussianParameterizedIto.realIntegral (volume : Measure ℝ) T).toContinuousLinearMap.adjoint U)
    (BochnerClosedOperator.tensor (predictableMeasure T) a h) = _
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ U (GaussianParameterizedIto.realIntegral (volume : Measure ℝ) T
    (BochnerClosedOperator.tensor (predictableMeasure T) a h)) = _
  rw [GaussianParameterizedIto.realIntegral_tensor, real_inner_comm, tensor_inner]
  exact (ContinuousLinearMap.adjoint_inner_right (realIto T).toContinuousLinearMap a
    ((innerSL ℝ h).compLpL 2 gaussianProduct U)).symm

theorem scalarAdjoint_eq (T : ℝ≥0) (F : GaussianL2) :
    scalarAdjoint T F = trimEquiv T (GaussianFiniteHorizonAdjoint.finiteAdjoint T F) := by
  apply ext_inner_right ℝ
  intro a
  have hi := (trimEquiv T).inner_map_map (GaussianFiniteHorizonAdjoint.finiteAdjoint T F)
    ((trimEquiv T).symm a)
  rw [LinearIsometryEquiv.apply_symm_apply] at hi
  rw [hi]
  change inner ℝ ((realIto T).toContinuousLinearMap.adjoint F) a =
    inner ℝ ((GaussianPredictableHorizon.itoIntegral T).toContinuousLinearMap.adjoint F)
      ((trimEquiv T).symm a)
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  rfl

theorem scalar_representation (T : ℝ≥0) (F : GaussianL2)
    (hF : F ∈ GaussianConditionalIto.pastL2 T) :
    realIto T (scalarAdjoint T F) = F-(∫ Y, F Y ∂gaussianProduct) • gaussianOne := by
  rw [scalarAdjoint_eq, realIto_trim]
  exact GaussianFiniteHorizonAdjoint.finiteAdjoint_representation T F hF

theorem representer_dual (T : ℝ≥0) (U : Lp TimeHilbert 2 gaussianProduct)
    (L : TimeHilbert →L[ℝ] ℝ) :
    L.compLpL 2 (predictableMeasure T) (representer T U) =
      scalarAdjoint T (L.compLpL 2 gaussianProduct U) := by
  let e := (InnerProductSpace.toDual ℝ TimeHilbert).symm L
  have he : L = innerSL ℝ e := by
    ext u
    exact (InnerProductSpace.toDual_symm_apply (x := u) (y := L)).symm
  rw [he]
  exact representer_scalarization T U e

end OperatorDerivativeRewrite.Foundation.IBMSpatialCanonicalAdjoint
