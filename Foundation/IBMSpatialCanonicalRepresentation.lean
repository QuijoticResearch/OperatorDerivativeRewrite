import Foundation.IBMSpatialCanonicalAdjoint
import Foundation.GaussianClockBochnerContraction

/-! Genuine spatial Brownian representation on the full past-measurable L2
domain, retaining its clock mean. No original derivative domain is enlarged. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialCanonicalRepresentation
open InfiniteGaussian GaussianTimeHilbert GaussianComplexHorizonIto
open IBMSpatialCanonicalAdjoint IBMSpatialHilbertRetract
local instance : MeasurableSpace (ℝ × SampleSpace) :=
  PredictableRealL2.predictable GaussianTimeProcess.naturalFiltration
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
attribute [local irreducible] GaussianParameterizedIto.realIntegral

def mean : Lp TimeHilbert 2 gaussianProduct →L[ℝ] TimeHilbert :=
  GaussianClockBochnerContraction.contract InfiniteGaussian.gaussianOne

theorem mean_integral (U : Lp TimeHilbert 2 gaussianProduct) : mean U = ∫ Y, U Y ∂gaussianProduct := by
  rw [mean, GaussianClockBochnerContraction.contract_integral]
  apply integral_congr_ae
  filter_upwards [InfiniteGaussian.gaussianOne_coeFn] with Y hy
  rw [hy, one_smul]

def center : Lp TimeHilbert 2 gaussianProduct →L[ℝ] Lp TimeHilbert 2 gaussianProduct :=
  ContinuousLinearMap.id ℝ _-(Lp.constL 2 gaussianProduct ℝ).comp mean

theorem center_scalarization (U : Lp TimeHilbert 2 gaussianProduct) (h : TimeHilbert) :
    (innerSL ℝ h).compLpL 2 gaussianProduct (center U) =
      (innerSL ℝ h).compLpL 2 gaussianProduct U-
        (∫ Y, ((innerSL ℝ h).compLpL 2 gaussianProduct U) Y ∂gaussianProduct) •
          InfiniteGaussian.gaussianOne := by
  have hm : inner ℝ h (mean U) =
      ∫ Y, ((innerSL ℝ h).compLpL 2 gaussianProduct U) Y ∂gaussianProduct := by
    rw [mean_integral, ← integral_inner ((Lp.memLp U).integrable (by norm_num)) h]
    apply integral_congr_ae
    filter_upwards [(innerSL ℝ h).coeFn_compLpL U] with Y hy
    rw [hy]
    rfl
  apply Lp.ext
  filter_upwards [(innerSL ℝ h).coeFn_compLpL (center U),
    Lp.coeFn_sub U (Lp.const 2 gaussianProduct (mean U)), Lp.coeFn_const 2 gaussianProduct (mean U),
    (innerSL ℝ h).coeFn_compLpL U,
    Lp.coeFn_sub ((innerSL ℝ h).compLpL 2 gaussianProduct U)
      ((∫ Y, ((innerSL ℝ h).compLpL 2 gaussianProduct U) Y ∂gaussianProduct) •
        InfiniteGaussian.gaussianOne),
    Lp.coeFn_smul (∫ Y, ((innerSL ℝ h).compLpL 2 gaussianProduct U) Y ∂gaussianProduct)
      InfiniteGaussian.gaussianOne, InfiniteGaussian.gaussianOne_coeFn]
    with Y hc hs hk hu hd ha h1
  change center U Y = _ at hs
  rw [hc, hs, Pi.sub_apply, hk, hd, Pi.sub_apply, ha, Pi.smul_apply, h1, hu]
  simp only [innerSL_apply_apply, inner_sub_right, smul_eq_mul, mul_one, Function.const_apply, hm]

private theorem scalar_ext (U V : Lp TimeHilbert 2 gaussianProduct)
    (h : ∀ e : TimeHilbert, (innerSL ℝ e).compLpL 2 gaussianProduct U =
      (innerSL ℝ e).compLpL 2 gaussianProduct V) : U = V := by
  apply lift.injective
  apply IBMPhysicalLpSeparation.ext
  intro L
  let A := L.comp model.toContinuousLinearMap
  let e := (InnerProductSpace.toDual ℝ TimeHilbert).symm A
  have he : A = innerSL ℝ e := by
    ext u
    exact (InnerProductSpace.toDual_symm_apply (x := u) (y := A)).symm
  have hc (W : Lp TimeHilbert 2 gaussianProduct) :
      L.compLpL 2 gaussianProduct (lift W) = A.compLpL 2 gaussianProduct W := by
    apply Lp.ext
    filter_upwards [L.coeFn_compLpL (lift W), lift_ae W, A.coeFn_compLpL W] with Y hl hw ha
    rw [hl, hw, ha]
    rfl
  rw [hc U, hc V, he]
  exact h e

theorem representation (T : ℝ≥0) (U : Lp TimeHilbert 2 gaussianProduct)
    (hU : AEStronglyMeasurable[GaussianTimeProcess.naturalFiltration T] U gaussianProduct) :
    GaussianParameterizedIto.realIntegral (volume : Measure ℝ) T (representer T U) = center U := by
  apply scalar_ext
  intro h
  rw [GaussianRealParameterizedItoScalar.realIntegral_scalarization,
    representer_scalarization, center_scalarization]
  apply scalar_representation
  exact ((innerSL ℝ h).continuous.comp_aestronglyMeasurable hU).congr
    ((innerSL ℝ h).coeFn_compLpL U).symm

theorem representation_unique (T : ℝ≥0) (U : Lp TimeHilbert 2 gaussianProduct)
    (hU : AEStronglyMeasurable[GaussianTimeProcess.naturalFiltration T] U gaussianProduct) :
    ∃! u : Lp TimeHilbert 2 (predictableMeasure T),
      GaussianParameterizedIto.realIntegral (volume : Measure ℝ) T u = center U := by
  refine ⟨representer T U, representation T U hU, ?_⟩
  intro v hv
  exact (GaussianParameterizedIto.realIntegral (volume : Measure ℝ) T).injective
    (hv.trans (representation T U hU).symm)

def input (T : ℝ≥0) (U : Lp TimeHilbert 2 gaussianProduct) : IBMSpatialPredictableSteps.Domain T :=
  (IBMSpatialPredictableSteps.trim T).symm (representer T U)

theorem integral_input (T : ℝ≥0) (U : Lp TimeHilbert 2 gaussianProduct)
    (hU : AEStronglyMeasurable[GaussianTimeProcess.naturalFiltration T] U gaussianProduct) :
    IBMSpatialPredictableSteps.integral T (input T U) = center U := by
  rw [IBMSpatialPredictableSteps.integral, input, LinearIsometryEquiv.apply_symm_apply]
  exact representation T U hU

end OperatorDerivativeRewrite.Foundation.IBMSpatialCanonicalRepresentation
