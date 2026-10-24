import Foundation.IBMPhysicalFullClockAdjoint
import Foundation.GaussianConditionalClarkOcone

/-! Genuine CLOCK Brownian Clark--Ocone for physical scenery-tested ACTUAL IBM.
Both original derivative-domain and raw Brownian-measurability premises are
discharged. This does not assert intrinsic IBM-filtration representation. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalSceneryTestClarkOcone
open InfiniteGaussian IBMPhysicalWeakWiener IBMPhysicalSceneryTestClockGraph
open GaussianTimeProcess GaussianPredictableFull GaussianPredictableAdjoint
open GaussianBrownianGeneratedSpace GaussianBrownianPRP GaussianConditionalClarkOcone
open GaussianConditionalIto GaussianPredictableCutoff
local instance : NormedSpace ℝ Kernel := NormedSpace.restrictScalars ℝ ℂ _

theorem point_mem_past (t : ℝ≥0) (L : Tests) : point t L ∈ pastL2 t := by
  have hm : StronglyMeasurable[naturalFiltration t] (fun Y =>
      inner ℝ (testNoise L) (IBMContinuousScenery.sourceScenery |process t Y|)) :=
    ((innerSL ℝ (testNoise L)).continuous.comp
      (IBMContinuousScenery.sourceScenery_continuous.comp continuous_abs)).stronglyMeasurable
        |>.comp_measurable
        (process_stronglyAdapted t).measurable
  have he : point t L =
      (innerSL ℝ (testNoise L)).compLpL 2 gaussianProduct (IBMRandomTimeHilbert.randomSourceL2 t) :=
    projection_flip _ L
  have ha : point t L =ᵐ[gaussianProduct] fun Y =>
      inner ℝ (testNoise L) (IBMContinuousScenery.sourceScenery |process t Y|) := by
    rw [he]
    filter_upwards [(innerSL ℝ (testNoise L)).coeFn_compLpL
      (IBMRandomTimeHilbert.randomSourceL2 t),
      (IBMRandomTimeHilbert.randomSourceClass_memLp t).coeFn_toLp] with Y hi hs
    change IBMRandomTimeHilbert.randomSourceL2 t Y = _ at hs
    rw [hi, hs]
    rfl
  exact hm.aestronglyMeasurable.congr ha.symm

def representer (t : ℝ≥0) (L : Tests) : fullPredictable :=
  predictableProjection (gradient t L)

theorem representer_eq_adjoint (t : ℝ≥0) (ht : 0 < t) (L : Tests) :
    representer t L = predictableAdjoint (point t L) := by
  have h := predictableAdjoint_eq_projected_derivative ⟨point t L, point_mem t ht L⟩
  rw [derivative_value t ht L] at h
  exact h.symm

theorem clark_ocone (t : ℝ≥0) (ht : 0 < t) (L : Tests) :
    point t L - (∫ Y, point t L Y ∂gaussianProduct) • gaussianOne =
      itoIntegral (representer t L) := by
  have h := GaussianBrownianPRP.clark_ocone ⟨point t L, point_mem t ht L⟩
    (past_mem_brownian t (point_mem_past t L))
  rw [derivative_value t ht L] at h
  exact h

theorem actual_clark_ocone (t : ℝ≥0) (ht : 0 < t) (L : Tests) :
    ∀ᵐ Y ∂gaussianProduct,
      (∫ X, IBMConstructedSources.ibmValue t (X,Y) * testNoise L X ∂gaussianProduct) -
        (∫ Z, (∫ X, IBMConstructedSources.ibmValue t (X,Z) * testNoise L X
          ∂gaussianProduct) ∂gaussianProduct) = itoIntegral (representer t L) Y := by
  let m : ℝ := ∫ Y, point t L Y ∂gaussianProduct
  have hm : m = ∫ Z, (∫ X, IBMConstructedSources.ibmValue t (X,Z) * testNoise L X
      ∂gaussianProduct) ∂gaussianProduct := integral_congr_ae (point_actual_ae t L)
  filter_upwards [point_actual_ae t L, gaussianOne_coeFn,
    Lp.coeFn_sub (point t L) (m • gaussianOne), Lp.coeFn_smul m gaussianOne]
    with Y hY hOne hSub hSmul
  have h := congrArg (fun F : GaussianL2 => F Y) (clark_ocone t ht L)
  change (point t L-m • gaussianOne) Y = itoIntegral (representer t L) Y at h
  rw [hSub, Pi.sub_apply, hSmul, Pi.smul_apply, hY, hOne, smul_eq_mul, mul_one, hm] at h
  exact h

theorem representer_supported (t : ℝ≥0) (ht : 0 < t) (L : Tests) :
    predictableCut t (representer t L) = representer t L := by
  rw [representer_eq_adjoint t ht L]
  exact past_representer_supported t (point t L) (point_mem_past t L)

theorem representer_unique (t : ℝ≥0) (ht : 0 < t) (L : Tests) (U : fullPredictable)
    (hU : itoIntegral U = point t L - (∫ Y, point t L Y ∂gaussianProduct) • gaussianOne) :
    U = representer t L :=
  itoIntegral.injective (hU.trans (clark_ocone t ht L))

theorem conditional_clark_ocone (s t : ℝ≥0) (ht : 0 < t) (L : Tests) :
    point t L - pastProjection s (point t L) =
      itoIntegral (representer t L - predictableCut s (representer t L)) := by
  have h := GaussianConditionalClarkOcone.conditional_clark_ocone s
    ⟨point t L, point_mem t ht L⟩ (past_mem_brownian t (point_mem_past t L))
  rw [derivative_value t ht L] at h
  exact h

end OperatorDerivativeRewrite.Foundation.IBMPhysicalSceneryTestClarkOcone
