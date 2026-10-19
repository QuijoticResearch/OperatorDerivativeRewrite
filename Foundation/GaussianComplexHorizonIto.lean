import Foundation.ComplexL2Isometry
import Foundation.GaussianPredictableFull
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! The existing actual finite-horizon Brownian integral on the trimmed
predictable measure, with its norm-preserving complex extension. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianComplexHorizonIto
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

abbrev predictableMeasure (T : ℝ≥0) :
    @Measure (ℝ × SampleSpace) (PredictableRealL2.predictable naturalFiltration) :=
  (PredictableRealL2.horizonMeasure T gaussianProduct).trim
    (PredictableRealL2.predictable_le naturalFiltration)

def trimEquiv (T : ℝ≥0) : GaussianPredictableHorizon.PredictableDomain T ≃ₗᵢ[ℝ]
    Lp ℝ 2 (predictableMeasure T) :=
  lpMeasToLpTrimLie ℝ ℝ 2 (PredictableRealL2.horizonMeasure T gaussianProduct)
    (PredictableRealL2.predictable_le naturalFiltration)

def realIto (T : ℝ≥0) : Lp ℝ 2 (predictableMeasure T) →ₗᵢ[ℝ] GaussianL2 :=
  (GaussianPredictableHorizon.itoIntegral T).comp (trimEquiv T).symm.toLinearIsometry

theorem realIto_trim (T : ℝ≥0) (u : GaussianPredictableHorizon.PredictableDomain T) :
    realIto T (trimEquiv T u) = GaussianPredictableHorizon.itoIntegral T u := by
  change GaussianPredictableHorizon.itoIntegral T ((trimEquiv T).symm (trimEquiv T u)) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

def integral (T : ℝ≥0) : Lp ℂ 2 (predictableMeasure T) →ₗᵢ[ℝ] Lp ℂ 2 gaussianProduct :=
  @ComplexL2Isometry.lift (ℝ × SampleSpace) SampleSpace
    (PredictableRealL2.predictable naturalFiltration) inferInstance
    (predictableMeasure T) gaussianProduct (realIto T)

def realToComplex (T : ℝ≥0) : Lp ℝ 2 (predictableMeasure T) →L[ℝ]
    Lp ℂ 2 (predictableMeasure T) :=
  @ComplexL2Isometry.ofReal (ℝ × SampleSpace)
    (PredictableRealL2.predictable naturalFiltration) (predictableMeasure T)

theorem integral_norm (T : ℝ≥0) (u : Lp ℂ 2 (predictableMeasure T)) :
    ‖integral T u‖ = ‖u‖ := (integral T).norm_map u

/-- Agreement with the original stochastic integral on every real native
predictable class, including the existing increment-product step domain. -/
theorem integral_trim_ofReal (T : ℝ≥0) (u : GaussianPredictableHorizon.PredictableDomain T) :
    integral T (realToComplex T (trimEquiv T u)) =
      ComplexL2Isometry.ofReal gaussianProduct (GaussianPredictableHorizon.itoIntegral T u) := by
  rw [integral, realToComplex,
    @ComplexL2Isometry.lift_ofReal (ℝ × SampleSpace) SampleSpace
      (PredictableRealL2.predictable naturalFiltration) inferInstance
      (predictableMeasure T) gaussianProduct (realIto T), realIto_trim]

theorem predictableL2_secondCountable (T : ℝ≥0) :
    SecondCountableTopology (Lp ℂ 2 (predictableMeasure T)) := by
  let J := (lpMeas ℂ ℝ (PredictableRealL2.predictable naturalFiltration) 2
    (PredictableRealL2.horizonMeasure T gaussianProduct)).subtypeₗᵢ.comp
      (lpMeasToLpTrimLie ℂ ℝ 2 (PredictableRealL2.horizonMeasure T gaussianProduct)
        (PredictableRealL2.predictable_le naturalFiltration)).symm.toLinearIsometry
  exact J.isometry.isEmbedding.secondCountableTopology

theorem realPredictableL2_secondCountable (T : ℝ≥0) :
    SecondCountableTopology (Lp ℝ 2 (predictableMeasure T)) := by
  let J := (lpMeas ℝ ℝ (PredictableRealL2.predictable naturalFiltration) 2
    (PredictableRealL2.horizonMeasure T gaussianProduct)).subtypeₗᵢ.comp
      (trimEquiv T).symm.toLinearIsometry
  exact J.isometry.isEmbedding.secondCountableTopology

end OperatorDerivativeRewrite.Foundation.GaussianComplexHorizonIto
