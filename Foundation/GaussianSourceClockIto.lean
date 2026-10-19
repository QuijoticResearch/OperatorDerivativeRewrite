import Foundation.GaussianRealParameterizedItoScalar

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
open OperatorDerivativeRewrite.Foundation
open InfiniteGaussian GaussianTimeProcess GaussianComplexHorizonIto GaussianParameterizedIto
namespace OperatorDerivativeRewrite.Foundation.GaussianSourceClockIto
open GaussianPredictableFull GaussianTimeProductL2
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
abbrev Domain (T : ℝ≥0) := lpMeas GaussianL2 ℝ
  (PredictableRealL2.predictable naturalFiltration) 2 (PredictableRealL2.horizonMeasure T gaussianProduct)

def trimEquiv (T : ℝ≥0) : Domain T ≃ₗᵢ[ℝ] Lp GaussianL2 2 (predictableMeasure T) :=
  lpMeasToLpTrimLie GaussianL2 ℝ 2 (PredictableRealL2.horizonMeasure T gaussianProduct)
    (PredictableRealL2.predictable_le naturalFiltration)

def integral (T : ℝ≥0) : Domain T →ₗᵢ[ℝ] Lp GaussianL2 2 gaussianProduct :=
  (realIntegral gaussianProduct T).comp (trimEquiv T).toLinearIsometry

theorem integral_norm (T : ℝ≥0) (u : Domain T) : ‖integral T u‖ = ‖u‖ := (integral T).norm_map u

def tensor (T : ℝ≥0) (a : Lp ℝ 2 (predictableMeasure T)) (h : GaussianL2) : Domain T :=
  by
  letI : MeasurableSpace (ℝ × SampleSpace) := PredictableRealL2.predictable naturalFiltration
  exact (trimEquiv T).symm (BochnerClosedOperator.tensor (predictableMeasure T) a h)

theorem integral_tensor (T : ℝ≥0) (a : Lp ℝ 2 (predictableMeasure T)) (h : GaussianL2) :
    integral T (tensor T a h) = BochnerClosedOperator.tensor gaussianProduct (realIto T a) h := by
  letI : MeasurableSpace (ℝ × SampleSpace) := PredictableRealL2.predictable naturalFiltration
  change realIntegral gaussianProduct T ((trimEquiv T) ((trimEquiv T).symm _)) = _
  rw [LinearIsometryEquiv.apply_symm_apply,realIntegral_tensor]

theorem native_scalarization (T : ℝ≥0) (L : GaussianL2 →L[ℝ] ℝ) (u : Domain T) :
    L.compLpL 2 gaussianProduct (integral T u) =
      realIto T (L.compLpL 2 (predictableMeasure T) (trimEquiv T u)) :=
  GaussianRealParameterizedItoScalar.realIntegral_scalarization gaussianProduct T L (trimEquiv T u)
theorem scalarization_full (T : ℝ≥0) (L : GaussianL2 →L[ℝ] ℝ)
    (u : Domain T) (v : fullPredictable)
    (hv : (v : TimeProbabilityL2) =ᵐ[timeProbability]
      (PredictableRealL2.horizon T).indicator (fun z => L (u.val z))) :
    L.compLpL 2 gaussianProduct (integral T u) = itoIntegral v := by
  let a := L.compLpL 2 (predictableMeasure T) (trimEquiv T u)
  let S := (GaussianComplexHorizonIto.trimEquiv T).symm a
  have he : (S : Lp ℝ 2 (PredictableRealL2.horizonMeasure T gaussianProduct)) =ᵐ[
      PredictableRealL2.horizonMeasure T gaussianProduct] fun z => L (u.val z) := by
    have hs := lpTrimToLpMeas_ae_eq (𝕜 := ℝ) (PredictableRealL2.predictable_le naturalFiltration) a
    have hc := ae_eq_of_ae_eq_trim (L.coeFn_compLpL (trimEquiv T u))
    have hu := lpMeasToLpTrim_ae_eq (𝕜 := ℝ) (PredictableRealL2.predictable_le naturalFiltration) u
    filter_upwards [hs,hc,hu] with z hs hc hu
    change S.val z = a z at hs
    change a z = L (trimEquiv T u z) at hc
    change trimEquiv T u z = u.val z at hu
    rw [hs,hc,hu]
  have hzero : L2ZeroExtension (PredictableRealL2.horizon_measurable T) S.val = v.val := by
    apply Lp.ext
    exact (L2ZeroExtension_coeFn (PredictableRealL2.horizon_measurable T) S.val).trans
      (((ae_eq_restrict_iff_indicator_ae_eq (PredictableRealL2.horizon_measurable T)).mp he).trans hv.symm)
  rw [native_scalarization]
  change GaussianPredictableHorizon.itoIntegral T S = itoIntegral v
  change GaussianPredictableL2Completion.productIntegral (GaussianPredictableHorizon.horizonEmbedding T S) =
    GaussianPredictableL2Completion.productIntegral (domainEquiv v)
  congr 1
  apply Subtype.ext
  exact hzero


/-- Bounded source operators act on the actual native predictable field. -/
def mapField (T : ℝ≥0) (A : GaussianL2 →L[ℝ] GaussianL2) (u : Domain T) : Domain T :=
  (trimEquiv T).symm (A.compLpL 2 (predictableMeasure T) (trimEquiv T u))

theorem mapField_ae (T : ℝ≥0) (A : GaussianL2 →L[ℝ] GaussianL2) (u : Domain T) :
    (mapField T A u).val =ᵐ[PredictableRealL2.horizonMeasure T gaussianProduct]
      fun z => A (u.val z) := by
  let a := A.compLpL 2 (predictableMeasure T) (trimEquiv T u)
  have hs := lpTrimToLpMeas_ae_eq (𝕜 := ℝ) (PredictableRealL2.predictable_le naturalFiltration) a
  have hc := ae_eq_of_ae_eq_trim (A.coeFn_compLpL (trimEquiv T u))
  have hu := lpMeasToLpTrim_ae_eq (𝕜 := ℝ) (PredictableRealL2.predictable_le naturalFiltration) u
  filter_upwards [hs,hc,hu] with z hs hc hu
  change (mapField T A u).val z = a z at hs
  change a z = A (trimEquiv T u z) at hc
  change trimEquiv T u z = u.val z at hu
  rw [hs,hc,hu]

theorem integral_mapField (T : ℝ≥0) (A : GaussianL2 →L[ℝ] GaussianL2) (u : Domain T) :
    A.compLpL 2 gaussianProduct (integral T u) = integral T (mapField T A u) := by
  change A.compLpL 2 gaussianProduct (realIntegral gaussianProduct T (trimEquiv T u)) =
    realIntegral gaussianProduct T ((trimEquiv T) ((trimEquiv T).symm _))
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact GaussianRealParameterizedItoScalar.realIntegral_naturality gaussianProduct T A (trimEquiv T u)
end OperatorDerivativeRewrite.Foundation.GaussianSourceClockIto
