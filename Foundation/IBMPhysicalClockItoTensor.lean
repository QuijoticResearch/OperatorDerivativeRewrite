import Foundation.IBMPhysicalClockIto
import Foundation.GaussianParameterizedItoTensor

/-! Finite-rank stochastic agreement for the native physical H^-1 integral. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalClockItoTensor
open InfiniteGaussian GaussianTimeProcess GaussianComplexHorizonIto IBMPhysicalClockIto
local instance : MeasurableSpace (ℝ × SampleSpace) :=
  PredictableRealL2.predictable naturalFiltration
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

def tensor (T : ℝ≥0) (a : Lp ℝ 2 (predictableMeasure T)) (h : H^{(-1 : ℝ)}(ℝ)) : Domain T :=
  (IBMPhysicalClockIto.trimEquiv T).symm
    ((ContinuousLinearMap.toSpanSingleton ℂ h).compLpL 2 (predictableMeasure T)
      (realToComplex T a))

def coefficientTensor (a : GaussianL2) (h : H^{(-1 : ℝ)}(ℝ)) :
    Lp (H^{(-1 : ℝ)}(ℝ)) 2 gaussianProduct :=
  (ContinuousLinearMap.toSpanSingleton ℂ h).compLpL 2 gaussianProduct
    (ComplexL2Isometry.ofReal gaussianProduct a)

theorem tensor_ae (T : ℝ≥0) (a : Lp ℝ 2 (predictableMeasure T)) (h : H^{(-1 : ℝ)}(ℝ)) :
    (tensor T a h : Lp (H^{(-1 : ℝ)}(ℝ)) 2
      (PredictableRealL2.horizonMeasure T gaussianProduct)) =ᵐ[
        PredictableRealL2.horizonMeasure T gaussianProduct] fun z => (a z : ℂ) • h := by
  let f := (ContinuousLinearMap.toSpanSingleton ℂ h).compLpL 2 (predictableMeasure T)
    (realToComplex T a)
  have he := lpTrimToLpMeas_ae_eq (𝕜 := ℂ)
    (PredictableRealL2.predictable_le naturalFiltration) f
  have hf : f =ᵐ[predictableMeasure T] fun z => (a z : ℂ) • h := by
    filter_upwards [(ContinuousLinearMap.toSpanSingleton ℂ h).coeFn_compLpL (realToComplex T a),
      Complex.ofRealCLM.coeFn_compLpL a] with z ht ha
    change realToComplex T a z = _ at ha
    change f z = _ at ht
    rw [ht, ha]
    rfl
  exact he.trans (ae_eq_of_ae_eq_trim hf)

theorem coefficientTensor_ae (a : GaussianL2) (h : H^{(-1 : ℝ)}(ℝ)) :
    coefficientTensor a h =ᵐ[gaussianProduct] fun ω => (a ω : ℂ) • h := by
  filter_upwards [(ContinuousLinearMap.toSpanSingleton ℂ h).coeFn_compLpL
    (ComplexL2Isometry.ofReal gaussianProduct a), Complex.ofRealCLM.coeFn_compLpL a]
    with ω ht ha
  change coefficientTensor a h ω = _ at ht
  change ComplexL2Isometry.ofReal gaussianProduct a ω = _ at ha
  rw [ht, ha]
  rfl

theorem encode_tensor (T : ℝ≥0) (a : Lp ℝ 2 (predictableMeasure T))
    (h : H^{(-1 : ℝ)}(ℝ)) :
    encode T (IBMPhysicalClockIto.trimEquiv T (tensor T a h)) =
      BochnerClosedOperator.tensor (predictableMeasure T) a h.toLp := by
  rw [tensor, LinearIsometryEquiv.apply_symm_apply]
  apply Lp.ext
  filter_upwards [BochnerLinearIsometry.lift_coeFn (predictableMeasure T)
      (BesselPotentialSpace.toLpₗᵢ ℝ ℂ (-1 : ℝ) 2).toLinearIsometry
      ((ContinuousLinearMap.toSpanSingleton ℂ h).compLpL 2 (predictableMeasure T) (realToComplex T a)),
    (ContinuousLinearMap.toSpanSingleton ℂ h).coeFn_compLpL (realToComplex T a),
    Complex.ofRealCLM.coeFn_compLpL a,
    BochnerClosedOperator.tensor_coeFn (predictableMeasure T) a h.toLp] with z he ht ha ho
  change encode T _ z = _ at he
  change realToComplex T a z = _ at ha
  rw [he, ht, ha, ho]
  change ((a z : ℂ) • h).toLp = (a z : ℝ) • h.toLp
  rw [BesselPotentialSpace.toLp_smul, Complex.coe_smul]
  rfl

theorem decode_tensor (a : GaussianL2) (h : H^{(-1 : ℝ)}(ℝ)) :
    decode (BochnerClosedOperator.tensor gaussianProduct a h.toLp) = coefficientTensor a h := by
  apply Lp.ext
  filter_upwards [BochnerLinearIsometry.lift_coeFn gaussianProduct
      (BesselPotentialSpace.toLpₗᵢ ℝ ℂ (-1 : ℝ) 2).symm.toLinearIsometry
      (BochnerClosedOperator.tensor gaussianProduct a h.toLp),
    BochnerClosedOperator.tensor_coeFn gaussianProduct a h.toLp,
    (ContinuousLinearMap.toSpanSingleton ℂ h).coeFn_compLpL
      (ComplexL2Isometry.ofReal gaussianProduct a),
    Complex.ofRealCLM.coeFn_compLpL a] with ω hd ht hc ha
  change decode _ ω = _ at hd
  change coefficientTensor a h ω = _ at hc
  change ComplexL2Isometry.ofReal gaussianProduct a ω = _ at ha
  rw [hd, hc, ht, ha]
  apply BesselPotentialSpace.injective_toLp ℝ ℂ (-1 : ℝ) 2
  change a ω • h.toLp = ((a ω : ℂ) • h).toLp
  rw [BesselPotentialSpace.toLp_smul, Complex.coe_smul]
  rfl

theorem integral_tensor (T : ℝ≥0) (a : Lp ℝ 2 (predictableMeasure T))
    (h : H^{(-1 : ℝ)}(ℝ)) :
    IBMPhysicalClockIto.integral T (tensor T a h) = coefficientTensor (realIto T a) h := by
  rw [IBMPhysicalClockIto.integral, encode_tensor,
    GaussianParameterizedItoTensor.integral_tensor, decode_tensor]

theorem integral_native_tensor (T : ℝ≥0) (a : GaussianPredictableHorizon.PredictableDomain T)
    (h : H^{(-1 : ℝ)}(ℝ)) :
    IBMPhysicalClockIto.integral T (tensor T (GaussianComplexHorizonIto.trimEquiv T a) h) =
      coefficientTensor (GaussianPredictableHorizon.itoIntegral T a) h := by
  rw [integral_tensor, realIto_trim]

theorem integral_native_tensor_ae (T : ℝ≥0) (a : GaussianPredictableHorizon.PredictableDomain T)
    (h : H^{(-1 : ℝ)}(ℝ)) :
    IBMPhysicalClockIto.integral T (tensor T (GaussianComplexHorizonIto.trimEquiv T a) h) =ᵐ[
      gaussianProduct] fun ω => (GaussianPredictableHorizon.itoIntegral T a ω : ℂ) • h := by
  rw [integral_native_tensor]
  exact coefficientTensor_ae _ _

theorem tensor_native_ae (T : ℝ≥0) (a : GaussianPredictableHorizon.PredictableDomain T)
    (h : H^{(-1 : ℝ)}(ℝ)) :
    (tensor T (GaussianComplexHorizonIto.trimEquiv T a) h : Lp (H^{(-1 : ℝ)}(ℝ)) 2
      (PredictableRealL2.horizonMeasure T gaussianProduct)) =ᵐ[
        PredictableRealL2.horizonMeasure T gaussianProduct] fun z => (a.val z : ℂ) • h := by
  have ha := lpMeasToLpTrim_ae_eq (𝕜 := ℝ)
    (PredictableRealL2.predictable_le naturalFiltration) a
  filter_upwards [tensor_ae T (GaussianComplexHorizonIto.trimEquiv T a) h, ha] with z ht ha
  change GaussianComplexHorizonIto.trimEquiv T a z = a.val z at ha
  rw [ht, ha]

end OperatorDerivativeRewrite.Foundation.IBMPhysicalClockItoTensor
