import Foundation.IBMPhysicalClockItoTensor
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal BesselPotentialSpace
open OperatorDerivativeRewrite.Foundation
open InfiniteGaussian GaussianTimeProcess GaussianComplexHorizonIto IBMPhysicalClockIto
namespace DraftNativeScalarization
local instance : NormedSpace ℝ H^{(-1 : ℝ)}(ℝ) := NormedSpace.restrictScalars ℝ ℂ _
def pullback (L : H^{(-1 : ℝ)}(ℝ) →L[ℝ] ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℝ] ℝ :=
  L.comp ((BesselPotentialSpace.toLpₗᵢ ℝ ℂ (-1 : ℝ) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)

theorem decode_test (L : H^{(-1 : ℝ)}(ℝ) →L[ℝ] ℝ)
    (v : Lp (Lp ℂ 2 (volume : Measure ℝ)) 2 gaussianProduct) :
    L.compLpL 2 gaussianProduct (decode v) = (pullback L).compLpL 2 gaussianProduct v := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (decode v),
    BochnerLinearIsometry.lift_coeFn gaussianProduct
      (BesselPotentialSpace.toLpₗᵢ ℝ ℂ (-1 : ℝ) 2).symm.toLinearIsometry v,
    (pullback L).coeFn_compLpL v] with ω hL hd ht
  change decode v ω = _ at hd
  rw [hL, hd, ht]
  rfl

theorem encode_test (T : ℝ≥0) (L : H^{(-1 : ℝ)}(ℝ) →L[ℝ] ℝ)
    (v : Lp (H^{(-1 : ℝ)}(ℝ)) 2 (predictableMeasure T)) :
    (pullback L).compLpL 2 (predictableMeasure T) (encode T v) =
      L.compLpL 2 (predictableMeasure T) v := by
  letI : MeasurableSpace (ℝ × SampleSpace) := PredictableRealL2.predictable naturalFiltration
  apply Lp.ext
  filter_upwards [(pullback L).coeFn_compLpL (encode T v),
    BochnerLinearIsometry.lift_coeFn (predictableMeasure T)
      (BesselPotentialSpace.toLpₗᵢ ℝ ℂ (-1 : ℝ) 2).toLinearIsometry v,
    L.coeFn_compLpL v] with z ht he hL
  change encode T v z = _ at he
  rw [ht, he, hL]
  change L ((BesselPotentialSpace.toLpₗᵢ ℝ ℂ (-1 : ℝ) 2).symm
    ((BesselPotentialSpace.toLpₗᵢ ℝ ℂ (-1 : ℝ) 2) (v z))) = L (v z)
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem native_scalarization (T : ℝ≥0) (L : H^{(-1 : ℝ)}(ℝ) →L[ℝ] ℝ) (u : Domain T) :
    L.compLpL 2 gaussianProduct (IBMPhysicalClockIto.integral T u) =
      realIto T (L.compLpL 2 (predictableMeasure T) (IBMPhysicalClockIto.trimEquiv T u)) := by
  rw [IBMPhysicalClockIto.integral, decode_test,
    GaussianParameterizedItoTensor.integral_scalarization, encode_test]
end DraftNativeScalarization
