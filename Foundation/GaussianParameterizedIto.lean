import Foundation.GaussianComplexHorizonIto
import Foundation.ProductL2Flip

/-! Actual Hilbert-valued Brownian integration for L2 parameter targets.
The construction flips the existing real L2 factors, lifts the ACTUAL scalar
Ito isometry, and complexifies that isometry on the flat product space. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianParameterizedIto
open InfiniteGaussian GaussianTimeProcess GaussianComplexHorizonIto
local instance : MeasurableSpace (ℝ × SampleSpace) :=
  PredictableRealL2.predictable naturalFiltration
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
attribute [local instance] realPredictableL2_secondCountable predictableL2_secondCountable
variable {P : Type*} [MeasurableSpace P] (ν : Measure P) [SFinite ν]
  [SecondCountableTopology (Lp ℝ 2 ν)] [SecondCountableTopology (Lp ℂ 2 ν)]

def realIntegral (T : ℝ≥0) : Lp (Lp ℝ 2 ν) 2 (predictableMeasure T) →ₗᵢ[ℝ]
    Lp (Lp ℝ 2 ν) 2 gaussianProduct :=
  (ProductL2Curry.flip ν gaussianProduct).comp
    ((BochnerLinearIsometry.lift ν (realIto T)).comp
      (@ProductL2Curry.flip (ℝ × SampleSpace) P
        (PredictableRealL2.predictable naturalFiltration) inferInstance
        (predictableMeasure T) ν inferInstance inferInstance inferInstance inferInstance))

theorem realIntegral_tensor (T : ℝ≥0) (a : Lp ℝ 2 (predictableMeasure T)) (h : Lp ℝ 2 ν) :
    realIntegral ν T (BochnerClosedOperator.tensor (predictableMeasure T) a h) =
      BochnerClosedOperator.tensor gaussianProduct (realIto T a) h := by
  change ProductL2Curry.flip ν gaussianProduct
    (BochnerLinearIsometry.lift ν (realIto T)
      (ProductL2Curry.flip (predictableMeasure T) ν
        (BochnerClosedOperator.tensor (predictableMeasure T) a h))) = _
  rw [ProductL2Curry.flip_tensor, BochnerLinearIsometry.lift_tensor, ProductL2Curry.flip_tensor]

def realFlat (T : ℝ≥0) : Lp ℝ 2 ((predictableMeasure T).prod ν) →ₗᵢ[ℝ]
    Lp ℝ 2 (gaussianProduct.prod ν) :=
  (ProductL2Curry.curryEquiv gaussianProduct ν).symm.toLinearIsometry.comp
    ((realIntegral ν T).comp
      (@ProductL2Curry.curryEquiv (ℝ × SampleSpace) P ℝ
        (PredictableRealL2.predictable naturalFiltration) inferInstance
        inferInstance inferInstance (predictableMeasure T) ν inferInstance inferInstance
        inferInstance inferInstance).toLinearIsometry)

def complexFlat (T : ℝ≥0) : Lp ℂ 2 ((predictableMeasure T).prod ν) →ₗᵢ[ℝ]
    Lp ℂ 2 (gaussianProduct.prod ν) :=
  @ComplexL2Isometry.lift ((ℝ × SampleSpace) × P) (SampleSpace × P)
    ((PredictableRealL2.predictable naturalFiltration).prod inferInstance) inferInstance
    ((predictableMeasure T).prod ν) (gaussianProduct.prod ν) (realFlat ν T)

def integral (T : ℝ≥0) : Lp (Lp ℂ 2 ν) 2 (predictableMeasure T) →ₗᵢ[ℝ]
    Lp (Lp ℂ 2 ν) 2 gaussianProduct :=
  (ProductL2Curry.curryEquiv gaussianProduct ν (E := ℂ)).toLinearIsometry.comp
    ((complexFlat ν T).comp
      (@ProductL2Curry.curryEquiv (ℝ × SampleSpace) P ℂ
        (PredictableRealL2.predictable naturalFiltration) inferInstance
        inferInstance inferInstance (predictableMeasure T) ν inferInstance inferInstance
        inferInstance inferInstance).symm.toLinearIsometry)

theorem integral_norm (T : ℝ≥0) (u : Lp (Lp ℂ 2 ν) 2 (predictableMeasure T)) :
    ‖integral ν T u‖ = ‖u‖ := (integral ν T).norm_map u

end OperatorDerivativeRewrite.Foundation.GaussianParameterizedIto
