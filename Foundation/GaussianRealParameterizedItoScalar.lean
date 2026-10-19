import Foundation.GaussianParameterizedItoTensor

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
open OperatorDerivativeRewrite.Foundation
open InfiniteGaussian GaussianTimeProcess GaussianComplexHorizonIto GaussianParameterizedIto
namespace OperatorDerivativeRewrite.Foundation.GaussianRealParameterizedItoScalar
local instance : MeasurableSpace (ℝ × SampleSpace) := PredictableRealL2.predictable naturalFiltration
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
attribute [local instance] realPredictableL2_secondCountable predictableL2_secondCountable
variable {P : Type*} [MeasurableSpace P] (ν : Measure P) [SFinite ν]
  [SecondCountableTopology (Lp ℝ 2 ν)] [SecondCountableTopology (Lp ℂ 2 ν)]

private theorem scalar_tensor {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (L : Lp ℝ 2 ν →L[ℝ] ℝ) (a : Lp ℝ 2 μ) (h : Lp ℝ 2 ν) :
    L.compLpL 2 μ (BochnerClosedOperator.tensor μ a h) = (L h) • a := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (BochnerClosedOperator.tensor μ a h),
    BochnerClosedOperator.tensor_coeFn μ a h, Lp.coeFn_smul (L h) a] with x hL ht hs
  rw [hL, ht, hs, Pi.smul_apply, map_smul]
  simp only [smul_eq_mul, mul_comm]

theorem realIntegral_scalarization (T : ℝ≥0) (L : Lp ℝ 2 ν →L[ℝ] ℝ)
    (u : Lp (Lp ℝ 2 ν) 2 (predictableMeasure T)) :
    L.compLpL 2 gaussianProduct (realIntegral ν T u) =
      realIto T (L.compLpL 2 (predictableMeasure T) u) := by
  let F := (L.compLpL 2 gaussianProduct).comp (realIntegral ν T).toContinuousLinearMap
  let G := (realIto T).toContinuousLinearMap.comp (L.compLpL 2 (predictableMeasure T))
  have he : ∀ v : Lp (Lp ℝ 2 ν) 2 (predictableMeasure T), F v = G v := by
    intro v
    apply Lp.induction (by simp) (fun v => F v = G v)
    · intro h s hs hfin
      rw [Lp.simpleFunc.coe_indicatorConst, indicatorConstLp_eq_toSpanSingleton_compLp]
      change L.compLpL 2 gaussianProduct
        (realIntegral ν T (BochnerClosedOperator.tensor (predictableMeasure T)
          (indicatorConstLp 2 hs hfin.ne (1 : ℝ)) h)) =
        realIto T (L.compLpL 2 (predictableMeasure T)
          (BochnerClosedOperator.tensor (predictableMeasure T)
            (indicatorConstLp 2 hs hfin.ne (1 : ℝ)) h))
      rw [realIntegral_tensor, scalar_tensor, scalar_tensor, map_smul]
    · intro v w hv hw hd heV heW
      rw [map_add, map_add, heV, heW]
    · exact isClosed_eq F.continuous G.continuous
  exact he u
private theorem map_tensor {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (a : Lp ℝ 2 μ) (h : Lp ℝ 2 ν) :
    A.compLpL 2 μ (BochnerClosedOperator.tensor μ a h) = BochnerClosedOperator.tensor μ a (A h) := by
  apply Lp.ext
  filter_upwards [A.coeFn_compLpL (BochnerClosedOperator.tensor μ a h),
    BochnerClosedOperator.tensor_coeFn μ a h,BochnerClosedOperator.tensor_coeFn μ a (A h)] with x hA ht hr
  rw [hA,ht,hr,map_smul]

theorem realIntegral_naturality (T : ℝ≥0) (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν)
    (u : Lp (Lp ℝ 2 ν) 2 (predictableMeasure T)) :
    A.compLpL 2 gaussianProduct (realIntegral ν T u) =
      realIntegral ν T (A.compLpL 2 (predictableMeasure T) u) := by
  let F := (A.compLpL 2 gaussianProduct).comp (realIntegral ν T).toContinuousLinearMap
  let G := (realIntegral ν T).toContinuousLinearMap.comp (A.compLpL 2 (predictableMeasure T))
  have he : ∀ v : Lp (Lp ℝ 2 ν) 2 (predictableMeasure T), F v = G v := by
    intro v
    apply Lp.induction (by simp) (fun v => F v = G v)
    · intro h s hs hfin
      rw [Lp.simpleFunc.coe_indicatorConst,indicatorConstLp_eq_toSpanSingleton_compLp]
      change A.compLpL 2 gaussianProduct
        (realIntegral ν T (BochnerClosedOperator.tensor (predictableMeasure T)
          (indicatorConstLp 2 hs hfin.ne (1 : ℝ)) h)) =
        realIntegral ν T (A.compLpL 2 (predictableMeasure T)
          (BochnerClosedOperator.tensor (predictableMeasure T)
            (indicatorConstLp 2 hs hfin.ne (1 : ℝ)) h))
      rw [realIntegral_tensor,map_tensor,map_tensor,realIntegral_tensor]
    · intro v w hv hw hd heV heW
      rw [map_add,map_add,heV,heW]
    · exact isClosed_eq F.continuous G.continuous
  exact he u
end OperatorDerivativeRewrite.Foundation.GaussianRealParameterizedItoScalar
