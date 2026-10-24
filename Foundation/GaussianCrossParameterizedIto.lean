import Foundation.GaussianRealParameterizedItoScalar

/-! Naturality of the ORIGINAL parameter-Ito integral between DIFFERENT
spatial parameter measures, on its whole genuine predictable L2 domain. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianCrossParameterizedIto
open InfiniteGaussian GaussianComplexHorizonIto GaussianParameterizedIto
local instance : MeasurableSpace (ℝ × SampleSpace) :=
  PredictableRealL2.predictable GaussianTimeProcess.naturalFiltration
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
attribute [local instance] realPredictableL2_secondCountable predictableL2_secondCountable
variable {P Q : Type*} [MeasurableSpace P] [MeasurableSpace Q]
  (ν : Measure P) (μ : Measure Q) [SFinite ν] [SFinite μ]
  [SecondCountableTopology (Lp ℝ 2 ν)] [SecondCountableTopology (Lp ℂ 2 ν)]
  [SecondCountableTopology (Lp ℝ 2 μ)] [SecondCountableTopology (Lp ℂ 2 μ)]

private theorem map_tensor {X : Type*} [MeasurableSpace X] (ξ : Measure X)
    (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 μ) (a : Lp ℝ 2 ξ) (h : Lp ℝ 2 ν) :
    A.compLpL 2 ξ (BochnerClosedOperator.tensor ξ a h) =
      BochnerClosedOperator.tensor ξ a (A h) := by
  apply Lp.ext
  filter_upwards [A.coeFn_compLpL (BochnerClosedOperator.tensor ξ a h),
    BochnerClosedOperator.tensor_coeFn ξ a h,
    BochnerClosedOperator.tensor_coeFn ξ a (A h)] with x hA ht hr
  rw [hA, ht, hr, map_smul]

theorem realIntegral_map (T : ℝ≥0) (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 μ)
    (u : Lp (Lp ℝ 2 ν) 2 (predictableMeasure T)) :
    A.compLpL 2 gaussianProduct (realIntegral ν T u) =
      realIntegral μ T (A.compLpL 2 (predictableMeasure T) u) := by
  let F := (A.compLpL 2 gaussianProduct).comp (realIntegral ν T).toContinuousLinearMap
  let G := (realIntegral μ T).toContinuousLinearMap.comp (A.compLpL 2 (predictableMeasure T))
  have he (v : Lp (Lp ℝ 2 ν) 2 (predictableMeasure T)) : F v = G v := by
    apply Lp.induction (by simp) (fun v => F v = G v)
    · intro h s hs hfin
      rw [Lp.simpleFunc.coe_indicatorConst, indicatorConstLp_eq_toSpanSingleton_compLp]
      change A.compLpL 2 gaussianProduct
        (realIntegral ν T (BochnerClosedOperator.tensor (predictableMeasure T)
          (indicatorConstLp 2 hs hfin.ne (1 : ℝ)) h)) =
        realIntegral μ T (A.compLpL 2 (predictableMeasure T)
          (BochnerClosedOperator.tensor (predictableMeasure T)
            (indicatorConstLp 2 hs hfin.ne (1 : ℝ)) h))
      rw [realIntegral_tensor, map_tensor, map_tensor, realIntegral_tensor]
    · intro v w _hv _hw _hd heV heW
      rw [map_add, map_add, heV, heW]
    · exact isClosed_eq F.continuous G.continuous
  exact he u

end OperatorDerivativeRewrite.Foundation.GaussianCrossParameterizedIto
