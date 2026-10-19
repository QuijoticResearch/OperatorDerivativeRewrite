import Foundation.GaussianParameterizedIto

/-! Agreement of the transported complex parameter integral with the
original stochastic integral on real predictable scalar tensors. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianParameterizedItoTensor
open InfiniteGaussian GaussianTimeProcess GaussianComplexHorizonIto
open GaussianParameterizedIto ProductL2Curry
local instance : MeasurableSpace (ℝ × SampleSpace) :=
  PredictableRealL2.predictable naturalFiltration
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
attribute [local instance] realPredictableL2_secondCountable predictableL2_secondCountable
variable {P : Type*} [MeasurableSpace P] (ν : Measure P) [SFinite ν]
  [SecondCountableTopology (Lp ℝ 2 ν)] [SecondCountableTopology (Lp ℂ 2 ν)]

theorem realFlat_tensor (T : ℝ≥0) (a : Lp ℝ 2 (predictableMeasure T)) (h : Lp ℝ 2 ν) :
    realFlat ν T (productTensor (predictableMeasure T) ν a h) =
      productTensor gaussianProduct ν (realIto T a) h := by
  apply (curryEquiv gaussianProduct ν).injective
  change curryEquiv gaussianProduct ν
    ((curryEquiv gaussianProduct ν).symm
      (realIntegral ν T (curryEquiv (predictableMeasure T) ν
        (productTensor (predictableMeasure T) ν a h)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change realIntegral ν T (curry (predictableMeasure T) ν
    (productTensor (predictableMeasure T) ν a h)) =
      curry gaussianProduct ν (productTensor gaussianProduct ν (realIto T a) h)
  rw [curry_productTensor,
    realIntegral_tensor, curry_productTensor]

theorem realPart_tensor {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    (a : Lp ℝ 2 μ) (h : Lp ℂ 2 ν) :
    ComplexL2Isometry.realPart (μ.prod ν) (productTensor μ ν a h) =
      productTensor μ ν a (ComplexL2Isometry.realPart ν h) := by
  apply Lp.ext
  have hh := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae_eq_comp
    (Complex.reCLM.coeFn_compLpL h)
  filter_upwards [Complex.reCLM.coeFn_compLpL (productTensor μ ν a h),
    productTensor_coeFn μ ν a h,
    productTensor_coeFn μ ν a (ComplexL2Isometry.realPart ν h), hh] with z hr hp ho hh
  change ComplexL2Isometry.realPart (μ.prod ν) (productTensor μ ν a h) z = _ at hr
  change ComplexL2Isometry.realPart ν h z.2 = _ at hh
  rw [hr, hp, ho, hh]
  change ((a z.1 : ℝ) • h z.2).re = a z.1*(h z.2).re
  simp

theorem imagPart_tensor {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    (a : Lp ℝ 2 μ) (h : Lp ℂ 2 ν) :
    ComplexL2Isometry.imagPart (μ.prod ν) (productTensor μ ν a h) =
      productTensor μ ν a (ComplexL2Isometry.imagPart ν h) := by
  apply Lp.ext
  have hh := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae_eq_comp
    (Complex.imCLM.coeFn_compLpL h)
  filter_upwards [Complex.imCLM.coeFn_compLpL (productTensor μ ν a h),
    productTensor_coeFn μ ν a h,
    productTensor_coeFn μ ν a (ComplexL2Isometry.imagPart ν h), hh] with z hr hp ho hh
  change ComplexL2Isometry.imagPart (μ.prod ν) (productTensor μ ν a h) z = _ at hr
  change ComplexL2Isometry.imagPart ν h z.2 = _ at hh
  rw [hr, hp, ho, hh]
  change ((a z.1 : ℝ) • h z.2).im = a z.1*(h z.2).im
  simp

theorem combine_tensors {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    (a : Lp ℝ 2 μ) (h : Lp ℂ 2 ν) :
    ComplexL2Isometry.combine (μ.prod ν)
      (productTensor μ ν a (ComplexL2Isometry.realPart ν h))
      (productTensor μ ν a (ComplexL2Isometry.imagPart ν h)) = productTensor μ ν a h := by
  rw [← realPart_tensor ν μ, ← imagPart_tensor ν μ, ComplexL2Isometry.combine_parts]

theorem complexFlat_tensor (T : ℝ≥0) (a : Lp ℝ 2 (predictableMeasure T)) (h : Lp ℂ 2 ν) :
    complexFlat ν T (productTensor (predictableMeasure T) ν a h) =
      productTensor gaussianProduct ν (realIto T a) h := by
  rw [complexFlat, ComplexL2Isometry.lift_apply, realPart_tensor, imagPart_tensor,
    realFlat_tensor, realFlat_tensor, combine_tensors]

theorem integral_tensor (T : ℝ≥0) (a : Lp ℝ 2 (predictableMeasure T)) (h : Lp ℂ 2 ν) :
    GaussianParameterizedIto.integral ν T
      (BochnerClosedOperator.tensor (predictableMeasure T) a h) =
      BochnerClosedOperator.tensor gaussianProduct (realIto T a) h := by
  have ht : (curryEquiv (predictableMeasure T) ν (E := ℂ)).symm
      (BochnerClosedOperator.tensor (predictableMeasure T) a h) =
      productTensor (predictableMeasure T) ν a h := by
    apply (curryEquiv (predictableMeasure T) ν).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact (curry_productTensor (predictableMeasure T) ν a h).symm
  change curryEquiv gaussianProduct ν (complexFlat ν T
    ((curryEquiv (predictableMeasure T) ν).symm
      (BochnerClosedOperator.tensor (predictableMeasure T) a h))) = _
  rw [ht, complexFlat_tensor]
  exact curry_productTensor gaussianProduct ν (realIto T a) h

private theorem scalar_tensor {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (L : Lp ℂ 2 ν →L[ℝ] ℝ) (a : Lp ℝ 2 μ) (h : Lp ℂ 2 ν) :
    L.compLpL 2 μ (BochnerClosedOperator.tensor μ a h) = (L h) • a := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (BochnerClosedOperator.tensor μ a h),
    BochnerClosedOperator.tensor_coeFn μ a h, Lp.coeFn_smul (L h) a] with x hL ht hs
  rw [hL, ht, hs, Pi.smul_apply, map_smul]
  simp only [smul_eq_mul, mul_comm]

/-- Scalar testing commutes with the actual target integral on the entire
domain, by finite-rank agreement and native L2 simple-field density. -/
theorem integral_scalarization (T : ℝ≥0) (L : Lp ℂ 2 ν →L[ℝ] ℝ)
    (u : Lp (Lp ℂ 2 ν) 2 (predictableMeasure T)) :
    L.compLpL 2 gaussianProduct (GaussianParameterizedIto.integral ν T u) =
      realIto T (L.compLpL 2 (predictableMeasure T) u) := by
  let F := (L.compLpL 2 gaussianProduct).comp
    (GaussianParameterizedIto.integral ν T).toContinuousLinearMap
  let G := (realIto T).toContinuousLinearMap.comp (L.compLpL 2 (predictableMeasure T))
  have he : ∀ v : Lp (Lp ℂ 2 ν) 2 (predictableMeasure T), F v = G v := by
    intro v
    apply Lp.induction (by simp) (fun v => F v = G v)
    · intro h s hs hfin
      rw [Lp.simpleFunc.coe_indicatorConst, indicatorConstLp_eq_toSpanSingleton_compLp]
      change L.compLpL 2 gaussianProduct
        (GaussianParameterizedIto.integral ν T
          (BochnerClosedOperator.tensor (predictableMeasure T)
            (indicatorConstLp 2 hs hfin.ne (1 : ℝ)) h)) =
        realIto T (L.compLpL 2 (predictableMeasure T)
          (BochnerClosedOperator.tensor (predictableMeasure T)
            (indicatorConstLp 2 hs hfin.ne (1 : ℝ)) h))
      rw [integral_tensor, scalar_tensor, scalar_tensor, map_smul]
    · intro v w hv hw hd heV heW
      rw [map_add, map_add, heV, heW]
    · exact isClosed_eq F.continuous G.continuous
  exact he u

end OperatorDerivativeRewrite.Foundation.GaussianParameterizedItoTensor
