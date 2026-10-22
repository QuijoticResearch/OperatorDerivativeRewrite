import Foundation.IBMClockInnovationObstruction

/-! Arbitrary scenery coefficients cannot turn a first-clock-chaos field into
an observed IBM innovation. This does not exclude higher even clock channels. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMClockMixedSymmetry
open InfiniteGaussian GaussianSampleReflection IBMClockSignSymmetry
open IBMTimeAveragedObservable IBMNaturalFiltrationObstruction IBMClockInnovationObstruction
set_option backward.isDefEq.respectTransparency false

theorem mixed_clock_odd (a : GaussianL2) (h : CoefficientSpace) :
    jointReflection (ProductL2Curry.productTensor gaussianProduct gaussianProduct
      a (firstChaosEmbedding h)) =
        -ProductL2Curry.productTensor gaussianProduct gaussianProduct a (firstChaosEmbedding h) := by
  let F := ProductL2Curry.productTensor gaussianProduct gaussianProduct a (firstChaosEmbedding h)
  apply Lp.ext
  filter_upwards [jointReflection_ae F,
    reflectClock_preserving.quasiMeasurePreserving.ae_eq_comp
      (ProductL2Curry.productTensor_coeFn gaussianProduct gaussianProduct a (firstChaosEmbedding h)),
    ProductL2Curry.productTensor_coeFn gaussianProduct gaussianProduct a (firstChaosEmbedding h),
    (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
      (firstChaos_reflect_ae h), Lp.coeFn_neg F] with ω hr hp ho hc hn
  simp only [Function.comp_def] at hp hc
  change jointReflection F ω = (-F) ω
  rw [hr, hp, hn, Pi.neg_apply, ho]
  change a ω.1 • firstChaosEmbedding h (reflect ω.2) = -(a ω.1 • firstChaosEmbedding h ω.2)
  rw [hc, smul_neg]

theorem mixed_clock_condExp_zero (T : ℝ≥0) (a : GaussianL2) (h : CoefficientSpace) :
    (condExpL2 (μ := IBMSourceLaws.jointMeasure) ℝ ℝ (naturalFiltration.le T)
      (ProductL2Curry.productTensor gaussianProduct gaussianProduct a (firstChaosEmbedding h)) :
        JointL2) = 0 :=
  odd_condExpL2_zero T _ (mixed_clock_odd a h)

theorem mixed_clock_orthogonal (a : GaussianL2) (h : CoefficientSpace)
    (f : JointL2) (hf : f ∈ IntrinsicSpace) :
    inner ℝ (ProductL2Curry.productTensor gaussianProduct gaussianProduct
      a (firstChaosEmbedding h)) f = 0 :=
  odd_inner_zero _ (mixed_clock_odd a h) f hf

end OperatorDerivativeRewrite.Foundation.IBMClockMixedSymmetry
