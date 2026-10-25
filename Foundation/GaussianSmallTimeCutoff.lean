import Foundation.GaussianConditionalClarkOcone
import Foundation.BochnerL2Approximation

/-! Strong small-time cutoff convergence and triviality of shrinking Brownian pasts.
The cutoff is (0,T]; no monotonicity of the positive-time approach is required. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianSmallTimeCutoff
open InfiniteGaussian GaussianTimeProductL2 GaussianPredictableCutoff
open GaussianPredictableFull GaussianPredictableAdjoint GaussianConditionalIto

theorem cut_small_tendsto (U : TimeProbabilityL2) (τ : ℕ → ℝ≥0)
    (hτ : Tendsto τ atTop (𝓝 0)) :
    Tendsto (fun n => cut (τ n) U) atTop (𝓝 0) := by
  apply BochnerL2Approximation.tendsto_of_dominated
    (fun n => cut (τ n) U) (0 : TimeProbabilityL2) U
  · intro n
    filter_upwards [cut_coeFn (τ n) U] with z hz
    rw [hz]
    by_cases hm : z ∈ PredictableRealL2.horizon (τ n) <;> simp [hm]
  · filter_upwards [Lp.coeFn_zero ℝ 2 timeProbability] with z hz
    rw [hz]
    change ‖(0 : ℝ)‖ ≤ ‖U z‖
    simpa only [norm_zero] using norm_nonneg (U z)
  · have hr : Tendsto (fun n => (τ n : ℝ)) atTop (𝓝 0) :=
      NNReal.continuous_coe.continuousAt.tendsto.comp hτ
    filter_upwards [ae_all_iff.mpr (fun n => cut_coeFn (τ n) U),
      Lp.coeFn_zero ℝ 2 timeProbability] with z hz hzero
    rw [hzero]
    change Tendsto (fun n => cut (τ n) U z) atTop (𝓝 (0 : ℝ))
    by_cases hp : 0 < z.1
    · apply tendsto_const_nhds.congr'
      filter_upwards [hr.eventually (gt_mem_nhds hp)] with n hn
      have hm : z ∉ PredictableRealL2.horizon (τ n) :=
        fun hm => (not_le_of_gt hn) hm.1.2
      exact ((hz n).trans (indicator_of_notMem hm _)).symm
    · have he (n : ℕ) : cut (τ n) U z = 0 := by
        rw [hz n, indicator_of_notMem (fun hm => hp hm.1.1)]
      simpa only [he] using (tendsto_const_nhds (x := (0 : ℝ)))

theorem pastProjection_small_tendsto (F : GaussianL2)
    (hb : F ∈ GaussianBrownianGeneratedSpace.brownianL2) (τ : ℕ → ℝ≥0)
    (hτ : Tendsto τ atTop (𝓝 0)) :
    Tendsto (fun n => pastProjection (τ n) F) atTop
      (𝓝 ((∫ ω, F ω ∂gaussianProduct) • InfiniteGaussian.gaussianOne)) := by
  have ht := GaussianContinuousRigidity.integralExtension.continuous.tendsto
    (0 : TimeProbabilityL2) |>.comp (cut_small_tendsto (predictableAdjoint F) τ hτ)
  have he (n : ℕ) : GaussianContinuousRigidity.integralExtension
      (cut (τ n) (predictableAdjoint F)) =
      pastProjection (τ n) F -
        (∫ ω, F ω ∂gaussianProduct) • InfiniteGaussian.gaussianOne := by
    change GaussianContinuousRigidity.integralExtension
      (predictableCut (τ n) (predictableAdjoint F)) = _
    rw [GaussianContinuousRigidity.integralExtension_eq,
      GaussianConditionalClarkOcone.past_representation _ F hb]
  simp only [Function.comp_def, he, map_zero] at ht
  have ha := ht.add (tendsto_const_nhds
    (x := (∫ ω, F ω ∂gaussianProduct) • InfiniteGaussian.gaussianOne))
  simpa only [sub_add_cancel, zero_add] using ha

theorem constant_of_shrinking_pasts (F : GaussianL2) (τ : ℕ → ℝ≥0)
    (hτ : Tendsto τ atTop (𝓝 0)) (hF : ∀ n, F ∈ pastL2 (τ n)) :
    F = (∫ ω, F ω ∂gaussianProduct) • InfiniteGaussian.gaussianOne := by
  have hb := GaussianConditionalClarkOcone.past_mem_brownian (τ 0) (hF 0)
  have ht := pastProjection_small_tendsto F hb τ hτ
  have he (n : ℕ) : pastProjection (τ n) F = F :=
    Submodule.starProjection_eq_self_iff.mpr (hF n)
  simp only [he] at ht
  exact tendsto_nhds_unique tendsto_const_nhds ht

end OperatorDerivativeRewrite.Foundation.GaussianSmallTimeCutoff
