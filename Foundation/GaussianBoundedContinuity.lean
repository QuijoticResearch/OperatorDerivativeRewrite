import Foundation.GaussianBoundedApproximation

/-! Bounded continuous functions of the actual L2-continuous Brownian process
are L2-continuous, without a Lipschitz hypothesis on the scalar function. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianBoundedContinuity
open InfiniteGaussian GaussianTimeProcess GaussianLipschitzIntegrands GaussianBoundedApproximation

theorem boundedValue_continuous {φ : ℝ → ℝ} {M : ℝ} (hφ : Continuous φ)
    (hM : ∀ x, ‖φ x‖ ≤ M) : Continuous (boundedValue hφ hM) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, _, hm⟩ := (tendstoInMeasure_of_tendsto_Lp
    (wienerL2_continuous.continuousAt.tendsto.comp hns)).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  apply BochnerL2Approximation.tendsto_of_dominated _ _ (M • gaussianOne)
  · intro n
    filter_upwards [boundedValue_coeFn hφ hM (ns (ms n)),
      Lp.coeFn_smul M gaussianOne, gaussianOne_coeFn] with ω hv hs ho
    simp only [hv, hs, Pi.smul_apply, ho, smul_eq_mul, mul_one]
    exact (hM _).trans (le_abs_self M)
  · filter_upwards [boundedValue_coeFn hφ hM t,
      Lp.coeFn_smul M gaussianOne, gaussianOne_coeFn] with ω hv hs ho
    simp only [hv, hs, Pi.smul_apply, ho, smul_eq_mul, mul_one]
    exact (hM _).trans (le_abs_self M)
  · filter_upwards [hm, ae_all_iff.mpr (fun n => boundedValue_coeFn hφ hM (ns (ms n))),
      boundedValue_coeFn hφ hM t] with ω hm hn ht
    simp only [hn, ht]
    exact hφ.continuousAt.tendsto.comp hm

end OperatorDerivativeRewrite.Foundation.GaussianBoundedContinuity
