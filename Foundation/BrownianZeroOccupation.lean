import Foundation.BrownianClockWeightedEnergy

/-! Almost every actual continuous Brownian path spends zero Lebesgue time at zero. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianZeroOccupation
open InfiniteGaussian IBMConstructedSources BrownianClockWeightedEnergy

theorem zero_time_ae (T : ℝ≥0) : ∀ᵐ ω ∂gaussianProduct,
    ∀ᵐ t ∂(volume : Measure ℝ).restrict (Ioc 0 (T : ℝ)), clockPath ω t.toNNReal ≠ 0 := by
  have hm : MeasurableSet {z : ℝ × SampleSpace | sigma z ≠ 0} :=
    (measurableSet_eq_fun sigma_measurable measurable_const).compl
  have h := sigma_nonzero T
  change ∀ᵐ z ∂PredictableRealL2.horizonMeasure T gaussianProduct, sigma z ≠ 0 at h
  rw [PredictableRealL2.horizonMeasure_eq_product] at h
  exact (Measure.ae_ae_comm hm).mp ((Measure.ae_prod_iff_ae_ae hm).mp h)

theorem zero_time_all : ∀ᵐ ω ∂gaussianProduct,
    ∀ T : ℝ≥0, ∀ᵐ t ∂(volume : Measure ℝ).restrict (Ioc 0 (T : ℝ)),
      clockPath ω t.toNNReal ≠ 0 := by
  have h : ∀ᵐ ω ∂gaussianProduct, ∀ n : ℕ,
      ∀ᵐ t ∂(volume : Measure ℝ).restrict (Ioc 0 (n : ℝ)), clockPath ω t.toNNReal ≠ 0 :=
    ae_all_iff.mpr (fun n => zero_time_ae (n : ℝ≥0))
  filter_upwards [h] with ω hω
  intro S
  obtain ⟨n,hn⟩ := exists_nat_gt (S : ℝ)
  have hs : Ioc 0 (S : ℝ) ⊆ Ioc 0 (n : ℝ) := fun _ ht => ⟨ht.1, ht.2.trans hn.le⟩
  exact ae_restrict_of_ae_restrict_of_subset hs (hω n)

theorem zero_set_measure : ∀ᵐ ω ∂gaussianProduct, ∀ T : ℝ≥0,
    ((volume : Measure ℝ).restrict (Ioc 0 (T : ℝ)))
      {t | clockPath ω t.toNNReal = 0} = 0 := by
  filter_upwards [zero_time_all] with ω hω
  intro T
  simpa only [ae_iff, not_not] using hω T

end OperatorDerivativeRewrite.Foundation.BrownianZeroOccupation
