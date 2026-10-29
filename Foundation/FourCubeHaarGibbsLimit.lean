import Foundation.FourCubeHaarPartitionAsymptotic

/-! Actual finite-cell Gibbs convergence for bounded measurable rescaled chart tests. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeHaarGibbsLimit
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereChart
open FourCubePinnedHaar FourCubePinnedCoercivity FourCubePinnedConcentration
open FourCubeHemisphereCoercivity FourCubeHaarProductCoordinates FourCubeHaarQuadraticLimit
open FourCubeHaarLaplaceDensity FourCubeHaarPartitionAsymptotic

def scaledTest (t : ℝ) (f : Field → ℝ) (U : PinnedState) : ℝ :=
  f (t⁻¹ • coordinateField U)

def gaussianAverage (f : Field → ℝ) : ℝ :=
  (∫ Y : Field,f Y*gaussianDensity Y)/(∫ Y : Field,gaussianDensity Y)

theorem coordinateField_chartField (Y : Field) : coordinateField (chartField Y)=Y := by
  funext e
  exact coordinates_chart (Y e)

theorem scaledTest_measurable (t : ℝ) (f : Field → ℝ) (hf : Measurable f) :
    Measurable (scaledTest t f) :=
  hf.comp ((continuous_const_smul t⁻¹).measurable.comp coordinateField_measurable)

theorem gibbs_cutoff_integral (β : ℝ) (g : PinnedState → ℝ) :
    (∫ U in localStateDomain,g U ∂gibbs β)=
      (∫ U in localStateDomain,g U*Real.exp (-β*pinnedAction U) ∂pinnedHaar)/normalizer β := by
  classical
  rw [← integral_indicator localStateDomain_measurable]
  rw [gibbs_integral]
  congr 1
  rw [← integral_indicator localStateDomain_measurable]
  apply integral_congr_ae
  filter_upwards with U
  by_cases h : U∈localStateDomain
  · simp only [Set.indicator_of_mem h]
  · simp only [Set.indicator_of_notMem h,zero_mul]

theorem cutoff_numerator_rescale (t : ℝ) (ht : t ≠ 0) (f : Field → ℝ) (hf : Measurable f) :
    (∫ U in localStateDomain,scaledTest t f U*Real.exp (-pinnedAction U/t^2) ∂pinnedHaar)=
      |t|^93*(∫ Y : Field,f Y*scaledDensity t Y) := by
  classical
  have hm : Measurable (fun U : PinnedState => scaledTest t f U*Real.exp (-pinnedAction U/t^2)) :=
    (scaledTest_measurable t f hf).mul ((pinnedAction_measurable.neg.div_const _).exp)
  rw [integral_actual_cutoff _ hm,← integral_indicator coordinateCutoff_measurable]
  let F : Field → ℝ := coordinateCutoff.indicator (fun Z =>
    productDensity Z*(scaledTest t f (chartField Z)*Real.exp (-pinnedAction (chartField Z)/t^2)))
  change (∫ Y : Field,F Y)=_
  rw [integral_rescale F t ht]
  congr 1
  apply integral_congr_ae
  filter_upwards with Y
  have hs : t⁻¹ • (t • Y)=Y := by rw [smul_smul,inv_mul_cancel₀ ht,one_smul]
  by_cases h : Y∈scaledCutoff t
  · have h' : t • Y∈coordinateCutoff := h
    simp only [F,Set.indicator_of_mem h',scaledDensity,Set.indicator_of_mem h,
      scaledTest,coordinateField_chartField,hs,ray]
    ring
  · have h' : t • Y∉coordinateCutoff := h
    simp only [F,Set.indicator_of_notMem h',scaledDensity,Set.indicator_of_notMem h,mul_zero]

theorem actual_cutoff_test (t : ℝ) (ht : t ≠ 0) (f : Field → ℝ) (hf : Measurable f) :
    (∫ U in localStateDomain,scaledTest t f U ∂gibbs (1/t^2))=
      (|t|^93*(∫ Y : Field,f Y*scaledDensity t Y))/normalizer (1/t^2) := by
  rw [gibbs_cutoff_integral]
  congr 1
  have he (U : PinnedState) : Real.exp (-(1/t^2)*pinnedAction U)=Real.exp (-pinnedAction U/t^2) := by
    congr 1
    ring
  simp_rw [he]
  exact cutoff_numerator_rescale t ht f hf

theorem actual_cutoff_test_tendsto (f : Field → ℝ) (hf : Measurable f) (M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ Y,|f Y| ≤ M) :
    Tendsto (fun t : ℝ => ∫ U in localStateDomain,scaledTest t f U ∂gibbs (1/t^2))
      (𝓝[≠] 0) (𝓝 (gaussianAverage f)) := by
  have hh := (bounded_test_integral_tendsto f hf M hM hbound).div
    actual_normalizer_asymptotic gaussianDensity_integral_positive.ne'
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [actual_cutoff_test t ht f hf]
  have hn : normalizer (1/t^2) ≠ 0 := (normalizer_positive _).ne'
  change (∫ Y : Field,f Y*scaledDensity t Y)/(normalizer (1/t^2)/|t|^93)=
    (|t|^93*(∫ Y : Field,f Y*scaledDensity t Y))/normalizer (1/t^2)
  field_simp [hn,abs_ne_zero.mpr ht] <;> ring

theorem outside_test_bound (t : ℝ) (f : Field → ℝ) (M : ℝ) (hbound : ∀ Y,|f Y| ≤ M) :
    |∫ U in localStateDomainᶜ,scaledTest t f U ∂gibbs (1/t^2)| ≤
      M*(gibbs (1/t^2)).real localStateDomainᶜ := by
  have hh := norm_setIntegral_le_of_norm_le_const (μ := gibbs (1/t^2))
    (s := localStateDomainᶜ) (f := scaledTest t f) (measure_lt_top _ _)
    (fun U _ => by simpa only [Real.norm_eq_abs,scaledTest] using hbound (t⁻¹ • coordinateField U))
  simpa only [Real.norm_eq_abs] using hh

theorem outside_test_tendsto_zero (f : Field → ℝ) (M : ℝ) (hbound : ∀ Y,|f Y| ≤ M) :
    Tendsto (fun t : ℝ => ∫ U in localStateDomainᶜ,scaledTest t f U ∂gibbs (1/t^2))
      (𝓝[≠] 0) (𝓝 0) := by
  have hp := gibbs_outside_cutoff_tendsto_zero.comp inverse_square_tendsto
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun t => norm_nonneg _) (fun t => ?_)
    (show Tendsto (fun t : ℝ => M*(gibbs (1/t^2)).real localStateDomainᶜ) (𝓝[≠] 0) (𝓝 0) from
      by simpa only [mul_zero,Function.comp_def] using tendsto_const_nhds.mul hp)
  simpa only [Real.norm_eq_abs] using outside_test_bound t f M hbound

theorem actual_gibbs_bounded_test_limit (f : Field → ℝ) (hf : Measurable f) (M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ Y,|f Y| ≤ M) :
    Tendsto (fun t : ℝ => ∫ U,scaledTest t f U ∂gibbs (1/t^2))
      (𝓝[≠] 0) (𝓝 (gaussianAverage f)) := by
  have hh := (actual_cutoff_test_tendsto f hf M hM hbound).add (outside_test_tendsto_zero f M hbound)
  simp only [add_zero] at hh
  apply hh.congr'
  exact Filter.Eventually.of_forall (fun t => by
    have hi : Integrable (scaledTest t f) (gibbs (1/t^2)) := by
      apply (integrable_const M).mono' (scaledTest_measurable t f hf).aestronglyMeasurable
      exact ae_of_all _ (fun U => by simpa only [Real.norm_eq_abs,scaledTest] using hbound (t⁻¹ • coordinateField U))
    exact integral_add_compl localStateDomain_measurable hi)


def limitingDensity (Y : Field) : ℝ :=
  gaussianDensity Y/(∫ Z : Field,gaussianDensity Z)

def limitingLaw : Measure Field := (volume : Measure Field).withDensity
  (fun Y => ENNReal.ofReal (limitingDensity Y))

theorem limitingDensity_nonneg (Y : Field) : 0 ≤ limitingDensity Y :=
  div_nonneg (mul_nonneg (productDensity_nonneg 0) (Real.exp_pos _).le)
    gaussianDensity_integral_positive.le

theorem limitingDensity_integrable : Integrable limitingDensity :=
  gaussianDensity_integrable.div_const _

theorem limitingDensity_integral : (∫ Y : Field,limitingDensity Y)=1 := by
  unfold limitingDensity
  rw [integral_div]
  exact div_self gaussianDensity_integral_positive.ne'

instance limitingLaw_probability : IsProbabilityMeasure limitingLaw := by
  constructor
  rw [limitingLaw,withDensity_apply _ MeasurableSet.univ]
  have hh := ofReal_integral_eq_lintegral_ofReal limitingDensity_integrable
    (ae_of_all _ limitingDensity_nonneg)
  simpa only [Measure.restrict_univ,limitingDensity_integral,ENNReal.ofReal_one] using hh.symm

theorem limitingLaw_integral (f : Field → ℝ) :
    (∫ Y,f Y ∂limitingLaw)=gaussianAverage f := by
  have hh := integral_withDensity_eq_integral_toReal_smul₀
    limitingDensity_integrable.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (ae_of_all (volume : Measure Field) (fun _ => ENNReal.ofReal_lt_top)) f
  change (∫ Y,f Y ∂(volume : Measure Field).withDensity (fun Y => ENNReal.ofReal (limitingDensity Y)))=_
  rw [hh]
  simp only [ENNReal.toReal_ofReal (limitingDensity_nonneg _),smul_eq_mul]
  unfold limitingDensity gaussianAverage
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards with Y
  ring

theorem actual_gibbs_limit_law (f : Field → ℝ) (hf : Measurable f) (M : ℝ)
    (hM : 0 ≤ M) (hbound : ∀ Y,|f Y| ≤ M) :
    Tendsto (fun t : ℝ => ∫ U,scaledTest t f U ∂gibbs (1/t^2)) (𝓝[≠] 0)
      (𝓝 (∫ Y,f Y ∂limitingLaw)) := by
  rw [limitingLaw_integral]
  exact actual_gibbs_bounded_test_limit f hf M hM hbound

end OperatorDerivativeRewrite.Foundation.FourCubeHaarGibbsLimit
