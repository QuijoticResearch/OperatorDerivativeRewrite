import Foundation.FourCubeHaarLaplaceDensity

/-! Actual Haar cutoff partition and full finite-cell normalization asymptotics. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace OperatorDerivativeRewrite.Foundation.FourCubeHaarPartitionAsymptotic
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereChart
open FourCubePinnedHaar FourCubePinnedCoercivity FourCubePinnedConcentration
open FourCubeHemisphereCoercivity FourCubeHaarProductCoordinates
open FourCubeHaarQuadraticLimit FourCubeHaarLaplaceDensity
open OneSidedPinnedInterior (Free)

theorem integral_joint_density (f : PinnedState → ℝ) (hf : Measurable f) :
    (∫ U in jointHemisphere,f U ∂pinnedHaar)=
      ∫ Y : Field,productDensity Y*f (chartField Y) := by
  calc
    _ = ∫ Y : Field,f (chartField Y) ∂productCoordinateLaw := by
      rw [← chartField_map]
      exact integral_map chartField_measurable.aemeasurable hf.aestronglyMeasurable
    _ = _ := by
      rw [productCoordinateLaw_density]
      have hh := integral_withDensity_eq_integral_toReal_smul
        productDensity_measurable.ennreal_ofReal
        (ae_of_all (volume : Measure Field) (fun _ => ENNReal.ofReal_lt_top))
        (fun Y : Field => f (chartField Y))
      simpa only [ENNReal.toReal_ofReal (productDensity_nonneg _),smul_eq_mul] using hh

theorem cutoff_subset_jointHemisphere : localStateDomain ⊆ jointHemisphere := by
  intro U hU e _
  exact (hU e).1

theorem cutoff_chart_iff (Y : Field) : chartField Y∈localStateDomain ↔ Y∈coordinateCutoff := by
  change Y∈chartField ⁻¹' localStateDomain ↔ Y∈coordinateCutoff
  rw [cutoff_preimage]
  rfl

theorem integral_actual_cutoff (f : PinnedState → ℝ) (hf : Measurable f) :
    (∫ U in localStateDomain,f U ∂pinnedHaar)=
      ∫ Y in coordinateCutoff,productDensity Y*f (chartField Y) := by
  classical
  have hh := integral_joint_density (localStateDomain.indicator f)
    (hf.indicator localStateDomain_measurable)
  rw [setIntegral_indicator localStateDomain_measurable,
    Set.inter_eq_right.mpr cutoff_subset_jointHemisphere] at hh
  rw [← integral_indicator coordinateCutoff_measurable]
  exact hh.trans (integral_congr_ae (ae_of_all _ (fun Y => by
    by_cases h : Y∈coordinateCutoff
    · simp only [Set.indicator_of_mem h,Set.indicator_of_mem ((cutoff_chart_iff Y).mpr h)]
    · simp only [Set.indicator_of_notMem h,
        Set.indicator_of_notMem (mt (cutoff_chart_iff Y).mp h),mul_zero])))

def localPartition (t : ℝ) : ℝ :=
  ∫ U in localStateDomain,Real.exp (-pinnedAction U/t^2) ∂pinnedHaar

theorem localPartition_rescale (t : ℝ) (ht : t ≠ 0) :
    localPartition t=|t|^93*(∫ Y : Field,scaledDensity t Y) := by
  classical
  have hm : Measurable (fun U : PinnedState => Real.exp (-pinnedAction U/t^2)) :=
    (pinnedAction_measurable.neg.div_const (t^2)).exp
  rw [localPartition,integral_actual_cutoff _ hm,← integral_indicator coordinateCutoff_measurable]
  let F : Field → ℝ := coordinateCutoff.indicator
    (fun Z => productDensity Z*Real.exp (-pinnedAction (chartField Z)/t^2))
  change (∫ Y : Field,F Y)=_
  rw [integral_rescale F t ht]
  congr 1

theorem localPartition_asymptotic :
    Tendsto (fun t : ℝ => localPartition t/|t|^93) (𝓝[≠] 0)
      (𝓝 (∫ Y : Field,gaussianDensity Y)) := by
  apply scaledDensity_integral_tendsto.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [localPartition_rescale t ht]
  have hn : |t|^93 ≠ 0 := pow_ne_zero _ (abs_ne_zero.mpr ht)
  exact (mul_div_cancel_left₀ _ hn).symm

theorem inverse_square_tendsto : Tendsto (fun t : ℝ => 1/t^2) (𝓝[≠] 0) atTop := by
  have hs : Tendsto (fun t : ℝ => t^2) (𝓝[≠] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [id_eq,zero_pow (by norm_num : 2 ≠ 0)] using
        ((tendsto_id.pow 2).mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact sq_pos_of_ne_zero ht
  simpa only [one_div,Function.comp_def] using tendsto_inv_nhdsGT_zero.comp hs

theorem actual_cutoff_probability (t : ℝ) :
    (gibbs (1/t^2)).real localStateDomain=localPartition t/normalizer (1/t^2) := by
  classical
  have hh := gibbs_integral (1/t^2) (localStateDomain.indicator (fun _ => (1 : ℝ)))
  have hi : (∫ U,localStateDomain.indicator (fun _ => (1 : ℝ)) U ∂gibbs (1/t^2))=
      (gibbs (1/t^2)).real localStateDomain := by
    convert! integral_indicator_one (μ := gibbs (1/t^2)) localStateDomain_measurable using 1
  rw [hi] at hh
  rw [hh]
  congr 1
  unfold localPartition
  rw [← integral_indicator localStateDomain_measurable]
  apply integral_congr_ae
  filter_upwards with U
  by_cases h : U∈localStateDomain
  · simp only [Set.indicator_of_mem h,one_mul]
    congr 1
    ring
  · simp only [Set.indicator_of_notMem h,zero_mul]

theorem actual_normalizer_asymptotic :
    Tendsto (fun t : ℝ => normalizer (1/t^2)/|t|^93) (𝓝[≠] 0)
      (𝓝 (∫ Y : Field,gaussianDensity Y)) := by
  have hp := gibbs_cutoff_tendsto_one.comp inverse_square_tendsto
  have hh := localPartition_asymptotic.div hp (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin,hp.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)] with t ht hprob
  have hn : normalizer (1/t^2) ≠ 0 := (normalizer_positive _).ne'
  have hc := actual_cutoff_probability t
  have hl : localPartition t ≠ 0 := by
    intro hz
    rw [hz,zero_div] at hc
    exact hprob hc
  change (localPartition t/|t|^93)/((gibbs (1/t^2)).real localStateDomain)=
    normalizer (1/t^2)/|t|^93
  rw [hc]
  field_simp [hl,hn,abs_ne_zero.mpr ht]

end OperatorDerivativeRewrite.Foundation.FourCubeHaarPartitionAsymptotic
