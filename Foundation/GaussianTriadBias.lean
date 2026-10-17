import Foundation.GaussianTriadHermite

/-! Positive probability densities change signed transfer while preserving every even law. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianTriadBias
open GaussianTriadPhase
set_option backward.isDefEq.respectTransparency false

def bias (c : ℝ) : ℝ := c/(1+|c|)

theorem bias_continuous : Continuous bias := by
  exact continuous_id.div (continuous_const.add continuous_abs)
    (fun c => by positivity)

theorem bias_odd (c : ℝ) : bias (-c) = -bias c := by
  simp only [bias, abs_neg]
  ring

theorem bias_norm_le (c : ℝ) : ‖bias c‖ ≤ 1 := by
  rw [bias, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0:ℝ)<1+|c|)]
  exact (div_le_one (by positivity)).mpr (by linarith)

theorem bias_mul_integrable {f : ℝ → ℝ} (hf : Integrable f γ) :
    Integrable (fun c => bias c*f c) γ :=
  hf.bdd_mul bias_continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall bias_norm_le)

theorem bias_integrable : Integrable bias γ := by
  simpa using bias_mul_integrable (integrable_const (1:ℝ))

theorem odd_mean_zero (f : ℝ → ℝ) (ho : ∀ c, f (-c) = -f c) :
    (∫ c, f c ∂γ)=0 := by
  have he := gaussian_neg_preserving.integral_comp measurableEmbedding_neg f
  simp_rw [ho] at he
  rw [integral_neg] at he
  linarith

theorem bias_mean_zero : (∫ c, bias c ∂γ)=0 := odd_mean_zero bias bias_odd

def density (ε c : ℝ) : ℝ := 1+ε*bias c

theorem density_continuous (ε : ℝ) : Continuous (density ε) := by
  exact continuous_const.add (continuous_const.mul bias_continuous)

theorem density_nonneg {ε : ℝ} (hε : |ε|≤1) (c : ℝ) : 0≤density ε c := by
  have hb := bias_norm_le c
  rw [Real.norm_eq_abs] at hb
  have hm : |ε*bias c|≤1 := by
    rw [abs_mul]
    nlinarith [abs_nonneg ε, abs_nonneg (bias c)]
  have hl := (abs_le.mp hm).1
  unfold density
  linarith

theorem density_integrable (ε : ℝ) : Integrable (density ε) γ :=
  (integrable_const 1).add (bias_integrable.const_mul ε)

theorem density_integral (ε : ℝ) : (∫ c, density ε c ∂γ)=1 := by
  change (∫ c, 1+ε*bias c ∂γ)=1
  rw [integral_add (integrable_const 1) (bias_integrable.const_mul ε),
    integral_const_mul, bias_mean_zero]
  simp

def law (ε : ℝ) : Measure ℝ := GaussianCore.weightedMeasure γ (density ε)

theorem law_probability {ε : ℝ} (hε : |ε|≤1) : IsProbabilityMeasure (law ε) := by
  constructor
  rw [law, GaussianCore.weightedMeasure, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (density_integrable ε)
    (Filter.Eventually.of_forall (density_nonneg hε)), density_integral]
  norm_num

theorem density_mul_integrable (ε : ℝ) {f : ℝ → ℝ} (hf : Integrable f γ) :
    Integrable (fun c => density ε c*f c) γ := by
  convert hf.add ((bias_mul_integrable hf).const_mul ε) using 1
  ext c
  change (1+ε*bias c)*f c=f c+ε*(bias c*f c)
  ring

theorem law_integrable {ε : ℝ} (hε : |ε|≤1) {f : ℝ → ℝ} (hf : Integrable f γ) :
    Integrable f (law ε) :=
  (GaussianCore.weighted_integrable_iff (density_continuous ε).measurable
    (density_nonneg hε)).mpr (density_mul_integrable ε hf)

theorem law_integral {ε : ℝ} (hε : |ε|≤1) {f : ℝ → ℝ} (hf : Integrable f γ) :
    (∫ c, f c ∂law ε) = (∫ c, f c ∂γ)+ε*(∫ c, bias c*f c ∂γ) := by
  rw [law, GaussianCore.weighted_integral (density_continuous ε).measurable
    (density_nonneg hε)]
  have he : (fun c => density ε c*f c)=(fun c => f c+ε*(bias c*f c)) := by
    ext c; unfold density; ring
  rw [he, integral_add hf ((bias_mul_integrable hf).const_mul ε), integral_const_mul]

theorem even_integral_preserved {ε : ℝ} (hε : |ε|≤1) {f : ℝ → ℝ}
    (hf : Integrable f γ) (he : ∀ c, f (-c)=f c) :
    (∫ c, f c ∂law ε) = ∫ c, f c ∂γ := by
  rw [law_integral hε hf, odd_mean_zero (fun c => bias c*f c)
    (by intro c; rw [bias_odd, he]; ring)]
  ring

/-- Equality of full pushforward laws, not just equality of one expectation. -/
theorem even_map_preserved {β : Type*} [MeasurableSpace β]
    {ε : ℝ} (hε : |ε|≤1) {f : ℝ → β}
    (hf : Measurable f) (he : ∀ c, f (-c)=f c) :
    (law ε).map f = γ.map f := by
  classical
  have := law_probability hε
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hf hs, Measure.map_apply hf hs]
  have hi : Integrable ((f ⁻¹' s).indicator (fun _ => (1:ℝ))) γ :=
    (integrable_const 1).indicator (hf hs)
  have hp : ∀ c, (f ⁻¹' s).indicator (fun _ => (1:ℝ)) (-c) =
      (f ⁻¹' s).indicator (fun _ => (1:ℝ)) c := by
    intro c
    change (if f (-c)∈s then (1:ℝ) else 0) = if f c∈s then 1 else 0
    rw [he]
  have h := even_integral_preserved hε hi hp
  change (∫ c, (f ⁻¹' s).indicator (1 : ℝ → ℝ) c ∂law ε) =
    ∫ c, (f ⁻¹' s).indicator (1 : ℝ → ℝ) c ∂γ at h
  rw [integral_indicator_one (hf hs), integral_indicator_one (hf hs)] at h
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp h

theorem bias_rate_nonpos (c : ℝ) : bias c*phaseRate c≤0 := by
  have he : bias c*phaseRate c=(phaseRate c*c)/(1+|c|) := by unfold bias; ring
  rw [he]
  exact div_nonpos_of_nonpos_of_nonneg (linear_product_nonpos c) (by positivity)

theorem negative_bias_rate_support :
    γ (Function.support (fun c => -(bias c*phaseRate c)))=1 := by
  have hs : Function.support (fun c => -(bias c*phaseRate c))=
      Function.support (fun c => -(phaseRate c*c)) := by
    ext c
    simp [Function.mem_support, bias,
      phaseRate_zero_iff, (by positivity : (1+|c|:ℝ)≠0)]
  rw [hs, negative_linear_support_measure]

theorem bias_rate_mean_negative : (∫ c, bias c*phaseRate c ∂γ)<0 := by
  have hp : 0<∫ c, -(bias c*phaseRate c) ∂γ := by
    apply (integral_pos_iff_support_of_nonneg
      (fun c => neg_nonneg.mpr (bias_rate_nonpos c))
      (bias_mul_integrable phaseRate_integrable).neg).mpr
    rw [negative_bias_rate_support]
    norm_num
  rw [integral_neg] at hp
  linarith

theorem law_rate_mean {ε : ℝ} (hε : |ε|≤1) :
    (∫ c, phaseRate c ∂law ε)=ε*(∫ c, bias c*phaseRate c ∂γ) := by
  rw [law_integral hε phaseRate_integrable, phaseRate_mean_zero, zero_add]

theorem law_rate_mean_negative {ε : ℝ} (hε : |ε|≤1) (hp : 0<ε) :
    (∫ c, phaseRate c ∂law ε)<0 := by
  rw [law_rate_mean hε]
  exact mul_neg_of_pos_of_neg hp bias_rate_mean_negative

theorem law_rate_mean_positive {ε : ℝ} (hε : |ε|≤1) (hn : ε<0) :
    0<(∫ c, phaseRate c ∂law ε) := by
  rw [law_rate_mean hε]
  exact mul_pos_of_neg_of_neg hn bias_rate_mean_negative

def sourceEnergy (c : ℝ) : ℝ := SectorTransferSymmetry.energy SectorTriadSign.modes
  (ParameterizedSectorTriad.polarization 2 1 c)

def sourceConcentration (c : ℝ) : ℝ := SectorTransferSymmetry.concentration
  SectorTriadSign.modes AngularTriadPartition.sector (ParameterizedSectorTriad.polarization 2 1 c)

theorem sourceEnergy_even (c : ℝ) : sourceEnergy (-c)=sourceEnergy c := by
  simp only [sourceEnergy, ParameterizedSectorTriad.energy_exact,
    ParameterizedSectorTriad.energyValue]
  ring

theorem sourceConcentration_even (c : ℝ) : sourceConcentration (-c)=sourceConcentration c := by
  simp only [sourceConcentration, ParameterizedSectorTriad.concentration_exact,
    ParameterizedSectorTriad.energyValue, ParameterizedSectorTriad.fourthValue]
  ring

theorem sourceEnergy_measurable : Measurable sourceEnergy := by
  have he : sourceEnergy=(fun c : ℝ => 2*(2:ℝ)^2+2*(1:ℝ)^2+8*c^2) := by
    ext c
    exact ParameterizedSectorTriad.energy_exact 2 1 c
  rw [he]
  fun_prop

theorem sourceConcentration_measurable : Measurable sourceConcentration := by
  have he : sourceConcentration=(fun c : ℝ =>
      2*((2:ℝ)^4+(1:ℝ)^4+16*c^4)/(2*(2:ℝ)^2+2*(1:ℝ)^2+8*c^2)^2) := by
    ext c
    exact ParameterizedSectorTriad.concentration_exact 2 1 c
  rw [he]
  fun_prop

theorem energy_law_preserved {ε : ℝ} (hε : |ε|≤1) :
    (law ε).map sourceEnergy = γ.map sourceEnergy := by
  exact even_map_preserved hε sourceEnergy_measurable sourceEnergy_even

theorem concentration_law_preserved {ε : ℝ} (hε : |ε|≤1) :
    (law ε).map sourceConcentration = γ.map sourceConcentration := by
  exact even_map_preserved hε sourceConcentration_measurable sourceConcentration_even

def sourceStatistics (c : ℝ) : ℝ × ℝ := (sourceEnergy c, sourceConcentration c)

theorem joint_statistics_preserved {ε : ℝ} (hε : |ε|≤1) :
    (law ε).map sourceStatistics = γ.map sourceStatistics := by
  exact even_map_preserved hε
    (sourceEnergy_measurable.prodMk sourceConcentration_measurable)
    (fun c => by simp [sourceStatistics, sourceEnergy_even, sourceConcentration_even])

theorem opposite_means_same_statistics :
    IsProbabilityMeasure (law 1) ∧ IsProbabilityMeasure (law (-1)) ∧
      (law 1).map sourceStatistics = (law (-1)).map sourceStatistics ∧
      (∫ c, phaseRate c ∂law 1)<0 ∧ 0<(∫ c, phaseRate c ∂law (-1)) := by
  have hp : |(1:ℝ)|≤1 := by norm_num
  have hn : |(-1:ℝ)|≤1 := by norm_num
  exact ⟨law_probability hp, law_probability hn,
    (joint_statistics_preserved hp).trans (joint_statistics_preserved hn).symm,
    law_rate_mean_negative hp (by norm_num), law_rate_mean_positive hn (by norm_num)⟩

theorem opposite_laws_distinct : law 1 ≠ law (-1) := by
  intro he
  have hn := opposite_means_same_statistics.2.2.2.1
  have hp := opposite_means_same_statistics.2.2.2.2
  rw [he] at hn
  linarith

end OperatorDerivativeRewrite.Foundation.GaussianTriadBias
