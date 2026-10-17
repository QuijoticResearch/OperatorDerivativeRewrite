import Foundation.GaussianTriadBias
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! Signed transfer is invisible in conditional mean to every even observation. -/
noncomputable section
open MeasureTheory Set
namespace OperatorDerivativeRewrite.Foundation.GaussianTriadConditional
open GaussianTriadPhase GaussianTriadBias
set_option backward.isDefEq.respectTransparency false

abbrev observedSpace {β : Type*} [MeasurableSpace β] (f : ℝ → β) : MeasurableSpace ℝ :=
  MeasurableSpace.comap f inferInstance

theorem observedSpace_le {β : Type*} [MeasurableSpace β] {f : ℝ → β}
    (hf : Measurable f) : observedSpace f ≤ (inferInstance : MeasurableSpace ℝ) := hf.comap_le

theorem observed_set_symmetric {β : Type*} [MeasurableSpace β] {f : ℝ → β}
    (he : ∀ c, f (-c)=f c) {s : Set ℝ} (hs : MeasurableSet[observedSpace f] s)
    (c : ℝ) : -c∈s ↔ c∈s := by
  obtain ⟨t, ht, rfl⟩ := hs
  simp only [Set.mem_preimage, he]

theorem rate_integral_symmetric_set {s : Set ℝ} (hs : MeasurableSet s)
    (he : ∀ c : ℝ, -c∈s ↔ c∈s) : (∫ c in s, phaseRate c ∂γ)=0 := by
  classical
  rw [← integral_indicator hs]
  apply odd_mean_zero
  intro c
  by_cases hc : c∈s
  · have hn := (he c).mpr hc
    simp only [Set.indicator_of_mem hc, Set.indicator_of_mem hn, phaseRate_odd]
  · have hn : -c∉s := by simpa only [he] using hc
    simp only [Set.indicator_of_notMem hc, Set.indicator_of_notMem hn, neg_zero]

theorem even_observation_condexp_zero {β : Type*} [MeasurableSpace β]
    {f : ℝ → β} (hf : Measurable f) (he : ∀ c, f (-c)=f c) :
    γ[phaseRate | observedSpace f] =ᵐ[γ] (0 : ℝ → ℝ) := by
  have hm := observedSpace_le hf
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm phaseRate_integrable
  · intro s hs hfin
    exact integrable_zero ℝ ℝ (γ.restrict s)
  · intro s hs hfin
    simp only [Pi.zero_apply, integral_zero]
    rw [rate_integral_symmetric_set (hm s hs) (observed_set_symmetric he hs)]
  · exact stronglyMeasurable_const.aestronglyMeasurable

theorem absolute_observation_condexp_zero :
    γ[phaseRate | observedSpace (fun c : ℝ => |c|)] =ᵐ[γ] (0 : ℝ → ℝ) :=
  even_observation_condexp_zero continuous_abs.measurable abs_neg

theorem energy_observation_condexp_zero :
    γ[phaseRate | observedSpace sourceEnergy] =ᵐ[γ] (0 : ℝ → ℝ) :=
  even_observation_condexp_zero sourceEnergy_measurable sourceEnergy_even

theorem concentration_observation_condexp_zero :
    γ[phaseRate | observedSpace sourceConcentration] =ᵐ[γ] (0 : ℝ → ℝ) :=
  even_observation_condexp_zero sourceConcentration_measurable sourceConcentration_even

theorem statistics_observation_condexp_zero :
    γ[phaseRate | observedSpace sourceStatistics] =ᵐ[γ] (0 : ℝ → ℝ) :=
  even_observation_condexp_zero
    (sourceEnergy_measurable.prodMk sourceConcentration_measurable)
    (fun c => by simp [sourceStatistics, sourceEnergy_even, sourceConcentration_even])

theorem even_observation_error_identity {β : Type*} [MeasurableSpace β]
    {f : ℝ → β} (hf : Measurable f) (he : ∀ c, f (-c)=f c) :
    (∫ c, (phaseRate c-(γ[phaseRate | observedSpace f]) c)^2 ∂γ)=
      ∫ c, (phaseRate c)^2 ∂γ := by
  apply integral_congr_ae
  filter_upwards [even_observation_condexp_zero hf he] with c hc
  simp only [Pi.zero_apply] at hc
  rw [hc, sub_zero]

theorem statistics_observation_error_pos :
    0<∫ c, (phaseRate c-(γ[phaseRate | observedSpace sourceStatistics]) c)^2 ∂γ := by
  rw [even_observation_error_identity (f := sourceStatistics)
    (sourceEnergy_measurable.prodMk sourceConcentration_measurable)
    (fun c => by simp [sourceStatistics, sourceEnergy_even, sourceConcentration_even])]
  exact phaseRate_second_moment_pos

theorem even_predictor_product_integrable {g : ℝ → ℝ} (hg : MemLp g 2 γ) :
    Integrable (fun c => phaseRate c*g c) γ := by
  have hm : MemLp (fun c => phaseRate c*g c) 1 γ := mul_memLp phaseRate_memLp hg
  exact hm.integrable (by norm_num)

theorem even_predictor_orthogonal {g : ℝ → ℝ} (he : ∀ c, g (-c)=g c) :
    (∫ c, phaseRate c*g c ∂γ)=0 :=
  odd_mean_zero _ (fun c => by rw [phaseRate_odd, he]; ring)

theorem even_predictor_error_integrable {g : ℝ → ℝ} (hg : MemLp g 2 γ) :
    Integrable (fun c => (phaseRate c-g c)^2) γ :=
  (phaseRate_memLp.sub hg).integrable_sq

theorem even_predictor_error_identity {g : ℝ → ℝ} (hg : MemLp g 2 γ)
    (he : ∀ c, g (-c)=g c) :
    (∫ c, (phaseRate c-g c)^2 ∂γ)=
      (∫ c, (phaseRate c)^2 ∂γ)+(∫ c, (g c)^2 ∂γ) := by
  have hp := even_predictor_product_integrable hg
  have hsum : Integrable (fun c => (phaseRate c)^2+(g c)^2) γ :=
    phaseRate_sq_integrable.add hg.integrable_sq
  have hid : (fun c => (phaseRate c-g c)^2)=
      (fun c => (phaseRate c)^2+(g c)^2-2*(phaseRate c*g c)) := by
    ext c; ring
  rw [hid, integral_sub hsum (hp.const_mul 2),
    integral_add phaseRate_sq_integrable hg.integrable_sq, integral_const_mul,
    even_predictor_orthogonal he]
  ring

theorem even_predictor_error_lower {g : ℝ → ℝ} (hg : MemLp g 2 γ)
    (he : ∀ c, g (-c)=g c) :
    (∫ c, (phaseRate c)^2 ∂γ)≤∫ c, (phaseRate c-g c)^2 ∂γ := by
  rw [even_predictor_error_identity hg he]
  exact le_add_of_nonneg_right (integral_nonneg (fun c => sq_nonneg (g c)))

theorem even_predictor_error_positive {g : ℝ → ℝ} (hg : MemLp g 2 γ)
    (he : ∀ c, g (-c)=g c) : 0<∫ c, (phaseRate c-g c)^2 ∂γ :=
  lt_of_lt_of_le phaseRate_second_moment_pos (even_predictor_error_lower hg he)

theorem sourceEnergy_formula (c : ℝ) : sourceEnergy c=10+8*c^2 := by
  rw [sourceEnergy, ParameterizedSectorTriad.energy_exact]
  norm_num [ParameterizedSectorTriad.energyValue]

def energyRateSquare (e : ℝ) : ℝ :=
  2304*((e-10)/8)/(30*((e-10)/8)^2-5*((e-10)/8)+247/8)^2

theorem rate_square_from_energy (c : ℝ) : (phaseRate c)^2=energyRateSquare (sourceEnergy c) := by
  rw [phaseRate_formula, sourceEnergy_formula]
  unfold energyRateSquare
  rw [show (10+8*c^2-10)/8=c^2 by ring,
    show 30*(c^2)^2-5*c^2+247/8=phaseDen c by unfold phaseDen; ring, div_pow]
  ring

theorem energyRateSquare_measurable : Measurable energyRateSquare := by
  unfold energyRateSquare
  fun_prop

theorem rate_square_observation_measurable :
    @Measurable ℝ ℝ (observedSpace sourceEnergy) inferInstance (fun c => (phaseRate c)^2) := by
  have hs : @Measurable ℝ ℝ (observedSpace sourceEnergy) inferInstance sourceEnergy :=
    Measurable.of_comap_le le_rfl
  have hh : (fun c => (phaseRate c)^2)=energyRateSquare ∘ sourceEnergy :=
    funext rate_square_from_energy
  rw [hh]
  exact energyRateSquare_measurable.comp hs

theorem rate_square_condexp_energy :
    γ[(fun c => (phaseRate c)^2) | observedSpace sourceEnergy]=fun c => (phaseRate c)^2 := by
  exact condExp_of_stronglyMeasurable (observedSpace_le sourceEnergy_measurable)
    rate_square_observation_measurable.stronglyMeasurable phaseRate_sq_integrable

theorem statistics_predictor_error_identity (φ : ℝ × ℝ → ℝ)
    (hφ : MemLp (fun c => φ (sourceStatistics c)) 2 γ) :
    (∫ c, (phaseRate c-φ (sourceStatistics c))^2 ∂γ)=
      (∫ c, (phaseRate c)^2 ∂γ)+(∫ c, (φ (sourceStatistics c))^2 ∂γ) := by
  apply even_predictor_error_identity hφ
  intro c
  simp only [sourceStatistics, sourceEnergy_even, sourceConcentration_even]

theorem energy_conditional_variance :
    (fun c => (γ[(fun z => (phaseRate z)^2) | observedSpace sourceEnergy]) c -
      ((γ[phaseRate | observedSpace sourceEnergy]) c)^2) =ᵐ[γ]
      (fun c => (phaseRate c)^2) := by
  rw [rate_square_condexp_energy]
  filter_upwards [energy_observation_condexp_zero] with c hc
  simp only [Pi.zero_apply] at hc
  rw [hc]
  simp

theorem energy_conditional_variance_pos_ae :
    ∀ᵐ c ∂γ, 0 < (γ[(fun z => (phaseRate z)^2) | observedSpace sourceEnergy]) c -
      ((γ[phaseRate | observedSpace sourceEnergy]) c)^2 := by
  have : NullSingletonClass γ :=
    ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num)
  filter_upwards [energy_conditional_variance, γ.ae_ne 0] with c hc hn
  rw [hc]
  exact sq_pos_of_ne_zero ((phaseRate_zero_iff c).not.mpr hn)

theorem even_observation_error_integrable {β : Type*} [MeasurableSpace β]
    {f : ℝ → β} (hf : Measurable f) (he : ∀ c, f (-c)=f c) :
    Integrable (fun c => (phaseRate c-(γ[phaseRate | observedSpace f]) c)^2) γ := by
  apply phaseRate_sq_integrable.congr
  filter_upwards [even_observation_condexp_zero hf he] with c hc
  simp only [Pi.zero_apply] at hc
  rw [hc, sub_zero]

end OperatorDerivativeRewrite.Foundation.GaussianTriadConditional
