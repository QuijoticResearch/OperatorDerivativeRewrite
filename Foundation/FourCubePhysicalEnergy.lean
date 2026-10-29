import Foundation.FourCubeHaarPartitionAsymptotic

/-! Exact physical-action exponential moments and their actual fixed-cell scaling limit. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubePhysicalEnergy
open FourCubePinnedHaar FourCubePinnedCoercivity FourCubePinnedConcentration
open FourCubeHemisphereCoercivity FourCubeHaarLaplaceDensity FourCubeHaarPartitionAsymptotic

def scaledEnergy (t : ℝ) (U : PinnedState) : ℝ := pinnedAction U/t^2

def energyMGF (t s : ℝ) : ℝ :=
  ∫ U,Real.exp (s*scaledEnergy t U) ∂gibbs (1/t^2)

def limitMGF (s : ℝ) : ℝ := (Real.sqrt (1-s))⁻¹^93

theorem scaledEnergy_measurable (t : ℝ) : Measurable (scaledEnergy t) :=
  pinnedAction_measurable.div_const _

theorem scaledEnergy_nonneg (t : ℝ) (U : PinnedState) : 0 ≤ scaledEnergy t U :=
  div_nonneg (pinnedAction_nonneg U) (sq_nonneg t)

theorem scaledEnergy_integrable (t : ℝ) : Integrable (scaledEnergy t) (gibbs (1/t^2)) := by
  have hi : Integrable energySource (gibbs (1/t^2)) :=
    (integrable_const (1 : ℝ)).mono' energySource_measurable.aestronglyMeasurable
      (ae_of_all _ (fun U => by simpa only [Real.norm_eq_abs] using energySource_bound U))
  convert! hi.const_mul (-144/t^2) using 1
  funext U
  unfold scaledEnergy energySource
  ring

theorem exponential_integrable (t s : ℝ) :
    Integrable (fun U => Real.exp (s*scaledEnergy t U)) (gibbs (1/t^2)) := by
  have hh := BoundedExponentialTiltResponse.exponential_integrable (gibbs (1/t^2))
    energySource energySource_measurable energySource_bound (-144*s/t^2)
  convert! hh using 1
  funext U
  congr 1
  unfold scaledEnergy energySource
  ring

theorem energyMGF_partition (t s : ℝ) :
    energyMGF t s=normalizer ((1-s)/t^2)/normalizer (1/t^2) := by
  rw [energyMGF,gibbs_integral,normalizer_integral ((1-s)/t^2)]
  congr 1
  apply integral_congr_ae
  filter_upwards with U
  rw [← Real.exp_add]
  congr 1
  unfold scaledEnergy
  ring

theorem partition_ratio_tendsto (c : ℝ) (hc : 0 < c) :
    Tendsto (fun t : ℝ => normalizer (c/t^2)/normalizer (1/t^2))
      (𝓝[≠] 0) (𝓝 ((Real.sqrt c)⁻¹^93)) := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hmap : Tendsto (fun t : ℝ => t/Real.sqrt c) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using ((tendsto_id.div_const (Real.sqrt c)).mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact div_ne_zero ht hs.ne'
  have hh := (actual_normalizer_asymptotic.comp hmap).div actual_normalizer_asymptotic
    gaussianDensity_integral_positive.ne'
  simp only [div_self gaussianDensity_integral_positive.ne'] at hh
  have hlim := hh.mul_const ((Real.sqrt c)⁻¹^93)
  simp only [one_mul] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hz := (normalizer_positive (1/t^2)).ne'
  have he : 1/(t/Real.sqrt c)^2=c/t^2 := by
    rw [div_pow,Real.sq_sqrt hc.le]
    field_simp
  simp only [Pi.div_apply,Function.comp_apply] at *
  rw [he,abs_div,abs_of_pos hs,div_pow]
  field_simp [hz,ht,hs.ne',abs_ne_zero.mpr ht]

theorem energyMGF_tendsto (s : ℝ) (hs : s < 1) :
    Tendsto (fun t : ℝ => energyMGF t s) (𝓝[≠] 0) (𝓝 (limitMGF s)) := by
  simpa only [energyMGF_partition,limitMGF] using partition_ratio_tendsto (1-s) (by linarith)

theorem energyMGF_zero (t : ℝ) : energyMGF t 0=1 := by
  simp [energyMGF]

def energyMean (t : ℝ) : ℝ := ∫ U,scaledEnergy t U ∂gibbs (1/t^2)

theorem energyMean_sandwich (t a : ℝ) (ha : 0 < a) :
    (1-energyMGF t (-a))/a ≤ energyMean t ∧
      energyMean t ≤ (energyMGF t a-1)/a := by
  have hl := integral_mono (integrable_const (1 : ℝ) |>.sub (exponential_integrable t (-a)))
    ((scaledEnergy_integrable t).const_mul a) (fun U => by
      change 1-Real.exp (-a*scaledEnergy t U) ≤ a*scaledEnergy t U
      have hh := Real.add_one_le_exp (-a*scaledEnergy t U)
      linarith)
  have hu := integral_mono ((scaledEnergy_integrable t).const_mul a)
    ((exponential_integrable t a).sub (integrable_const (1 : ℝ))) (fun U => by
      change a*scaledEnergy t U ≤ Real.exp (a*scaledEnergy t U)-1
      have hh := Real.add_one_le_exp (a*scaledEnergy t U)
      linarith)
  simp only [Pi.sub_apply] at hl hu
  rw [integral_sub (integrable_const _) (exponential_integrable t (-a)),integral_const_mul] at hl
  rw [integral_sub (exponential_integrable t a) (integrable_const _),integral_const_mul] at hu
  simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,
    smul_eq_mul,one_mul] at hl hu
  change 1-energyMGF t (-a) ≤ a*energyMean t at hl
  change a*energyMean t ≤ energyMGF t a-1 at hu
  exact ⟨(div_le_iff₀ ha).2 (by nlinarith), (le_div_iff₀ ha).2 (by nlinarith)⟩

theorem limitMGF_zero : limitMGF 0=1 := by norm_num [limitMGF]

theorem limitMGF_hasDerivAt_zero : HasDerivAt limitMGF (93/2 : ℝ) 0 := by
  have hh := ((((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id 0)).sqrt
    (by norm_num : (1 : ℝ)-0 ≠ 0)).inv (by norm_num : Real.sqrt (1-(0 : ℝ)) ≠ 0)).pow 93
  convert! hh using 1; norm_num [limitMGF]

theorem upper_slope_tendsto : Tendsto (fun a : ℝ => (limitMGF a-1)/a)
    (𝓝[>] 0) (𝓝 (93/2 : ℝ)) := by
  simpa only [zero_add,limitMGF_zero,smul_eq_mul,div_eq_mul_inv,mul_comm]
    using limitMGF_hasDerivAt_zero.tendsto_slope_zero_right

theorem lower_slope_tendsto : Tendsto (fun a : ℝ => (1-limitMGF (-a))/a)
    (𝓝[>] 0) (𝓝 (93/2 : ℝ)) := by
  have hh : HasDerivAt (fun a : ℝ => limitMGF (-a)) (-(93/2 : ℝ)) 0 := by
    have hd : HasDerivAt (fun a : ℝ => -a) (-1) 0 := by
      convert! (hasDerivAt_id (0 : ℝ)).neg using 1
    have ho : HasDerivAt limitMGF (93/2 : ℝ) (-(0 : ℝ)) := by
      simpa only [neg_zero] using limitMGF_hasDerivAt_zero
    convert! ho.comp (0 : ℝ) hd using 1; simp
  have hh' := ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hh).tendsto_slope_zero_right
  simpa only [zero_sub,zero_add,neg_zero,limitMGF_zero,sub_self,sub_zero,smul_eq_mul,
    div_eq_mul_inv,mul_comm,neg_mul,neg_neg,Pi.sub_apply] using hh'

/-- This is proved from exponential secants, not by differentiating an asymptotic. -/
theorem actual_energyMean_tendsto :
    Tendsto energyMean (𝓝[≠] 0) (𝓝 (93/2 : ℝ)) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    have hh := lower_slope_tendsto.eventually (eventually_gt_nhds hb)
    obtain ⟨a,ha,hb'⟩ :=
      ((show ∀ᶠ a : ℝ in 𝓝[>] 0,0<a from self_mem_nhdsWithin).and hh).exists
    have ht :=
      ((tendsto_const_nhds.sub (energyMGF_tendsto (-a) (by linarith))).div_const a).eventually
      (eventually_gt_nhds hb')
    filter_upwards [ht] with t ht
    exact ht.trans_le (energyMean_sandwich t a ha).1
  · intro b hb
    have hh := upper_slope_tendsto.eventually (eventually_lt_nhds hb)
    have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0,a < 1 :=
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    obtain ⟨a,ha,ha',hb'⟩ :=
      ((show ∀ᶠ a : ℝ in 𝓝[>] 0,0<a from self_mem_nhdsWithin).and (hsmall.and hh)).exists
    have ht := (((energyMGF_tendsto a ha').sub tendsto_const_nhds).div_const a).eventually
      (eventually_lt_nhds hb')
    filter_upwards [ht] with t ht
    exact (energyMean_sandwich t a ha).2.trans_lt ht

/-- The physical coupling parametrization, for the original actual Gibbs measure. -/
theorem actual_beta_mean_tendsto :
    Tendsto (fun β : ℝ => β*(∫ U,pinnedAction U ∂gibbs β)) atTop (𝓝 (93/2 : ℝ)) := by
  have hc := (tendsto_inv_atTop_nhdsGT_zero.comp Real.tendsto_sqrt_atTop).mono_right
    (nhdsGT_le_nhdsNE (0 : ℝ))
  apply (actual_energyMean_tendsto.comp hc).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
  have he : 1/((Real.sqrt β)⁻¹)^2=β := by
    rw [inv_pow,Real.sq_sqrt hβ.le,one_div,inv_inv]
  change (∫ U,scaledEnergy ((Real.sqrt β)⁻¹) U ∂gibbs (1/((Real.sqrt β)⁻¹)^2))=_
  rw [he,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with U
  change pinnedAction U/((Real.sqrt β)⁻¹)^2=β*pinnedAction U
  rw [div_eq_mul_inv,← one_div,he,mul_comm]

def energyTail (t R : ℝ) : Set PinnedState := {U | R ≤ scaledEnergy t U}

theorem energyTail_measurable (t R : ℝ) : MeasurableSet (energyTail t R) :=
  measurableSet_le measurable_const (scaledEnergy_measurable t)

/-- A full-measure-space bound: there is no chart-cutoff or outside remainder. -/
theorem energyTail_bound (t a R : ℝ) (ha : 0 ≤ a) :
    (gibbs (1/t^2)).real (energyTail t R) ≤ Real.exp (-a*R)*energyMGF t a := by
  have hm := energyTail_measurable t R
  have hi := exponential_integrable t a
  have hc : Integrable (fun _ : PinnedState => Real.exp (a*R)) (gibbs (1/t^2)) :=
    integrable_const _
  have hh := setIntegral_mono_on hc.integrableOn hi.integrableOn hm
    (fun U hU => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hU ha))
  have hu := setIntegral_le_integral (s := energyTail t R) hi
    (ae_of_all _ (fun U => (Real.exp_pos _).le))
  have hl : Real.exp (a*R)*(gibbs (1/t^2)).real (energyTail t R) ≤ energyMGF t a := by
    convert! hh.trans hu using 1
    simp only [setIntegral_const,smul_eq_mul,mul_comm]
  have hp := Real.exp_pos (a*R)
  have he : Real.exp (-a*R)*Real.exp (a*R)=1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hh' := mul_le_mul_of_nonneg_left hl (Real.exp_pos (-a*R)).le
  simpa only [← mul_assoc,he,one_mul] using hh'

theorem eventual_energyTail_bound (a : ℝ) (ha : 0 ≤ a) (ha' : a < 1) :
    ∀ᶠ t : ℝ in 𝓝[≠] 0,∀ R : ℝ,
      (gibbs (1/t^2)).real (energyTail t R) ≤ Real.exp (-a*R)*(limitMGF a+1) := by
  have hh := (energyMGF_tendsto a ha').eventually
    (eventually_lt_nhds (show limitMGF a < limitMGF a+1 by linarith))
  filter_upwards [hh] with t ht R
  exact (energyTail_bound t a R ha).trans
    (mul_le_mul_of_nonneg_left ht.le (Real.exp_pos _).le)

theorem normalizer_tendsto_zero :
    Tendsto (fun t : ℝ => normalizer (1/t^2)) (𝓝[≠] 0) (𝓝 0) := by
  have hp : Tendsto (fun t : ℝ => |t|^93) (𝓝[≠] 0) (𝓝 0) := by
    simpa using ((tendsto_id.abs.pow 93).mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0))
  have hh := actual_normalizer_asymptotic.mul hp
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact div_mul_cancel₀ _ (pow_ne_zero _ (abs_ne_zero.mpr ht))

theorem normalizer_zero : normalizer 0=1 := by simp [normalizer_integral]

/-- The limiting exponential-moment domain is sharp, though every finite-scale moment exists. -/
theorem energyMGF_boundary_tendsto :
    Tendsto (fun t : ℝ => energyMGF t 1) (𝓝[≠] 0) atTop := by
  have hp : Tendsto (fun t : ℝ => normalizer (1/t^2)) (𝓝[≠] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨normalizer_tendsto_zero,Filter.Eventually.of_forall (fun t => normalizer_positive _)⟩
  simpa only [energyMGF_partition,sub_self,zero_div,normalizer_zero,one_div,Function.comp_def]
    using tendsto_inv_nhdsGT_zero.comp hp

theorem energyMGF_mono (t : ℝ) : Monotone (energyMGF t) := by
  intro a b hab
  exact integral_mono (exponential_integrable t a) (exponential_integrable t b)
    (fun U => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hab (scaledEnergy_nonneg t U)))

theorem energyMGF_supercritical_tendsto (s : ℝ) (hs : 1 ≤ s) :
    Tendsto (fun t : ℝ => energyMGF t s) (𝓝[≠] 0) atTop :=
  tendsto_atTop_mono (fun t => energyMGF_mono t hs) energyMGF_boundary_tendsto

end OperatorDerivativeRewrite.Foundation.FourCubePhysicalEnergy
