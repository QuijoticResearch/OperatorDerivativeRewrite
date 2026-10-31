import Foundation.PeriodicQuarticKernelBlock
import Foundation.PeriodicTransferVariation
/-! Actual stationary L2 probes on gauge-saturated quartic regions.
The ground cancellation, Haar volume, constrained-root kernel block and
principal-value upper bound give a fixed positive Rayleigh lower bound along
a proved unbounded-coupling family outside every fixed Gaussian flat-tube
budget. A bounded operator annihilating the selected probe has a fixed norm
error. This is not a centered quasimode, a physical gap or a continuum limit.
Every ground object and operator is the existing finite-lattice construction. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open OperatorDerivativeRewrite.Foundation
namespace OperatorDerivativeRewrite.Foundation.PeriodicQuarticNativeObstruction
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround PeriodicSlabL2
attribute [local irreducible] boundaryHaar kernel
variable {β : ℝ} (g : GroundData β)
private instance stationary_probability : IsProbabilityMeasure g.stationary := g.stationary_probability

def chi (B : Set State) : State → ℝ := B.indicator (fun _ => 1)
def trial (B : Set State) (U : State) : ℝ := chi B U/g.function U

theorem chi_abs (B : Set State) (U : State) : |chi B U|≤1 := by
  by_cases hu : U∈B <;> simp [chi,hu]

theorem trial_measurable (B : Set State) (hB : MeasurableSet B) : Measurable (trial g B) :=
  (measurable_const.indicator hB).div g.measurable

theorem trial_bound (B : Set State) (U : State) : |trial g B U|≤1/g.lower := by
  unfold trial
  rw [abs_div,abs_of_pos (g.function_pos U)]
  exact (div_le_div_of_nonneg_right (chi_abs B U) (g.function_pos U).le).trans
    (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ)≤1) g.lower_pos (g.bounds U).1)

theorem trial_memLp (B : Set State) (hB : MeasurableSet B) : MemLp (trial g B) 2 g.stationary :=
  MemLp.of_bound (trial_measurable g B hB).aestronglyMeasurable (1/g.lower)
    (ae_of_all _ (fun U => by simpa only [Real.norm_eq_abs] using trial_bound g B U))

theorem cancel_trial (B : Set State) (U : State) : g.function U*trial g B U=chi B U := by
  unfold trial
  field_simp [(g.function_pos U).ne']

theorem trial_square_integral (B : Set State) (hB : MeasurableSet B) :
    (∫ U,trial g B U^2 ∂g.stationary)=boundaryHaar.real B/g.normalizer := by
  rw [g.stationary_integral]
  have he : (fun U => g.function U^2*trial g B U^2)=chi B := by
    funext U
    calc
      _ = (g.function U*trial g B U)^2 := by ring
      _ = chi B U^2 := by rw [cancel_trial]
      _ = chi B U := by by_cases hu : U∈B <;> simp [chi,hu]
  rw [he]
  have hi : (∫ U,chi B U ∂boundaryHaar)=boundaryHaar.real B := integral_indicator_one hB
  rw [hi]

theorem trial_stationary_pairing (B : Set State) :
    (∫ U,trial g B U*(∫ V,trial g B V ∂g.transition U) ∂g.stationary)=
      pairing β (chi B) (chi B)/(g.value*g.normalizer) := by
  rw [g.stationary_pairing]
  have he : (fun U => g.function U*trial g B U)=chi B := funext (cancel_trial g B)
  rw [he]

theorem native_norm_square (B : Set State) (hB : MeasurableSet B) :
    ‖(trial_memLp g B hB).toLp (trial g B)‖^2=boundaryHaar.real B/g.normalizer := by
  rw [PeriodicTransferVariation.state_norm_square]
  exact trial_square_integral g B hB

theorem native_pairing (B : Set State) (hB : MeasurableSet B) :
    inner ℝ (operator g ((trial_memLp g B hB).toLp (trial g B)))
      ((trial_memLp g B hB).toLp (trial g B))=
        pairing β (chi B) (chi B)/(g.value*g.normalizer) := by
  let f := trial g B
  have hf := trial_measurable g B hB
  have hb := trial_bound g B
  have hm := trial_memLp g B hB
  have hp := transfer_memLp g f hf (1/g.lower) hb
  have he : inner ℝ (operator g (hm.toLp f)) (hm.toLp f)=
      ∫ U,f U*transfer g f U ∂g.stationary := by
    rw [operator_toLp g f hm hf (1/g.lower) hb,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hp,MemLp.coeFn_toLp hm] with U hP hF
    rw [hP,hF]
    rfl
  exact he.trans (trial_stationary_pairing g B)


attribute [local irreducible] pairing

theorem pairing_indicator_lower (β : ℝ) (B : Set State) (hB : MeasurableSet B) (k : ℝ)
    (hK : ∀ U∈B,∀ V∈B,k≤kernel β U V) :
    k*(boundaryHaar.real B)^2≤pairing β (chi B) (chi B) := by
  have hiK : Integrable (fun p : State × State => kernel β p.1 p.2) (boundaryHaar.prod boundaryHaar) := by
    apply Integrable.of_bound (kernel_joint_measurable β).aestronglyMeasurable (Real.exp (768*|β|))
    filter_upwards with p
    change ‖kernel β p.1 p.2‖≤Real.exp (768*|β|)
    rw [Real.norm_eq_abs,abs_of_pos (kernel_positive β p.1 p.2)]
    exact (kernel_bounds β p.1 p.2).2
  have he : (fun p : State × State => chi B p.1*(kernel β p.1 p.2*chi B p.2))=
      (B ×ˢ B).indicator (fun p : State × State => kernel β p.1 p.2) := by
    funext p
    by_cases hu : p.1∈B <;> by_cases hv : p.2∈B <;> simp [chi,hu,hv]
  have hi : Integrable (fun p : State × State => chi B p.1*(kernel β p.1 p.2*chi B p.2))
      (boundaryHaar.prod boundaryHaar) := by
    rw [he]
    exact hiK.indicator (hB.prod hB)
  have hpair : pairing β (chi B) (chi B)=
      ∫ p : State × State in B ×ˢ B,kernel β p.1 p.2 ∂boundaryHaar.prod boundaryHaar := by
    unfold pairing
    simp_rw [← integral_const_mul]
    rw [← integral_prod _ hi,he,integral_indicator (hB.prod hB)]
  have hl := setIntegral_mono_on (integrable_const k).integrableOn hiK.integrableOn
    (hB.prod hB) (fun p hp => hK p.1 hp.1 p.2 hp.2)
  have hmass : (boundaryHaar.prod boundaryHaar).real (B ×ˢ B)=(boundaryHaar.real B)^2 := by
    change ((boundaryHaar.prod boundaryHaar) (B ×ˢ B)).toReal=_
    rw [Measure.prod_prod,ENNReal.toReal_mul,pow_two]
    rfl
  rw [setIntegral_const,smul_eq_mul,hmass,← hpair] at hl
  simpa only [mul_comm] using hl

theorem native_block_form (B : Set State) (hB : MeasurableSet B) (k : ℝ)
    (hK : ∀ U∈B,∀ V∈B,k≤kernel β U V) :
    (k*boundaryHaar.real B/g.value)*‖(trial_memLp g B hB).toLp (trial g B)‖^2≤
      inner ℝ (operator g ((trial_memLp g B hB).toLp (trial g B)))
        ((trial_memLp g B hB).toLp (trial g B)) := by
  rw [native_norm_square g B hB,native_pairing g B hB]
  have h := div_le_div_of_nonneg_right (pairing_indicator_lower β B hB k hK)
    (mul_pos g.value_pos g.normalizer_pos).le
  have he : (k*boundaryHaar.real B/g.value)*(boundaryHaar.real B/g.normalizer)=
      k*(boundaryHaar.real B)^2/(g.value*g.normalizer) := by
    field_simp [g.value_pos.ne',g.normalizer_pos.ne']
  rw [he]
  exact h


open QuaternionSU2Representation PeriodicSlabGauge PeriodicGaugeSaturatedGround SU2TwoAxisStabilizerHaar
open PeriodicQuarticGaugeOverlap PeriodicQuarticKernelBlock FourCubePinnedCoercivity
attribute [local irreducible] gaugeAction

def packetIndicator (t r : ℝ) : State → ℝ := chi (packet (PeriodicQuarticCurvature.field t) r)
def packetAverage (t r : ℝ) (U : State) : ℝ := ∫ a,packetIndicator t r (gaugeAction a U) ∂gaugeHaar
def packetRegion (t r : ℝ) : Set State := {U | 0<packetAverage t r U}
def overlapCoefficient (t r : ℝ) : ℝ :=
  law.real (nearStabilizer (4*t) (8*r))*(law.real (SU2HaarSmallCap.cap (8*r)))^63
def blockCoefficient (β t r : ℝ) : ℝ :=
  law.real (SU2HaarSmallCap.cap (r/(5*|Real.sin t|)))*(law.real (SU2HaarSmallCap.cap (r/3)))^63*
    Real.exp (-β*(256*Real.sin t^4+5472*r^2))

theorem packetIndicator_measurable (t r : ℝ) : Measurable (packetIndicator t r) :=
  measurable_const.indicator (packet_measurable _ _)

theorem packetIndicator_bounds (t r : ℝ) (U : State) : 0≤packetIndicator t r U ∧ packetIndicator t r U≤1 := by
  by_cases hu : U∈packet (PeriodicQuarticCurvature.field t) r <;> simp [packetIndicator,chi,hu]

theorem packetAverage_measurable (t r : ℝ) : Measurable (packetAverage t r) := by
  have hm : StronglyMeasurable (Function.uncurry (fun U : State => fun a : Gauge => packetIndicator t r (gaugeAction a U))) :=
    ((packetIndicator_measurable t r).comp action_joint_measurable).stronglyMeasurable
  exact hm.integral_prod_right.measurable

theorem packetIndicator_action_integrable (t r : ℝ) (U : State) :
    Integrable (fun a => packetIndicator t r (gaugeAction a U)) gaugeHaar := by
  have hc : Measurable (fun a : Gauge => (U,a)) := measurable_const.prodMk measurable_id
  have hm : Measurable (fun a : Gauge => packetIndicator t r (gaugeAction a U)) :=
    (packetIndicator_measurable t r).comp (action_joint_measurable.comp hc)
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  filter_upwards with a
  rw [Real.norm_eq_abs,abs_of_nonneg (packetIndicator_bounds t r _).1]
  exact (packetIndicator_bounds t r _).2

theorem packetAverage_bounds (t r : ℝ) (U : State) : 0≤packetAverage t r U ∧ packetAverage t r U≤1 := by
  constructor
  · exact integral_nonneg (fun a => (packetIndicator_bounds t r _).1)
  · have h := integral_mono (packetIndicator_action_integrable t r U) (integrable_const (1 : ℝ))
      (fun a => (packetIndicator_bounds t r _).2)
    simpa only [packetAverage,integral_const,probReal_univ,one_smul] using h

theorem packetAverage_invariant (t r : ℝ) (a : Gauge) (U : State) :
    packetAverage t r (gaugeAction a U)=packetAverage t r U := by
  unfold packetAverage
  simp_rw [action_comp]
  exact (gauge_right_preserving a).integral_comp (MeasurableEquiv.mulRight a).measurableEmbedding
    (fun b : Gauge => packetIndicator t r (gaugeAction b U))

theorem packetAverage_overlap_upper (t r : ℝ) (hr : 0≤r) (U : State)
    (hU : U∈packet (PeriodicQuarticCurvature.field t) r) : packetAverage t r U≤overlapCoefficient t r := by
  have hset := overlap_measurable (PeriodicQuarticCurvature.field t) U r
  have he : (fun a => packetIndicator t r (gaugeAction a U))=
      ({a : Gauge | gaugeAction a U∈packet (PeriodicQuarticCurvature.field t) r}).indicator (fun _ => (1 : ℝ)) := rfl
  unfold packetAverage
  rw [he]
  exact (integral_indicator_one hset).trans_le (quartic_overlap_mass_bound U t r hr hU)

theorem packetAverage_mass (t r : ℝ) :
    (∫ U,packetAverage t r U ∂boundaryHaar)=boundaryHaar.real (packet (PeriodicQuarticCurvature.field t) r) := by
  have hm : Measurable (fun p : State × Gauge => packetIndicator t r (gaugeAction p.2 p.1)) :=
    (packetIndicator_measurable t r).comp action_joint_measurable
  have hi : Integrable (fun p : State × Gauge => packetIndicator t r (gaugeAction p.2 p.1))
      (boundaryHaar.prod gaugeHaar) := Integrable.of_bound hm.aestronglyMeasurable 1
        (ae_of_all _ (fun p => by
          rw [Real.norm_eq_abs,abs_of_nonneg (packetIndicator_bounds t r _).1]
          exact (packetIndicator_bounds t r _).2))
  have hinner (a : Gauge) : (∫ U,packetIndicator t r (gaugeAction a U) ∂boundaryHaar)=
      boundaryHaar.real (packet (PeriodicQuarticCurvature.field t) r) := by
    have h := (action_boundary_preserving a).integral_comp (gaugeEquiv_embedding a) (packetIndicator t r)
    change (∫ U,packetIndicator t r (gaugeAction a U) ∂boundaryHaar)=∫ U,packetIndicator t r U ∂boundaryHaar at h
    exact h.trans (integral_indicator_one (packet_measurable _ _))
  unfold packetAverage
  rw [integral_integral_swap hi]
  simp_rw [hinner]
  simp only [integral_const,probReal_univ,one_smul]

theorem packetRegion_measurable (t r : ℝ) : MeasurableSet (packetRegion t r) :=
  measurableSet_lt measurable_const (packetAverage_measurable t r)

theorem packetRegion_witness (t r : ℝ) (U : State) (hU : U∈packetRegion t r) :
    ∃ a : Gauge,gaugeAction a U∈packet (PeriodicQuarticCurvature.field t) r := by
  by_contra hn
  push Not at hn
  have hz (a : Gauge) : packetIndicator t r (gaugeAction a U)=0 := by
    simp only [packetIndicator,chi,Set.indicator_of_notMem (hn a)]
  change 0<(∫ a,packetIndicator t r (gaugeAction a U) ∂gaugeHaar) at hU
  simp_rw [hz] at hU
  simp at hU

theorem packetRegion_average_bound (t r : ℝ) (hr : 0≤r) (U : State) :
    packetAverage t r U≤(packetRegion t r).indicator (fun _ => overlapCoefficient t r) U := by
  by_cases hU : U∈packetRegion t r
  · rw [Set.indicator_of_mem hU]
    obtain ⟨a,ha⟩ := packetRegion_witness t r U hU
    have h := packetAverage_overlap_upper t r hr (gaugeAction a U) ha
    rw [packetAverage_invariant] at h
    exact h
  · rw [Set.indicator_of_notMem hU]
    exact le_of_not_gt hU

theorem packetRegion_mass_bound (t r : ℝ) (hr : 0≤r) :
    boundaryHaar.real (packet (PeriodicQuarticCurvature.field t) r)≤
      boundaryHaar.real (packetRegion t r)*overlapCoefficient t r := by
  have h := integral_mono_of_nonneg (ae_of_all _ (fun U => (packetAverage_bounds t r U).1))
    ((integrable_const (μ := boundaryHaar) (overlapCoefficient t r)).indicator (packetRegion_measurable t r))
    (ae_of_all _ (packetRegion_average_bound t r hr))
  rw [packetAverage_mass,integral_indicator (packetRegion_measurable t r),setIntegral_const,smul_eq_mul] at h
  exact h

theorem packetRegion_mass_pos (t r : ℝ) (hr : 0<r) (h1 : r≤3) :
    0<boundaryHaar.real (packetRegion t r) := by
  have h := packetRegion_mass_bound t r hr.le
  have hp := packet_mass_pos (PeriodicQuarticCurvature.field t) r hr h1
  by_contra hn
  have hz : boundaryHaar.real (packetRegion t r)=0 := le_antisymm (le_of_not_gt hn) measureReal_nonneg
  rw [hz,zero_mul] at h
  linarith

theorem packetRegion_kernel_lower (β t r : ℝ) (hb : 0≤β) (hr : 0≤r) (ht : Real.sin t≠0)
    (U V : State) (hU : U∈packetRegion t r) (hV : V∈packetRegion t r) :
    blockCoefficient β t r≤kernel β U V := by
  obtain ⟨a,ha⟩ := packetRegion_witness t r U hU
  obtain ⟨b,hb'⟩ := packetRegion_witness t r V hV
  have h := kernel_packet_lower β t r hb hr ht (gaugeAction a U) (gaugeAction b V) ha hb'
  rw [kernel_left_invariant,kernel_right_invariant] at h
  exact h

theorem packetRegion_flat_separation (t r : ℝ) (hr : 0≤r) (hsmall : r≤|Real.sin (4*t)|/256)
    (U V : State) (hU : U∈packetRegion t r) (hV : spatialAction V=0) (b : Gauge) :
    Real.sin (4*t)^2≤256*temporalAction U V b := by
  obtain ⟨a,ha⟩ := packetRegion_witness t r U hU
  have h := packet_flat_separation (gaugeAction a U) V (a*b) t r hr ha hV hsmall
  have he : temporalAction (gaugeAction a U) V (a*b)=temporalAction U V b := by
    unfold temporalAction
    apply Finset.sum_congr rfl
    intro e _
    rw [temporal_left_word,halfTrace_conjugate]
  rw [he] at h
  exact h

def nativeTrial (t r : ℝ) : StateL2 g :=
  (trial_memLp g (packetRegion t r) (packetRegion_measurable t r)).toLp (trial g (packetRegion t r))

theorem nativeTrial_norm_square (t r : ℝ) :
    ‖nativeTrial g t r‖^2=boundaryHaar.real (packetRegion t r)/g.normalizer :=
  native_norm_square g _ (packetRegion_measurable t r)

theorem nativeTrial_norm_pos (t r : ℝ) (hr : 0<r) (h1 : r≤3) : 0<‖nativeTrial g t r‖ := by
  have h := nativeTrial_norm_square g t r
  have hp := div_pos (packetRegion_mass_pos t r hr h1) g.normalizer_pos
  nlinarith [norm_nonneg (nativeTrial g t r)]

theorem nativeTrial_outside (t r : ℝ) :
    ∀ᵐ U ∂g.stationary,U∉packetRegion t r → nativeTrial g t r U=0 := by
  filter_upwards [MemLp.coeFn_toLp (trial_memLp g (packetRegion t r) (packetRegion_measurable t r))] with U he hU
  change nativeTrial g t r U=trial g (packetRegion t r) U at he
  rw [he]
  simp [trial,chi,hU]

theorem nativeTrial_lower (t r : ℝ) (hb : 0≤β) (hr : 0≤r) (ht : Real.sin t≠0) :
    (blockCoefficient β t r*boundaryHaar.real (packetRegion t r)/g.value)*‖nativeTrial g t r‖^2≤
      inner ℝ (operator g (nativeTrial g t r)) (nativeTrial g t r) :=
  native_block_form g _ (packetRegion_measurable t r) (blockCoefficient β t r)
    (fun U hU V hV => packetRegion_kernel_lower β t r hb hr ht U V hU hV)


def relativeLower : ℝ := 1/(108*Real.pi^2)
def relativeUpper : ℝ := 512*(Real.exp 3*SU2HaarLaplaceUpper.upperConstant 1)
def rootUpper : ℝ := 512*SU2TwoAxisStabilizerHaar.upperConstant
def rawScaleConstant : ℝ :=
  ((SU2TwoAxisStabilizerHaar.lowerConstant*relativeLower^63*Real.exp (-5728))*relativeLower^192)/
    (rootUpper*relativeUpper^63)
def nativeConstant : ℝ := rawScaleConstant/PeriodicGroundHaarScale.upperConstant

attribute [local irreducible] blockCoefficient overlapCoefficient packetRegion

theorem relativeLower_pos : 0<relativeLower := by unfold relativeLower; positivity
theorem relativeUpper_pos : 0<relativeUpper := by
  unfold relativeUpper
  exact mul_pos (by norm_num) (mul_pos (Real.exp_pos _) (SU2HaarLaplaceUpper.upperConstant_pos 1 (by norm_num)))
theorem rootUpper_pos : 0<rootUpper := mul_pos (by norm_num) SU2TwoAxisStabilizerHaar.upperConstant_pos
theorem rawScaleConstant_pos : 0<rawScaleConstant := by
  unfold rawScaleConstant
  exact div_pos
    (mul_pos (mul_pos (mul_pos SU2TwoAxisStabilizerHaar.lowerConstant_pos (pow_pos relativeLower_pos _))
      (Real.exp_pos _)) (pow_pos relativeLower_pos _))
    (mul_pos rootUpper_pos (pow_pos relativeUpper_pos _))
theorem nativeConstant_pos : 0<nativeConstant :=
  div_pos rawScaleConstant_pos PeriodicGroundHaarScale.upperConstant_pos

theorem relative_cap_lower (r : ℝ) (hr : 0<r) (h1 : r≤1/8) :
    relativeLower*r^3≤law.real (SU2HaarSmallCap.cap (r/3)) := by
  have h := SU2HaarSmallCap.mass_lower (r/3) (by positivity) (by linarith)
  convert h using 1 <;> unfold relativeLower <;> ring

theorem relative_cap_upper (r : ℝ) (hr : 0<r) (h1 : r≤1/8) :
    law.real (SU2HaarSmallCap.cap (8*r))≤relativeUpper*r^3 := by
  have h := PeriodicGroundHaarScale.cap_polynomial_upper (8*r) (by positivity) (by linarith)
  convert h using 1 <;> unfold relativeUpper <;> ring

theorem root_cap_lower (t r : ℝ) (ht : 0<t) (hr : 0<r) (hnarrow : 256*r≤t)
    (hsin : t/4≤|Real.sin t|) :
    SU2TwoAxisStabilizerHaar.lowerConstant*(r/t)^3≤
      law.real (SU2HaarSmallCap.cap (r/(5*|Real.sin t|))) := by
  have hs : 0 < |Real.sin t| := by linarith
  have hu : |Real.sin t|≤t := (Real.abs_sin_le_abs (x := t)).trans_eq (abs_of_pos ht)
  have hd : 0<r/(5*|Real.sin t|) := div_pos hr (mul_pos (by norm_num) hs)
  have hd1 : r/(5*|Real.sin t|)≤1 := (div_le_one (by positivity)).mpr (by linarith)
  have hq : r/(5*t)≤r/(5*|Real.sin t|) :=
    div_le_div_of_nonneg_left hr.le (mul_pos (by norm_num) hs) (mul_le_mul_of_nonneg_left hu (by norm_num))
  have hp := pow_le_pow_left₀ (show 0≤r/(5*t) by positivity) hq 3
  have hh := (mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ)≤1/(4*Real.pi^2))).trans
    (SU2HaarSmallCap.mass_lower _ hd.le hd1)
  convert hh using 1 <;> unfold SU2TwoAxisStabilizerHaar.lowerConstant <;> ring

theorem root_stabilizer_upper (t r : ℝ) (ht : 0<t) (hr : 0<r) (hnarrow : 256*r≤t)
    (hsin4 : t≤|Real.sin (4*t)|) :
    law.real (nearStabilizer (4*t) (8*r))≤rootUpper*(r/t)^3 := by
  have hs : 0 < |Real.sin (4*t)| := ht.trans_le hsin4
  have hθ : Real.sin (4*t)≠0 := abs_pos.mp hs
  have h := (stabilizer_mass_cubic (4*t) (8*r) hθ (by positivity) (by linarith)).2
  have hq : 8*r/|Real.sin (4*t)|≤8*r/t :=
    div_le_div_of_nonneg_left (by positivity) ht hsin4
  have hp := pow_le_pow_left₀ (show 0≤8*r/|Real.sin (4*t)| by positivity) hq 3
  have hh := h.trans (mul_le_mul_of_nonneg_left hp SU2TwoAxisStabilizerHaar.upperConstant_pos.le)
  convert hh using 1 <;> unfold rootUpper <;> ring

theorem energy_uniform_bound (β t r : ℝ) (hb : 0≤β) (ht : 0<t)
    (hheat : β*r^2=1) (hpotential : β*t^4≤1) :
    β*(256*Real.sin t^4+5472*r^2)≤5728 := by
  have hs : |Real.sin t|≤t := (Real.abs_sin_le_abs (x := t)).trans_eq (abs_of_pos ht)
  have h2 := pow_le_pow_left₀ (abs_nonneg (Real.sin t)) hs 2
  rw [sq_abs] at h2
  have h4 := pow_le_pow_left₀ (sq_nonneg (Real.sin t)) h2 2
  have h4' : Real.sin t^4≤t^4 := by convert h4 using 1 <;> ring
  have hm := mul_le_mul_of_nonneg_left h4' hb
  nlinarith

theorem overlap_scaled_upper (t r : ℝ) (ht : 0<t) (hr : 0<r) (h1 : r≤1/8)
    (hnarrow : 256*r≤t) (hsin4 : t≤|Real.sin (4*t)|) :
    overlapCoefficient t r≤(rootUpper*relativeUpper^63)*((r/t)^3*r^189) := by
  have hroot := root_stabilizer_upper t r ht hr hnarrow hsin4
  have hrel := pow_le_pow_left₀ (show 0≤law.real (SU2HaarSmallCap.cap (8*r)) from measureReal_nonneg)
    (relative_cap_upper r hr h1) 63
  have hh := mul_le_mul hroot hrel (pow_nonneg measureReal_nonneg 63)
    (mul_nonneg rootUpper_pos.le (pow_nonneg (div_pos hr ht).le 3))
  unfold overlapCoefficient
  convert hh using 1 <;> ring

theorem packet_scaled_lower (t r : ℝ) (hr : 0<r) (h1 : r≤1/8) :
    relativeLower^192*r^576≤boundaryHaar.real (packet (PeriodicQuarticCurvature.field t) r) := by
  have hrel := pow_le_pow_left₀ (mul_nonneg relativeLower_pos.le (pow_nonneg hr.le 3))
    (relative_cap_lower r hr h1) 192
  have hh := hrel.trans (packet_mass_lower (PeriodicQuarticCurvature.field t) r hr.le)
  convert hh using 1 <;> ring

theorem block_scaled_lower (β t r : ℝ) (hb : 0≤β) (ht : 0<t) (hr : 0<r) (h1 : r≤1/8)
    (hnarrow : 256*r≤t) (hsin : t/4≤|Real.sin t|) (hheat : β*r^2=1) (hpotential : β*t^4≤1) :
    (SU2TwoAxisStabilizerHaar.lowerConstant*relativeLower^63*Real.exp (-5728))*((r/t)^3*r^189)≤
      blockCoefficient β t r := by
  have hroot := root_cap_lower t r ht hr hnarrow hsin
  have hrel := pow_le_pow_left₀ (mul_nonneg relativeLower_pos.le (pow_nonneg hr.le 3))
    (relative_cap_lower r hr h1) 63
  have hprod := mul_le_mul hroot hrel (pow_nonneg (mul_nonneg relativeLower_pos.le (pow_nonneg hr.le 3)) 63)
    (show 0≤law.real (SU2HaarSmallCap.cap (r/(5*|Real.sin t|))) from measureReal_nonneg)
  have he : Real.exp (-5728 : ℝ)≤Real.exp (-β*(256*Real.sin t^4+5472*r^2)) :=
    Real.exp_le_exp.mpr (by linarith [energy_uniform_bound β t r hb ht hheat hpotential])
  have hh := mul_le_mul hprod he (Real.exp_pos _).le
    (mul_nonneg measureReal_nonneg (pow_nonneg measureReal_nonneg 63))
  unfold blockCoefficient
  convert hh using 1 <;> ring


theorem region_scaled_product (β t r : ℝ) (hb : 0≤β) (ht : 0<t) (hr : 0<r) (h1 : r≤1/8)
    (hnarrow : 256*r≤t) (hsin : t/4≤|Real.sin t|) (hsin4 : t≤|Real.sin (4*t)|)
    (hheat : β*r^2=1) (hpotential : β*t^4≤1) :
    rawScaleConstant*r^576≤blockCoefficient β t r*boundaryHaar.real (packetRegion t r) := by
  let A : ℝ := SU2TwoAxisStabilizerHaar.lowerConstant*relativeLower^63*Real.exp (-5728)
  let D : ℝ := rootUpper*relativeUpper^63
  let Q : ℝ := (r/t)^3*r^189
  let M : ℝ := boundaryHaar.real (packetRegion t r)
  have ha : 0<A := mul_pos (mul_pos SU2TwoAxisStabilizerHaar.lowerConstant_pos (pow_pos relativeLower_pos _)) (Real.exp_pos _)
  have hd : 0<D := mul_pos rootUpper_pos (pow_pos relativeUpper_pos _)
  have hm : 0≤M := measureReal_nonneg
  have hmass : relativeLower^192*r^576≤M*(D*Q) :=
    (packet_scaled_lower t r hr h1).trans ((packetRegion_mass_bound t r hr.le).trans
      (mul_le_mul_of_nonneg_left (overlap_scaled_upper t r ht hr h1 hnarrow hsin4) hm))
  have hx := mul_le_mul_of_nonneg_left hmass (div_pos ha hd).le
  have heL : (A/D)*(relativeLower^192*r^576)=rawScaleConstant*r^576 := by
    unfold rawScaleConstant A D
    ring
  have heR : (A/D)*(M*(D*Q))=M*(A*Q) := by
    field_simp [hd.ne']
    <;> ring
  rw [heL,heR] at hx
  have hk : A*Q≤blockCoefficient β t r := block_scaled_lower β t r hb ht hr h1 hnarrow hsin hheat hpotential
  calc
    _ ≤ M*(A*Q) := hx
    _ ≤ M*blockCoefficient β t r := mul_le_mul_of_nonneg_left hk hm
    _ = _ := mul_comm _ _

theorem beta_radius_power (β r : ℝ) (hheat : β*r^2=1) : r^576=1/β^288 := by
  have hb : β≠0 := by intro hz; rw [hz,zero_mul] at hheat; norm_num at hheat
  have hp : (β*r^2)^288=1 := by rw [hheat,one_pow]
  have he : r^576*β^288=1 := by convert hp using 1 <;> ring
  exact (eq_div_iff (pow_ne_zero _ hb)).mpr he

theorem native_coefficient_lower (t r : ℝ) (hb : 0≤β) (ht : 0<t) (hr : 0<r) (h1 : r≤1/8)
    (hnarrow : 256*r≤t) (hsin : t/4≤|Real.sin t|) (hsin4 : t≤|Real.sin (4*t)|)
    (hheat : β*r^2=1) (hpotential : β*t^4≤1) :
    nativeConstant≤blockCoefficient β t r*boundaryHaar.real (packetRegion t r)/g.value := by
  have hr1 : r≤1 := by linarith
  have hrsq : r^2≤1 := by nlinarith
  have hb1 : 1≤β := by
    have hh := mul_le_mul_of_nonneg_left hrsq hb
    rw [hheat,mul_one] at hh
    exact hh
  have hbpos : 0<β := by linarith
  have hLam := PeriodicGroundHaarScale.eigenvalue_polynomial_upper β hb1 g
  have hp := region_scaled_product β t r hb ht hr h1 hnarrow hsin hsin4 hheat hpotential
  rw [beta_radius_power β r hheat] at hp
  apply (le_div_iff₀ g.value_pos).mpr
  have hh := mul_le_mul_of_nonneg_left hLam nativeConstant_pos.le
  have he : nativeConstant*(PeriodicGroundHaarScale.upperConstant/β^288)=rawScaleConstant*(1/β^288) := by
    unfold nativeConstant
    field_simp [PeriodicGroundHaarScale.upperConstant_pos.ne',hbpos.ne']
    <;> ring
  exact (hh.trans_eq he).trans hp

theorem uniform_native_lower (t r : ℝ) (hb : 0≤β) (ht : 0<t) (hr : 0<r) (h1 : r≤1/8)
    (hnarrow : 256*r≤t) (hsin : t/4≤|Real.sin t|) (hsin4 : t≤|Real.sin (4*t)|)
    (hheat : β*r^2=1) (hpotential : β*t^4≤1) :
    nativeConstant*‖nativeTrial g t r‖^2≤ inner ℝ (operator g (nativeTrial g t r)) (nativeTrial g t r) := by
  have hspos : 0 < |Real.sin t| := by linarith
  have hcoef := native_coefficient_lower g t r hb ht hr h1 hnarrow hsin hsin4 hheat hpotential
  exact (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)).trans
    (nativeTrial_lower g t r hb hr.le (abs_pos.mp hspos))

theorem trial_region_invariant (t r : ℝ) (a : Gauge) (U : State) :
    trial g (packetRegion t r) (gaugeAction a U)=trial g (packetRegion t r) U := by
  have hm : gaugeAction a U∈packetRegion t r ↔ U∈packetRegion t r := by
    unfold packetRegion
    change 0<packetAverage t r (gaugeAction a U) ↔ 0<packetAverage t r U
    rw [packetAverage_invariant]
  have he : chi (packetRegion t r) (gaugeAction a U)=chi (packetRegion t r) U := by
    by_cases hu : U∈packetRegion t r
    · simp [chi,hu,hm.mpr hu]
    · have hnot : gaugeAction a U∉packetRegion t r := fun h => hu (hm.mp h)
      simp [chi,hu,hnot]
  unfold trial
  rw [he,g.invariant]


open Filter
open scoped Topology
attribute [local irreducible] temporalAction

theorem eventual_sine_conditions : ∀ᶠ t : ℝ in 𝓝 0,
    t/4≤|Real.sin t| ∧ t≤|Real.sin (4*t)| := by
  have hd : Tendsto (fun t : ℝ => t/4) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0)).div_const 4
  filter_upwards [PeriodicFlatLocusQuarticObstruction.eventually_sine_floor,
    hd.eventually PeriodicFlatLocusQuarticObstruction.eventually_sine_floor] with t h4 h1
  rw [show (4*(t/4) : ℝ)=t by ring,← sq_abs (Real.sin t)] at h1
  rw [← sq_abs (Real.sin (4*t))] at h4
  exact ⟨le_of_sq_le_sq h1 (abs_nonneg _),le_of_sq_le_sq h4 (abs_nonneg _)⟩

theorem coupling_diverges : Tendsto (fun x : ℝ => 1/x^6) (𝓝[>] 0) atTop := by
  have h := (tendsto_pow_atTop (α := ℝ) (n := 6) (by decide)).comp
    (tendsto_inv_nhdsGT_zero : Tendsto (fun x : ℝ => x⁻¹) (𝓝[>] 0) atTop)
  simpa only [Function.comp_def,inv_pow,one_div] using h

theorem flat_distance_diverges : Tendsto (fun x : ℝ => 1/(256*x^2)) (𝓝[>] 0) atTop := by
  have h2 := (tendsto_pow_atTop (α := ℝ) (n := 2) (by decide)).comp
    (tendsto_inv_nhdsGT_zero : Tendsto (fun x : ℝ => x⁻¹) (𝓝[>] 0) atTop)
  have h := Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ)<1/256) h2
  have he : (fun x : ℝ => (1/256)*(x⁻¹)^2)=(fun x : ℝ => 1/(256*x^2)) := by
    funext x
    simp only [div_eq_mul_inv,mul_inv_rev,inv_pow,one_mul]
    ring
  change Tendsto (fun x : ℝ => (1/256)*(x⁻¹)^2) _ _ at h
  rw [he] at h
  exact h

theorem eventual_native_family : ∀ᶠ x : ℝ in 𝓝[>] 0,∀ q : GroundData (1/x^6),
    0<‖nativeTrial q (x^2) (x^3)‖ ∧
      nativeConstant*‖nativeTrial q (x^2) (x^3)‖^2≤ inner ℝ
        (operator q (nativeTrial q (x^2) (x^3))) (nativeTrial q (x^2) (x^3)) ∧
      (∀ᵐ U ∂q.stationary,U∉packetRegion (x^2) (x^3) → nativeTrial q (x^2) (x^3) U=0) ∧
      (∀ U∈packetRegion (x^2) (x^3),∀ V : State,spatialAction V=0 → ∀ a : Gauge,
        1/(256*x^2)≤(1/x^6)*temporalAction U V a) := by
  have htend : Tendsto (fun x : ℝ => x^2) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0)).pow 2
  have hs := htend.eventually eventual_sine_conditions
  have hsmall : ∀ᶠ x : ℝ in 𝓝 0,x<(1/256 : ℝ) := Iio_mem_nhds (by norm_num)
  filter_upwards [hs.filter_mono nhdsWithin_le_nhds,hsmall.filter_mono nhdsWithin_le_nhds,
    (self_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[>] 0,0<x)] with x hsin hxupper hx
  change 0<x at hx
  have hx1 : x≤1 := by linarith
  have hx2 : x^2≤1 := by simpa only [one_pow] using pow_le_pow_left₀ hx.le hx1 2
  have hnarrow : 256*x^3≤x^2 := by
    have h := mul_le_mul_of_nonneg_right (show (256 : ℝ)*x≤1 by linarith) (sq_nonneg x)
    convert h using 1 <;> ring
  have hr1 : x^3≤1/8 := by linarith
  have hb : 0≤1/x^6 := (one_div_pos.mpr (pow_pos hx 6)).le
  have ht : 0<x^2 := pow_pos hx 2
  have hr : 0<x^3 := pow_pos hx 3
  have hheat : (1/x^6)*(x^3)^2=1 := by
    field_simp [hx.ne']
    <;> ring
  have hpot : (1/x^6)*(x^2)^4≤1 := by
    have he : (1/x^6)*(x^2)^4=x^2 := by
      field_simp [hx.ne']
      <;> ring
    rw [he]
    exact hx2
  intro q
  refine ⟨nativeTrial_norm_pos q (x^2) (x^3) hr (by linarith),
    uniform_native_lower q (x^2) (x^3) hb ht hr hr1 hnarrow hsin.1 hsin.2 hheat hpot,
    nativeTrial_outside q (x^2) (x^3),?_⟩
  intro U hU V hV a
  have hgeom := packetRegion_flat_separation (x^2) (x^3) hr.le
    ((le_div_iff₀ (by norm_num : (0 : ℝ)<256)).mpr (by nlinarith [hsin.2])) U V hU hV a
  have hsq := pow_le_pow_left₀ (sq_nonneg x) hsin.2 2
  rw [sq_abs] at hsq
  have hs4 : x^4≤256*temporalAction U V a := by nlinarith
  have hcoef : (0 : ℝ)≤1/(256*x^6) :=
    (div_pos (by norm_num : (0 : ℝ)<1) (mul_pos (by norm_num : (0 : ℝ)<256) (pow_pos hx 6))).le
  have hm := mul_le_mul_of_nonneg_left hs4 hcoef
  have heL : (1/(256*x^6))*x^4=1/(256*x^2) := by
    field_simp [hx.ne']
    <;> ring
  have heR : (1/(256*x^6))*(256*temporalAction U V a)=(1/x^6)*temporalAction U V a := by
    field_simp [hx.ne']
    <;> ring
  rw [heL,heR] at hm
  exact hm

theorem arbitrarily_large_native (M : ℝ) : ∃ β : ℝ,1≤β ∧ M≤β ∧
    ∃ q : GroundData β,∃ F : StateL2 q,0<‖F‖ ∧
      nativeConstant*‖F‖^2≤ inner ℝ (operator q F) F ∧
      (∀ᵐ U ∂q.stationary,∀ V : State,spatialAction V=0 → ∀ a : Gauge,
        β*temporalAction U V a<M → F U=0) := by
  have hb := coupling_diverges.eventually (eventually_ge_atTop (max M 1))
  have he := flat_distance_diverges.eventually (eventually_ge_atTop M)
  obtain ⟨x,hfamily,hbeta,hescape⟩ := (eventual_native_family.and (hb.and he)).exists
  let q := ground (1/x^6)
  obtain ⟨hn,hq,ho,hsep⟩ := hfamily q
  refine ⟨1/x^6,(le_max_right M 1).trans hbeta,(le_max_left M 1).trans hbeta,q,
    nativeTrial q (x^2) (x^3),hn,hq,?_⟩
  filter_upwards [ho] with U hout
  intro V hV a hclose
  apply hout
  intro hreg
  have hlarge := hescape.trans (hsep U hreg V hV a)
  exact (not_lt_of_ge hlarge) hclose


theorem native_error_lower (F : StateL2 g) (hF : 0<‖F‖)
    (hform : nativeConstant*‖F‖^2≤ inner ℝ (operator g F) F)
    (Q : StateL2 g →L[ℝ] StateL2 g) (hQ : Q F=0) : nativeConstant≤‖operator g-Q‖ := by
  have he : (operator g-Q) F=operator g F := by
    rw [ContinuousLinearMap.sub_apply,hQ,sub_zero]
  have hc := real_inner_le_norm ((operator g-Q) F) F
  have ho := ContinuousLinearMap.le_opNorm (operator g-Q) F
  rw [he] at hc ho
  have h := hform.trans (hc.trans (mul_le_mul_of_nonneg_right ho (norm_nonneg F)))
  have hh : nativeConstant*‖F‖^2≤‖operator g-Q‖*‖F‖^2 := by convert h using 1 <;> ring
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hF)).mp hh

theorem arbitrarily_large_error_obstruction (M : ℝ) : ∃ β : ℝ,1≤β ∧ M≤β ∧
    ∃ q : GroundData β,∃ F : StateL2 q,0<‖F‖ ∧
      (∀ Q : StateL2 q →L[ℝ] StateL2 q,Q F=0 → nativeConstant≤‖operator q-Q‖) ∧
      (∀ᵐ U ∂q.stationary,∀ V : State,spatialAction V=0 → ∀ a : Gauge,
        β*temporalAction U V a<M → F U=0) := by
  obtain ⟨β,hb,hM,q,F,hF,hform,hloc⟩ := arbitrarily_large_native M
  exact ⟨β,hb,hM,q,F,hF,fun Q hQ => native_error_lower q F hF hform Q hQ,hloc⟩

end OperatorDerivativeRewrite.Foundation.PeriodicQuarticNativeObstruction
