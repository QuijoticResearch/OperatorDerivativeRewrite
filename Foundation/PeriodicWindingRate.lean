import Foundation.PeriodicPolynomialGround
import Foundation.PeriodicTransferVariation
import Foundation.SelfAdjointContractionIteration

/-!
# Quantitative energy and winding-correlation bounds for the actual periodic transfer

The true joint energy has an explicit logarithmic-over-beta bound. Actual
measurable gauge-invariant winding probes, a native edge-law Dirichlet identity,
and the existing reversible-contraction iteration theorem give correlation
persistence along the growing floor(beta / log(beta)^2) clock. All laws and
operator domains are the actual finite-periodic ground-transform ones.
The constants are coarse and cell-dependent. Global center-sensitive winding
observables do not establish a local glueball or continuum mass-gap statement.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicEnergyRate
open PeriodicPolynomialGround PeriodicSlabGround PeriodicTemporalConcentration PeriodicSlabJoint

private theorem constant_le_one : lowerConstant ≤ 1 := by
  have hp := Real.pi_gt_three
  have hb0 : 0 ≤ 1/(4*Real.pi^2) := by positivity
  have hb1 : 1/(4*Real.pi^2) ≤ (1 : ℝ) := by
    apply (div_le_one (by positivity : (0 : ℝ)<4*Real.pi^2)).mpr
    nlinarith
  have hpow : (1/(4*Real.pi^2))^256 ≤ (1 : ℝ) := pow_le_one₀ hb0 hb1
  have he : Real.exp (-41472 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  exact (mul_le_mul hpow he (Real.exp_pos _).le (by norm_num)).trans_eq (by ring)

def offset : ℝ := Real.log (768/lowerConstant)
theorem offset_nonneg : 0 ≤ offset := by
  apply Real.log_nonneg
  exact (le_div_iff₀ lowerConstant_pos).mpr (by linarith [constant_le_one])

def threshold (beta : ℝ) : ℝ := (385*Real.log beta+offset)/beta

theorem threshold_nonneg (beta : ℝ) (hb : 1 ≤ beta) : 0 ≤ threshold beta := by
  have hlog := Real.log_nonneg hb
  have ho := offset_nonneg
  unfold threshold
  positivity

theorem threshold_exp (beta : ℝ) (hb : 1 ≤ beta) :
    Real.exp (-beta*threshold beta)=(lowerConstant/768)/beta^385 := by
  have hp : 0<beta := by linarith
  have hc := lowerConstant_pos
  have ha : 0<768/lowerConstant := div_pos (by norm_num) hc
  have hex : -beta*threshold beta=-(385*Real.log beta)-Real.log (768/lowerConstant) := by
    unfold threshold offset
    field_simp
    <;> ring
  rw [hex,Real.exp_sub,Real.exp_neg]
  have hpow : Real.exp (385*Real.log beta)=beta^385 := by
    rw [show (385 : ℝ)=(385 : ℕ) by norm_num,Real.exp_nat_mul,Real.exp_log hp]
  rw [hpow,Real.exp_log ha]
  field_simp

theorem logarithmic_energy_bound {beta : ℝ} (d : GroundData beta) (hb : 1 ≤ beta) :
    (∫ q,energy q ∂tripleLaw d) ≤ (385*Real.log beta+offset+1)/beta := by
  have hp : 0<beta := by linarith
  have hc := lowerConstant_pos
  have h := energy_bound d hb (threshold beta) (threshold_nonneg beta hb)
  rw [threshold_exp beta hb] at h
  convert h using 1 <;> unfold threshold <;> field_simp <;> ring

def rate (beta : ℝ) : ℝ := (385*Real.log beta+offset+1)/beta

theorem rate_nonneg (beta : ℝ) (hb : 1 ≤ beta) : 0 ≤ rate beta := by
  have hlog := Real.log_nonneg hb
  have ho := offset_nonneg
  unfold rate
  positivity

theorem rate_tendsto_zero : Tendsto rate atTop (𝓝 0) := by
  have hl : Tendsto (fun beta : ℝ => Real.log beta/beta) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hi : Tendsto (fun beta : ℝ => (offset+1)/beta) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using tendsto_inv_atTop_zero.const_mul (offset+1)
  have h := (hl.const_mul 385).add hi
  convert h using 1
  · funext beta
    unfold rate
    ring
  · ring

end OperatorDerivativeRewrite.Foundation.PeriodicEnergyRate

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicWindingRate
open PeriodicTemporalSlab PeriodicSlabGround PeriodicSlabL2 PeriodicSlabJoint
open PeriodicTemporalConcentration PeriodicCenteredHolonomy PeriodicTransferVariation

variable {beta : ℝ} (d : GroundData beta)
private instance stationary_probability : IsProbabilityMeasure d.stationary := d.stationary_probability
private instance triple_probability : IsProbabilityMeasure (tripleLaw d) := PeriodicSlabJoint.triple_probability d

/-- A measurable pointwise gauge-invariant representative of the native vector. -/
def gaugeInvariant (F : StateL2 d) : Prop :=
  ∃ f : State → ℝ,Measurable f ∧
    (∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U) ∧
    ∃ hf : MemLp f 2 d.stationary,hf.toLp f=F

private theorem gaugeInvariant_smul (c : ℝ) (F : StateL2 d) (hF : gaugeInvariant d F) :
    gaugeInvariant d (c • F) := by
  obtain ⟨f,hm,hg,hf,rfl⟩ := hF
  refine ⟨c • f,hm.const_smul c,?_,hf.const_smul c,?_⟩
  · intro a U
    change c*f (PeriodicSlabGauge.gaugeAction a U)=c*f U
    rw [hg]
  · exact MemLp.toLp_const_smul c hf

theorem native_dirichlet (F : StateL2 d) :
    SelfAdjointContractionIteration.dissipation (operator d) F=
      ‖rightEmbedding d F-leftEmbedding d F‖^2/2 := by
  have hn := norm_sub_sq_real (rightEmbedding d F) (leftEmbedding d F)
  rw [(rightEmbedding d).norm_map,(leftEmbedding d).norm_map] at hn
  have hp := HilbertRepresentation.predictableAdjoint_pairing (leftEmbedding d)
    (rightEmbedding d F) F
  change inner ℝ (operator d F) F=inner ℝ (rightEmbedding d F) (leftEmbedding d F) at hp
  rw [← hp] at hn
  unfold SelfAdjointContractionIteration.dissipation
  rw [real_inner_self_eq_norm_sq]
  linarith

theorem core_dirichlet_bound (f : State → ℝ) (hf : MemLp f 2 d.stationary)
    (hm : Measurable f) (C : ℝ)
    (h : ∀ q : Triple,(f q.1.2-f q.1.1)^2 ≤ C*temporalEnergy q) :
    SelfAdjointContractionIteration.dissipation (operator d) (hf.toLp f) ≤
      (C/2)*(∫ q,temporalEnergy q ∂tripleLaw d) := by
  have hn := native_dirichlet d (hf.toLp f)
  rw [edge_norm_square] at hn
  have hm2 : Measurable (fun p : State × State => (f p.2-f p.1)^2) :=
    ((hm.comp measurable_snd).sub (hm.comp measurable_fst)).pow_const 2
  have hp : (∫ q : Triple,(f q.1.2-f q.1.1)^2 ∂tripleLaw d)=
      ∫ p : State × State,(f p.2-f p.1)^2 ∂edgeLaw d := by
    have he := integral_map (μ := tripleLaw d) (φ := (Prod.fst : Triple → State × State))
      measurable_fst.aemeasurable hm2.aestronglyMeasurable
    rw [(pair_preserving d).map_eq] at he
    exact he.symm
  have hi := (temporal_integrable d).const_mul C
  have hle : (∫ q : Triple,(f q.1.2-f q.1.1)^2 ∂tripleLaw d) ≤
      ∫ q,C*temporalEnergy q ∂tripleLaw d := by
    exact integral_mono_of_nonneg (ae_of_all _ (fun _ => sq_nonneg _)) hi (ae_of_all _ h)
  rw [integral_const_mul,hp] at hle
  linarith

theorem eventual_dirichlet_trial : ∀ᶠ beta : ℝ in atTop,∀ d : GroundData beta,
    ∃ f : State → ℝ,Measurable f ∧ (∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U) ∧
      ∃ hf : MemLp f 2 d.stationary,
      (∫ U,f U ∂d.stationary)=0 ∧ (1/24 : ℝ) ≤ ‖hf.toLp f‖^2 ∧
      SelfAdjointContractionIteration.dissipation (operator d) (hf.toLp f) ≤
        64*(∫ q,temporalEnergy q ∂tripleLaw d) := by
  filter_upwards [eventual_variance_channel] with beta hb
  intro g
  have hfirst := core_dirichlet_bound g first (first_memLp g) first_measurable 128 (by
    intro q
    have h := PeriodicLoopVariation.winding_trace_change q.1.1 q.1.2 q.2 origin 0
    change (first q.1.1-first q.1.2)^2 ≤ 32*temporalEnergy q at h
    nlinarith [(temporal_bounds q).1])
  have hsecond := core_dirichlet_bound g second (second_memLp g) second_measurable 128 (by
    intro q
    have h := PeriodicLoopVariation.winding_trace_change q.1.1 q.1.2 q.2 origin 1
    change (second q.1.1-second q.1.2)^2 ≤ 32*temporalEnergy q at h
    nlinarith [(temporal_bounds q).1])
  have hmixed := core_dirichlet_bound g mixed (mixed_memLp g) mixed_measurable 128 (by
    intro q
    have h := PeriodicLoopVariation.product_trace_change q.1.1 q.1.2 q.2 origin 0 1
    change (mixed q.1.1-mixed q.1.2)^2 ≤ 128*temporalEnergy q at h
    nlinarith)
  norm_num only [show (128 : ℝ)/2=64 by norm_num] at hfirst hsecond hmixed
  rcases hb g with h|h|h
  · refine ⟨first,first_measurable,(fun a U => PeriodicSpatialHolonomy.trace_gauge a U origin 0),first_memLp g,first_mean_zero g,?_,hfirst⟩
    rwa [state_norm_square,← first_variance]
  · refine ⟨second,second_measurable,(fun a U => PeriodicSpatialHolonomy.trace_gauge a U origin 1),second_memLp g,second_mean_zero g,?_,hsecond⟩
    rwa [state_norm_square,← second_variance]
  · refine ⟨mixed,mixed_measurable,(fun a U => PeriodicSpatialHolonomy.product_trace_gauge a U origin 0 1),mixed_memLp g,mixed_mean_zero g,?_,hmixed⟩
    rwa [state_norm_square,← mixed_variance]

theorem eventual_normalized_dirichlet : ∀ᶠ beta : ℝ in atTop,∀ d : GroundData beta,
    ∃ N : StateL2 d,gaugeInvariant d N ∧ ‖N‖=1 ∧ (∫ U,N U ∂d.stationary)=0 ∧
      SelfAdjointContractionIteration.dissipation (operator d) N ≤
        1536*(∫ q,energy q ∂tripleLaw d) := by
  filter_upwards [eventual_dirichlet_trial] with beta hb
  intro g
  obtain ⟨f,hm,hg,hf,hmean,hnorm,hres⟩ := hb g
  let F : StateL2 g := hf.toLp f
  change (1/24 : ℝ) ≤ ‖F‖^2 at hnorm
  change SelfAdjointContractionIteration.dissipation (operator g) F ≤ _ at hres
  have hF : 0<‖F‖ := by nlinarith [norm_nonneg F]
  have hFm : (∫ U,F U ∂g.stationary)=0 :=
    (integral_congr_ae (MemLp.coeFn_toLp hf)).trans hmean
  let N : StateL2 g := ‖F‖⁻¹ • F
  have hinv : ‖F‖⁻¹*‖F‖=1 := inv_mul_cancel₀ hF.ne'
  have hN : ‖N‖=1 := by
    dsimp [N]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hF),hinv]
  refine ⟨N,?_,hN,?_,?_⟩
  · exact gaugeInvariant_smul g (‖F‖⁻¹) F ⟨f,hm,hg,hf,rfl⟩
  · rw [integral_congr_ae (Lp.coeFn_smul ‖F‖⁻¹ F)]
    simp only [Pi.smul_apply]
    rw [integral_smul,hFm,smul_zero]
  · have hii : ‖F‖⁻¹^2*‖F‖^2=1 := by rw [← mul_pow,hinv]; norm_num
    have hmul := mul_le_mul_of_nonneg_left hnorm (sq_nonneg (‖F‖⁻¹))
    have hi : ‖F‖⁻¹^2 ≤ 24 := by nlinarith
    have hT : (∫ q,temporalEnergy q ∂tripleLaw g) ≤ ∫ q,energy q ∂tripleLaw g :=
      integral_mono (temporal_integrable g) (energy_integrable g) temporal_le_energy
    have hE : 0 ≤ ∫ q,energy q ∂tripleLaw g := integral_nonneg (fun q => (energy_bounds q).1)
    have hd : SelfAdjointContractionIteration.dissipation (operator g) N=
        ‖F‖⁻¹^2*SelfAdjointContractionIteration.dissipation (operator g) F := by
      dsimp [N,SelfAdjointContractionIteration.dissipation]
      rw [map_smul,real_inner_smul_left,real_inner_smul_right,real_inner_smul_left,real_inner_smul_right]
      ring
    rw [hd]
    calc
      _ ≤ ‖F‖⁻¹^2*(64*(∫ q,energy q ∂tripleLaw g)) :=
        mul_le_mul_of_nonneg_left (hres.trans (mul_le_mul_of_nonneg_left hT (by norm_num))) (sq_nonneg _)
      _ ≤ 24*(64*(∫ q,energy q ∂tripleLaw g)) :=
        mul_le_mul_of_nonneg_right hi (mul_nonneg (by norm_num) hE)
      _ = _ := by ring

theorem eventual_lag_bound : ∀ᶠ beta : ℝ in atTop,∀ d : GroundData beta,
    ∃ N : StateL2 d,gaugeInvariant d N ∧ ‖N‖=1 ∧ (∫ U,N U ∂d.stationary)=0 ∧ ∀ n : ℕ,
      1-1536*(n : ℝ)*(∫ q,energy q ∂tripleLaw d) ≤
        inner ℝ (SelfAdjointContractionIteration.steps (operator d) n N) N ∧
      inner ℝ (SelfAdjointContractionIteration.steps (operator d) n N) N ≤ 1 := by
  filter_upwards [eventual_normalized_dirichlet] with beta hb
  intro g
  obtain ⟨N,hg,hN,hm,hD⟩ := hb g
  refine ⟨N,hg,hN,hm,?_⟩
  intro n
  have hl := SelfAdjointContractionIteration.lag_lower (operator g)
    (operator_contraction g) (operator_symmetric g) n N
  have hu := SelfAdjointContractionIteration.lag_upper (operator g)
    (operator_contraction g) (operator_symmetric g) n N
  rw [real_inner_self_eq_norm_sq,hN,one_pow] at hl hu
  have hb := mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg n)
  exact ⟨by nlinarith,hu⟩

open PeriodicEnergyRate

theorem eventual_logarithmic_lag : ∀ᶠ beta : ℝ in atTop,∀ d : GroundData beta,
    ∃ N : StateL2 d,gaugeInvariant d N ∧ ‖N‖=1 ∧ (∫ U,N U ∂d.stationary)=0 ∧ ∀ n : ℕ,
      1-1536*(n : ℝ)*rate beta ≤
        inner ℝ (SelfAdjointContractionIteration.steps (operator d) n N) N ∧
      inner ℝ (SelfAdjointContractionIteration.steps (operator d) n N) N ≤ 1 := by
  filter_upwards [eventual_lag_bound,eventually_ge_atTop (1 : ℝ)] with beta hb hbeta
  intro g
  obtain ⟨N,hg,hN,hm,hn⟩ := hb g
  have hE : (∫ q,energy q ∂tripleLaw g) ≤ rate beta := logarithmic_energy_bound g hbeta
  refine ⟨N,hg,hN,hm,?_⟩
  intro n
  have hmul := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ 1536*(n : ℝ))
  exact ⟨by linarith [(hn n).1],(hn n).2⟩

theorem eventual_iteration_budget : ∀ᶠ beta : ℝ in atTop,∀ d : GroundData beta,
    ∀ n : ℕ,∀ q : ℝ,
      (∀ F : StateL2 d,gaugeInvariant d F → (∫ U,F U ∂d.stationary)=0 →
        ‖SelfAdjointContractionIteration.steps (operator d) n F‖ ≤ q*‖F‖) →
      1-q ≤ 1536*(n : ℝ)*rate beta := by
  filter_upwards [eventual_logarithmic_lag] with beta hb
  intro g n q hc
  obtain ⟨N,hg,hN,hm,hn⟩ := hb g
  have hnorm := hc N hg hm
  have hinner := real_inner_le_norm (SelfAdjointContractionIteration.steps (operator g) n N) N
  rw [hN,mul_one] at hnorm hinner
  linarith [(hn n).1]

theorem slow_clock_persistence (n : ℝ → ℕ)
    (hc : Tendsto (fun beta : ℝ => (n beta : ℝ)*rate beta) atTop (𝓝 0))
    (eps : ℝ) (he : 0<eps) :
    ∀ᶠ beta : ℝ in atTop,∀ d : GroundData beta,
      ∃ N : StateL2 d,gaugeInvariant d N ∧ ‖N‖=1 ∧ (∫ U,N U ∂d.stationary)=0 ∧
        1-eps < inner ℝ (SelfAdjointContractionIteration.steps (operator d) (n beta) N) N ∧
        inner ℝ (SelfAdjointContractionIteration.steps (operator d) (n beta) N) N ≤ 1 := by
  have hsmall := hc.eventually (gt_mem_nhds (by positivity : (0 : ℝ)<eps/1536))
  filter_upwards [eventual_logarithmic_lag,hsmall] with beta hb hs
  intro g
  obtain ⟨N,hg,hN,hm,hn⟩ := hb g
  refine ⟨N,hg,hN,hm,?_,(hn (n beta)).2⟩
  linarith [(hn (n beta)).1]

def logarithmicClock (beta : ℝ) : ℕ := ⌊beta/(Real.log beta)^2⌋₊

theorem logarithmic_clock_rate :
    Tendsto (fun beta : ℝ => (logarithmicClock beta : ℝ)*rate beta) atTop (𝓝 0) := by
  have hi : Tendsto (fun beta : ℝ => (Real.log beta)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hu : Tendsto (fun beta : ℝ => 385/(Real.log beta)+(offset+1)/(Real.log beta)^2)
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,inv_pow,mul_zero,zero_pow (by norm_num : 2 ≠ 0),add_zero]
      using (hi.const_mul 385).add ((hi.pow 2).const_mul (offset+1))
  apply squeeze_zero' ?_ ?_ hu
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with beta hb
    exact mul_nonneg (Nat.cast_nonneg _) (rate_nonneg beta (by linarith))
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with beta hb
    have hp : 0<beta := by linarith
    have hl : 0<Real.log beta := Real.log_pos (by linarith)
    have hf : (logarithmicClock beta : ℝ) ≤ beta/(Real.log beta)^2 :=
      Nat.floor_le (div_nonneg hp.le (sq_nonneg _))
    have hm := mul_le_mul_of_nonneg_right hf (rate_nonneg beta (by linarith))
    have heq : (beta/(Real.log beta)^2)*rate beta=
        385/(Real.log beta)+(offset+1)/(Real.log beta)^2 := by
      unfold rate
      field_simp
      <;> ring
    exact hm.trans_eq heq

theorem logarithmic_clock_persistence (eps : ℝ) (he : 0<eps) :
    ∀ᶠ beta : ℝ in atTop,∀ d : GroundData beta,
      ∃ N : StateL2 d,gaugeInvariant d N ∧ ‖N‖=1 ∧ (∫ U,N U ∂d.stationary)=0 ∧
        1-eps < inner ℝ (SelfAdjointContractionIteration.steps (operator d) (logarithmicClock beta) N) N ∧
        inner ℝ (SelfAdjointContractionIteration.steps (operator d) (logarithmicClock beta) N) N ≤ 1 :=
  slow_clock_persistence logarithmicClock logarithmic_clock_rate eps he

theorem logarithmic_clock_tendsto_atTop : Tendsto logarithmicClock atTop atTop := by
  have hs : Tendsto (fun beta : ℝ => (Real.log beta)^2/beta) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  apply tendsto_atTop.2
  intro N
  have hsmall := hs.eventually (gt_mem_nhds (by positivity : (0 : ℝ)<1/((N : ℝ)+1)))
  filter_upwards [hsmall,eventually_ge_atTop (2 : ℝ)] with beta hh hb
  have hp : 0<beta := by linarith
  have hl : 0<Real.log beta := Real.log_pos (by linarith)
  have hx := (div_lt_div_iff₀ hp (by positivity : (0 : ℝ)<(N : ℝ)+1)).mp hh
  have hr : (N : ℝ) ≤ beta/(Real.log beta)^2 :=
    (le_div_iff₀ (sq_pos_of_pos hl)).mpr (by nlinarith [sq_nonneg (Real.log beta)])
  exact (Nat.le_floor_iff (div_nonneg hp.le (sq_nonneg _))).mpr hr

theorem logarithmic_clock_no_uniform_contraction (q : ℝ) (hq : q<1) :
    ∀ᶠ beta : ℝ in atTop,∀ d : GroundData beta,
      ¬ ∀ F : StateL2 d,gaugeInvariant d F → (∫ U,F U ∂d.stationary)=0 →
        ‖SelfAdjointContractionIteration.steps (operator d) (logarithmicClock beta) F‖ ≤ q*‖F‖ := by
  have hsmall := logarithmic_clock_rate.eventually
    (gt_mem_nhds (by positivity : (0 : ℝ)<(1-q)/1536))
  filter_upwards [eventual_iteration_budget,hsmall] with beta hb hs
  intro g hc
  have h := hb g (logarithmicClock beta) q hc
  linarith

end OperatorDerivativeRewrite.Foundation.PeriodicWindingRate
