import Foundation.PeriodicSlabJoint

/-! Concentration of the actual temporal slab joint law. Spatial-marginal
concentration is not used as a substitute for this joint estimate. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicTemporalConcentration
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround PeriodicSlabJoint

def energy (q : Triple) : ℝ := halfAction q.1.1 q.1.2 q.2
def temporalEnergy (q : Triple) : ℝ := temporalAction q.1.1 q.1.2 q.2

theorem energy_measurable : Measurable energy := PeriodicLowActionBlock.action_continuous.measurable
theorem energy_bounds (q : Triple) : 0 ≤ energy q ∧ energy q ≤ 768 := half_action_bounds _ _ _
theorem temporal_measurable : Measurable temporalEnergy := temporal_action_joint_measurable
theorem temporal_bounds (q : Triple) : 0 ≤ temporalEnergy q ∧ temporalEnergy q ≤ 384 := temporal_action_bounds _ _ _

theorem temporal_le_energy (q : Triple) : temporalEnergy q ≤ energy q := by
  have hU := (spatial_action_bounds q.1.1).1
  have hV := (spatial_action_bounds q.1.2).1
  unfold energy temporalEnergy halfAction
  linarith

theorem temporal_word_alignment (U V : State) (a : Gauge) (e : SpatialEdge) :
    temporalWord U V a e=U e*(PeriodicSlabGauge.gaugeAction a V e)⁻¹ := by
  unfold temporalWord PeriodicSlabGauge.gaugeAction
  group

theorem temporal_zero_iff_alignment (U V : State) (a : Gauge) :
    temporalAction U V a=0 ↔ U=PeriodicSlabGauge.gaugeAction a V := by
  constructor
  · intro hz
    funext e
    have h := Finset.single_le_sum (fun e (_ : e∈Finset.univ) =>
      FourCubePinnedCoercivity.defect_nonneg (temporalWord U V a e)) (Finset.mem_univ e)
    change FourCubePinnedCoercivity.defect (temporalWord U V a e) ≤ temporalAction U V a at h
    have hd := (FourCubePinnedCoercivity.defect_zero_iff _).mp
      (le_antisymm (h.trans_eq hz) (FourCubePinnedCoercivity.defect_nonneg _))
    rw [temporal_word_alignment] at hd
    exact mul_inv_eq_one.mp hd
  · rintro rfl
    unfold temporalAction
    simp only [temporal_word_alignment,mul_inv_cancel,SU2OpenLinkGaugeObstruction.halfTrace_one,
      sub_self,Finset.sum_const_zero]

variable {beta : ℝ} (g : GroundData beta)

private theorem unweighted_integrable :
    Integrable (fun q : Triple => g.function q.1.1*g.function q.1.2) reference := by
  apply Integrable.of_bound ((g.measurable.comp (measurable_fst.comp measurable_fst)).mul
    (g.measurable.comp (measurable_snd.comp measurable_fst))).aestronglyMeasurable
    (|g.upper| * |g.upper|)
  filter_upwards with q
  change ‖g.function q.1.1*g.function q.1.2‖ ≤ _
  rw [Real.norm_eq_abs,abs_mul]
  exact mul_le_mul ((g.bounds _).2.trans (le_abs_self _)) ((g.bounds _).2.trans (le_abs_self _))
    (abs_nonneg _) (abs_nonneg _)

private theorem unweighted_integral :
    (∫ q : Triple,g.function q.1.1*g.function q.1.2 ∂reference)=
      (∫ U,g.function U ∂boundaryHaar)^2 := by
  change (∫ q : Triple,g.function q.1.1*g.function q.1.2 ∂
    (boundaryHaar.prod boundaryHaar).prod gaugeHaar)=_
  rw [integral_prod _ (unweighted_integrable g)]
  simp only [integral_const,probReal_univ,one_smul]
  rw [integral_prod_mul]
  ring

private theorem mass_square_le : (∫ U,g.function U ∂boundaryHaar)^2 ≤ g.normalizer := by
  have hm : MemLp g.function 2 boundaryHaar :=
    MemLp.of_bound g.measurable.aestronglyMeasurable g.upper (ae_of_all _ (fun U => (g.bounds U).2))
  have h := variance_nonneg g.function boundaryHaar
  rw [variance_eq_sub hm] at h
  change 0 ≤ g.normalizer-(∫ U,g.function U ∂boundaryHaar)^2 at h
  linarith

theorem tail_eigenfactor (hb : 0 ≤ beta) (eps : ℝ) :
    (tripleLaw g).real {q | eps ≤ energy q} ≤ Real.exp (-beta*eps)/g.value := by
  let S : Set Triple := {q | eps ≤ energy q}
  have hS : MeasurableSet S := measurableSet_le measurable_const energy_measurable
  have hi := probe_integrable g (S.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hS) 1
    (fun q => by by_cases hq : q∈S <;> simp [hq])
  have hu := (unweighted_integrable g).const_mul (Real.exp (-beta*eps))
  have hp (q : Triple) : jointWeight g q*S.indicator (fun _ => (1 : ℝ)) q ≤
      Real.exp (-beta*eps)*(g.function q.1.1*g.function q.1.2) := by
    by_cases hq : q∈S
    · rw [Set.indicator_of_mem hq,mul_one]
      unfold jointWeight
      apply mul_le_mul_of_nonneg_right ?_ (mul_pos (g.function_pos _) (g.function_pos _)).le
      change Real.exp (-beta*energy q) ≤ Real.exp (-beta*eps)
      apply Real.exp_le_exp.mpr
      have hh : eps ≤ energy q := hq
      nlinarith [mul_le_mul_of_nonneg_left hh hb]
    · rw [Set.indicator_of_notMem hq,mul_zero]
      exact (mul_pos (Real.exp_pos _) (mul_pos (g.function_pos _) (g.function_pos _))).le
  have hn := integral_mono hi hu hp
  rw [integral_const_mul,unweighted_integral] at hn
  have hn' := hn.trans (mul_le_mul_of_nonneg_left (mass_square_le g) (Real.exp_pos (-beta*eps)).le)
  have hf := integral_formula g (S.indicator (fun _ => (1 : ℝ)))
  have hid : (∫ q,S.indicator (fun _ => (1 : ℝ)) q ∂tripleLaw g)=(tripleLaw g).real S :=
    integral_indicator_one hS
  rw [hid] at hf
  change (tripleLaw g).real S ≤ _
  rw [hf]
  calc
    _ ≤ (Real.exp (-beta*eps)*g.normalizer)/(g.value*g.normalizer) :=
      div_le_div_of_nonneg_right hn' (mul_pos g.value_pos g.normalizer_pos).le
    _ = _ := by field_simp [g.value_pos.ne',g.normalizer_pos.ne']

theorem tail_exponential (eps : ℝ) (he : 0 < eps) :
    ∃ C : ℝ,0<C ∧ ∀ beta : ℝ,0≤beta → ∀ g : GroundData beta,
      (tripleLaw g).real {q | eps ≤ energy q} ≤ C*Real.exp (-beta*eps/2) := by
  obtain ⟨c,hc,hl⟩ := PeriodicGroundMass.eigenvalue_small_rate (eps/2) (by positivity)
  refine ⟨1/c,div_pos zero_lt_one hc,?_⟩
  intro beta hb g
  have hv := hl beta hb g
  have hd := div_le_div_of_nonneg_left (Real.exp_pos (-beta*eps)).le
    (mul_pos hc (Real.exp_pos (-beta*(eps/2)))) hv
  have heq : Real.exp (-beta*eps)/(c*Real.exp (-beta*(eps/2)))=(1/c)*Real.exp (-beta*eps/2) := by
    have h : Real.exp (-beta*eps)=Real.exp (-beta*eps/2)*Real.exp (-beta*(eps/2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [h]
    field_simp [hc.ne',(Real.exp_pos (-beta*(eps/2))).ne']
  exact (tail_eigenfactor g hb eps).trans (hd.trans_eq heq)

theorem energy_integrable : Integrable energy (tripleLaw g) :=
  Integrable.of_bound energy_measurable.aestronglyMeasurable 768
    (ae_of_all _ (fun q => by rw [Real.norm_eq_abs,abs_of_nonneg (energy_bounds q).1]; exact (energy_bounds q).2))

theorem temporal_integrable : Integrable temporalEnergy (tripleLaw g) :=
  Integrable.of_bound temporal_measurable.aestronglyMeasurable 384
    (ae_of_all _ (fun q => by rw [Real.norm_eq_abs,abs_of_nonneg (temporal_bounds q).1]; exact (temporal_bounds q).2))

theorem energy_from_tail (eps : ℝ) (he : 0 ≤ eps) :
    (∫ q,energy q ∂tripleLaw g) ≤ eps+768*(tripleLaw g).real {q | eps ≤ energy q} := by
  let S : Set Triple := {q | eps ≤ energy q}
  have hS : MeasurableSet S := measurableSet_le measurable_const energy_measurable
  have hi : Integrable (S.indicator (fun _ => (1 : ℝ))) (tripleLaw g) :=
    (integrable_const 1).indicator hS
  have hp (q : Triple) : energy q ≤ eps+768*S.indicator (fun _ => (1 : ℝ)) q := by
    by_cases hq : q∈S
    · rw [Set.indicator_of_mem hq,mul_one]
      linarith [(energy_bounds q).2]
    · rw [Set.indicator_of_notMem hq,mul_zero,add_zero]
      exact le_of_lt (lt_of_not_ge hq)
  have h := integral_mono (energy_integrable g) ((integrable_const eps).add (hi.const_mul 768)) hp
  simp only [Pi.add_apply] at h
  have hsid : (∫ q,S.indicator (fun _ => (1 : ℝ)) q ∂tripleLaw g)=(tripleLaw g).real S :=
    integral_indicator_one hS
  rw [integral_add (integrable_const eps) (hi.const_mul 768),integral_const_mul,hsid] at h
  simpa only [integral_const,probReal_univ,one_smul,S] using h

theorem energy_small (eps : ℝ) (he : 0 < eps) :
    ∀ᶠ beta : ℝ in atTop,∀ g : GroundData beta,(∫ q,energy q ∂tripleLaw g) ≤ eps := by
  obtain ⟨C,hC,htail⟩ := tail_exponential (eps/2) (by positivity)
  have ht : Tendsto (fun beta : ℝ => C*Real.exp (-beta*(eps/2)/2)) atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_atBot.comp
      (Filter.tendsto_id.const_mul_atTop_of_neg (by linarith : -(eps/2)/2 < 0))).const_mul C
    have hx : (fun beta : ℝ => C*Real.exp (-beta*(eps/2)/2))=
        (fun beta : ℝ => C*Real.exp ((-(eps/2)/2)*beta)) := by funext beta; congr 2 <;> ring
    rw [hx]
    simpa only [Function.comp_apply,id_eq,mul_zero] using h
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ)<eps/(2*768)))] with beta hbeta hsmall
  intro g
  have h := (energy_from_tail g (eps/2) (by positivity)).trans
    (add_le_add (le_refl (eps/2))
      (mul_le_mul_of_nonneg_left (htail beta hbeta g) (by norm_num : (0 : ℝ)≤768)))
  linarith

theorem energy_tendsto_zero :
    Tendsto (fun beta : ℝ => ∫ q,energy q ∂tripleLaw (ground beta)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun beta => ha.trans_le (integral_nonneg (fun q => (energy_bounds q).1)))
  · intro b hb
    filter_upwards [energy_small (b/2) (by positivity)] with beta hbeta
    exact (hbeta (ground beta)).trans_lt (by linarith)

theorem temporal_tendsto_zero :
    Tendsto (fun beta : ℝ => ∫ q,temporalEnergy q ∂tripleLaw (ground beta)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => integral_nonneg (fun q => (temporal_bounds q).1))) ?_
    energy_tendsto_zero
  exact Eventually.of_forall (fun beta => integral_mono (temporal_integrable _) (energy_integrable _) temporal_le_energy)

theorem spatial_zero_temporal_positive : ∃ U V : State,∃ a : Gauge,
    spatialAction U=0 ∧ spatialAction V=0 ∧ 0<temporalAction U V a := by
  let o : SpatialVertex := fun _ => 0
  let a : Gauge := fun v => if v 0=0 then SU2StapleExtremes.minusOne else 1
  have h0 : (1 : ZMod 4)≠0 := by decide
  have hw : halfTrace (temporalWord (1 : State) 1 a (o,0))= -1 := by
    simp [temporalWord,a,o,shift,h0,SU2WilsonConvolution.halfTrace_inv,
      SU2OpenLinkGaugeObstruction.halfTrace_minusOne]
  have hs : spatialAction (1 : State)=0 := by
    simp [spatialAction,PeriodicTemporalSlab.spatialWord,SU2OpenLinkGaugeObstruction.halfTrace_one]
  have ht : (2 : ℝ) ≤ temporalAction (1 : State) 1 a := by
    have h := Finset.single_le_sum (fun e (_ : e∈Finset.univ) =>
      sub_nonneg.mpr ((abs_le.mp (halfTrace_bound (temporalWord (1 : State) 1 a e))).2))
      (Finset.mem_univ (o,(0 : Fin 3)))
    change 1-halfTrace (temporalWord (1 : State) 1 a (o,0)) ≤ temporalAction (1 : State) 1 a at h
    rw [hw] at h
    linarith
  exact ⟨1,1,a,hs,hs,lt_of_lt_of_le (by norm_num : (0 : ℝ)<2) ht⟩

end OperatorDerivativeRewrite.Foundation.PeriodicTemporalConcentration
