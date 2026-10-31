import Foundation.PeriodicEvenWindingVariation
import Foundation.ProbabilityTailBound
/-! Actual centered center-even winding trials: native mean/norm domains,
Cauchy--Schwarz reduction, exact Haar moments and a strict finite-coupling
variance floor. The unit-vector quasimode criterion is conditional on two
explicit ground-law moment bounds. Neither a uniform relative variance nor
a large-coupling center-even near-one theorem is assumed or established. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.PeriodicEvenWindingCriterion
open PeriodicTemporalSlab PeriodicSlabGround PeriodicSlabJoint PeriodicSlabL2
open PeriodicEvenWindingVariation PeriodicTemporalConcentration
variable {β : ℝ} (g : GroundData β)
private instance stationary_probability : IsProbabilityMeasure g.stationary := g.stationary_probability
private instance joint_probability : IsProbabilityMeasure (tripleLaw g) := triple_probability g

def mean (i : Fin 3) : ℝ := ∫ U,evenWinding i U ∂g.stationary
def secondMoment (i : Fin 3) : ℝ := ∫ U,evenWinding i U^2 ∂g.stationary
def centered (i : Fin 3) (U : State) : ℝ := evenWinding i U-mean g i

theorem centered_measurable (i : Fin 3) : Measurable (centered g i) :=
  (even_measurable i).sub measurable_const

theorem centered_memLp (i : Fin 3) : MemLp (centered g i) 2 g.stationary :=
  (even_memLp g i).sub (memLp_const (mean g i))

def vector (i : Fin 3) : StateL2 g := (centered_memLp g i).toLp (centered g i)

theorem centered_mean_zero (i : Fin 3) : (∫ U,centered g i U ∂g.stationary)=0 := by
  rw [show centered g i=(fun U => evenWinding i U-mean g i) from rfl,
    integral_sub ((even_memLp g i).integrable (by norm_num)) (integrable_const _)]
  simp [mean]

theorem centered_gauge (i : Fin 3) (a : Gauge) (U : State) :
    centered g i (PeriodicSlabGauge.gaugeAction a U)=centered g i U := by
  unfold centered
  rw [even_gauge]

theorem centered_seam (i j : Fin 3) (U : State) :
    centered g i (PeriodicCenterSeam.flip j U)=centered g i U := by
  unfold centered
  rw [even_seam]

theorem second_nonneg (i : Fin 3) : 0≤secondMoment g i := integral_nonneg (fun _ => sq_nonneg _)

theorem variance_formula (i : Fin 3) :
    variance (evenWinding i) g.stationary=secondMoment g i-mean g i^2 := by
  rw [variance_eq_sub (even_memLp g i)]
  rfl

theorem vector_norm (i : Fin 3) : ‖vector g i‖^2=variance (evenWinding i) g.stationary := by
  rw [vector,PeriodicTransferVariation.state_norm_square]
  exact (variance_eq_integral (even_measurable i).aemeasurable).symm

theorem left_triple_preserving :
    MeasurePreserving (fun q : Triple => q.1.1) (tripleLaw g) g.stationary :=
  (left_preserving g).comp (pair_preserving g)

theorem second_triple (i : Fin 3) :
    (∫ q : Triple,evenWinding i q.1.1^2 ∂tripleLaw g)=secondMoment g i := by
  have h := integral_map (μ := tripleLaw g) (left_triple_preserving g).measurable.aemeasurable
    ((even_measurable i).pow_const 2).aestronglyMeasurable
  rw [(left_triple_preserving g).map_eq] at h
  exact h.symm

theorem weighted_cauchy (i : Fin 3) :
    (∫ q,weightedEnergy i q ∂tripleLaw g)^2 ≤
      secondMoment g i*(∫ q,energy q^2 ∂tripleLaw g) := by
  have hH := (even_memLp g i).comp_measurePreserving (left_triple_preserving g)
  have hE : MemLp energy 2 (tripleLaw g) :=
    MemLp.of_bound energy_measurable.aestronglyMeasurable 768
      (ae_of_all _ (fun q => by rw [Real.norm_eq_abs,abs_of_nonneg (energy_bounds q).1]; exact (energy_bounds q).2))
  have h := ProbabilityTailBound.integral_mul_square_le (tripleLaw g)
    (fun q : Triple => evenWinding i q.1.1) energy
    (fun q => (even_bounds i q.1.1).1) (fun q => (energy_bounds q).1) hH hE
  rw [second_triple] at h
  exact h


theorem centered_edge (i : Fin 3) :
    ‖rightEmbedding g (vector g i)-leftEmbedding g (vector g i)‖^2=
      ∫ q : Triple,(evenWinding i q.1.2-evenWinding i q.1.1)^2 ∂tripleLaw g := by
  rw [vector,PeriodicTransferVariation.edge_norm_square]
  have he : (fun p : State × State => (centered g i p.2-centered g i p.1)^2)=
      (fun p => (evenWinding i p.2-evenWinding i p.1)^2) := by
    funext p
    unfold centered
    congr 1
    ring
  rw [he]
  have hm : Measurable (fun p : State × State => (evenWinding i p.2-evenWinding i p.1)^2) :=
    (((even_measurable i).comp measurable_snd).sub ((even_measurable i).comp measurable_fst)).pow_const 2
  have h := integral_map (μ := tripleLaw g) (pair_preserving g).measurable.aemeasurable hm.aestronglyMeasurable
  rw [(pair_preserving g).map_eq] at h
  exact h

theorem centered_residual_bound (i : Fin 3) :
    ‖operator g (vector g i)-vector g i‖^2 ≤
      2048*(∫ q,energy q^2 ∂tripleLaw g)+256*(∫ q,weightedEnergy i q ∂tripleLaw g) := by
  have hr := PeriodicTransferVariation.operator_residual g (vector g i)
  have hs := mul_self_le_mul_self (norm_nonneg _) hr
  have he := centered_edge g i
  have hi := ((PeriodicCurvatureWeighted.energy_square_integrable g).const_mul 2048).add
    ((weighted_integrable g i).const_mul 256)
  have hle := integral_mono_of_nonneg
    (ae_of_all (tripleLaw g) (fun q : Triple => sq_nonneg (evenWinding i q.1.2-evenWinding i q.1.1)))
    hi (ae_of_all _ (even_energy_variation i))
  change (∫ q : Triple,(evenWinding i q.1.2-evenWinding i q.1.1)^2 ∂tripleLaw g)≤
    (∫ q : Triple,2048*energy q^2+256*weightedEnergy i q ∂tripleLaw g) at hle
  rw [integral_add ((PeriodicCurvatureWeighted.energy_square_integrable g).const_mul 2048)
    ((weighted_integrable g i).const_mul 256),integral_const_mul,integral_const_mul] at hle
  nlinarith only [hs,he,hle]

theorem relative_residual (i : Fin 3) (c η : ℝ) (hc : 0<c) (hη : 0≤η)
    (hvar : c*secondMoment g i≤variance (evenWinding i) g.stationary)
    (he : (∫ q,energy q^2 ∂tripleLaw g)≤η^2*secondMoment g i) :
    ‖operator g (vector g i)-vector g i‖^2 ≤
      ((2048*η^2+256*η)/c)*‖vector g i‖^2 := by
  have hM := second_nonneg g i
  have hw := weighted_cauchy g i
  have hm : (∫ q,weightedEnergy i q ∂tripleLaw g)≤η*secondMoment g i := by
    have hs := mul_le_mul_of_nonneg_left he hM
    nlinarith [mul_nonneg hη hM]
  have hr := centered_residual_bound g i
  have hc0 : 0≤(2048*η^2+256*η)/c := div_nonneg (by positivity) hc.le
  have hv := mul_le_mul_of_nonneg_left hvar hc0
  have hcancel : ((2048*η^2+256*η)/c)*(c*secondMoment g i)=
      (2048*η^2+256*η)*secondMoment g i := by field_simp
  rw [hcancel,← vector_norm g i] at hv
  nlinarith only [hr,he,hm,hv]


open QuaternionSU2Representation PeriodicSpatialHolonomy PeriodicGaugeSaturatedGround PeriodicWilsonSlab
open PeriodicBoundaryHaarReduction

theorem winding_preserving (i : Fin 3) :
    MeasurePreserving (fun U : State => winding U root i) boundaryHaar law := by
  have hp : MeasurePreserving (fun q : Chords => q (wrapChord i)) chordHaar law := by
    unfold chordHaar
    exact measurePreserving_eval (fun _ : ChordIndex => law) (wrapChord i)
  have h := hp.comp reduced_preserving
  convert h using 1
  funext U
  exact (reduced_winding U i).symm

theorem haar_trace_moment (i : Fin 3) (k : ℕ) :
    (∫ U : State,halfTrace (winding U root i)^k ∂boundaryHaar)=
      ∫ A,halfTrace A^k ∂law := by
  have h := integral_map (μ := boundaryHaar) (winding_preserving i).measurable.aemeasurable
    (halfTrace_measurable.pow_const k).aestronglyMeasurable
  rw [(winding_preserving i).map_eq] at h
  exact h.symm

private theorem trace_integrable (i : Fin 3) (k : ℕ) :
    Integrable (fun U : State => halfTrace (winding U root i)^k) boundaryHaar :=
  BoundedExponentialTiltResponse.bounded_power_integrable boundaryHaar
    (fun U : State => halfTrace (winding U root i))
    (halfTrace_measurable.comp (by unfold winding; fun_prop)) (fun _ => halfTrace_bound _) k

theorem haar_even_memLp (i : Fin 3) : MemLp (evenWinding i) 2 boundaryHaar :=
  MemLp.of_bound (even_measurable i).aestronglyMeasurable 1
    (ae_of_all _ (fun U => by rw [Real.norm_eq_abs,abs_of_nonneg (even_bounds i U).1]; exact (even_bounds i U).2))

theorem haar_even_mean (i : Fin 3) : (∫ U,evenWinding i U ∂boundaryHaar)=3/4 := by
  have h := (SU2TiltEnergyResponse.moment_values law).2.1
  simp only [evenWinding]
  rw [integral_sub (integrable_const 1) (trace_integrable i 2),integral_const,
    probReal_univ,one_smul,haar_trace_moment,h]
  norm_num

theorem haar_even_second (i : Fin 3) : (∫ U,evenWinding i U^2 ∂boundaryHaar)=5/8 := by
  have h2 := (SU2TiltEnergyResponse.moment_values law).2.1
  have h4 := (SU2TiltEnergyResponse.moment_values law).2.2.2.1
  have he : (fun U : State => evenWinding i U^2)=
      (fun U => (1-2*halfTrace (winding U root i)^2)+halfTrace (winding U root i)^4) := by
    funext U; unfold evenWinding; ring
  have his : Integrable (fun U : State => 1-2*halfTrace (winding U root i)^2) boundaryHaar :=
    (integrable_const 1).sub ((trace_integrable i 2).const_mul 2)
  rw [he,integral_add his (trace_integrable i 4),
    integral_sub (integrable_const 1) ((trace_integrable i 2).const_mul 2),integral_const_mul,
    integral_const,probReal_univ,one_smul,haar_trace_moment,haar_trace_moment,h2,h4]
  norm_num

theorem haar_centered_square (i : Fin 3) (a : ℝ) :
    (∫ U : State,(evenWinding i U-a)^2 ∂boundaryHaar)=(a-3/4)^2+1/16 := by
  have hm := haar_even_memLp i
  have hi := hm.integrable (by norm_num)
  have he : (fun U : State => (evenWinding i U-a)^2)=
      (fun U => (evenWinding i U^2-2*a*evenWinding i U)+a^2) := by funext U; ring
  have his : Integrable (fun U : State => evenWinding i U^2-2*a*evenWinding i U) boundaryHaar :=
    hm.integrable_sq.sub (hi.const_mul (2*a))
  rw [he,integral_add his (integrable_const _),
    integral_sub hm.integrable_sq (hi.const_mul (2*a)),integral_const_mul,
    haar_even_second,haar_even_mean,integral_const,probReal_univ,one_smul]
  ring

theorem native_variance_floor (i : Fin 3) :
    g.lower^2/(16*g.normalizer)≤variance (evenWinding i) g.stationary := by
  let a := mean g i
  have hm := (haar_even_memLp i).sub (memLp_const a)
  have hiw : Integrable (fun U : State => g.function U^2*(evenWinding i U-a)^2) boundaryHaar :=
    (PeriodicBoundaryHaarReduction.stationary_integrable_iff g _).mp
      ((even_memLp g i).sub (memLp_const a)).integrable_sq
  have h := integral_mono (hm.integrable_sq.const_mul (g.lower^2)) hiw (fun U =>
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ g.lower_pos.le (g.bounds U).1 2) (sq_nonneg _))
  rw [integral_const_mul] at h
  change g.lower^2*(∫ U : State,(evenWinding i U-a)^2 ∂boundaryHaar)≤
    (∫ U : State,g.function U^2*(evenWinding i U-a)^2 ∂boundaryHaar) at h
  rw [haar_centered_square] at h
  rw [variance_eq_integral (even_measurable i).aemeasurable,g.stationary_integral]
  change _≤(∫ U : State,g.function U^2*(evenWinding i U-a)^2 ∂boundaryHaar)/g.normalizer
  apply (le_div_iff₀ g.normalizer_pos).mpr
  have hs := mul_nonneg (sq_nonneg g.lower) (sq_nonneg (a-3/4))
  have he : g.lower^2/(16*g.normalizer)*g.normalizer=g.lower^2/16 := by
    field_simp [g.normalizer_pos.ne']
  rw [he]
  nlinarith

theorem native_variance_pos (i : Fin 3) : 0<variance (evenWinding i) g.stationary :=
  (div_pos (sq_pos_of_pos g.lower_pos) (mul_pos (by norm_num) g.normalizer_pos)).trans_le
    (native_variance_floor g i)


theorem second_pos (i : Fin 3) : 0<secondMoment g i := by
  have h := native_variance_pos g i
  rw [variance_formula] at h
  nlinarith [sq_nonneg (mean g i)]

theorem vector_mean_zero (i : Fin 3) : (∫ U,vector g i U ∂g.stationary)=0 :=
  (integral_congr_ae (MemLp.coeFn_toLp (centered_memLp g i))).trans (centered_mean_zero g i)

theorem normalized_criterion (i : Fin 3) (c η : ℝ) (hc : 0<c) (hη : 0≤η)
    (hvar : c*secondMoment g i≤variance (evenWinding i) g.stationary)
    (he : (∫ q,energy q^2 ∂tripleLaw g)≤η^2*secondMoment g i) :
    let F : StateL2 g := ‖vector g i‖⁻¹ • vector g i
    ‖F‖=1 ∧ (∫ U,F U ∂g.stationary)=0 ∧
      ‖operator g F-F‖^2≤(2048*η^2+256*η)/c := by
  have hn : 0<‖vector g i‖ := by
    have h := native_variance_pos g i
    rw [← vector_norm] at h
    nlinarith [norm_nonneg (vector g i)]
  dsimp only
  constructor
  · rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hn,inv_mul_cancel₀ hn.ne']
  constructor
  · have h := integral_congr_ae (Lp.coeFn_smul ‖vector g i‖⁻¹ (vector g i))
    rw [h]
    change (∫ U,‖vector g i‖⁻¹ • vector g i U ∂g.stationary)=0
    rw [integral_smul,vector_mean_zero,smul_zero]
  · have heq : operator g (‖vector g i‖⁻¹ • vector g i)-‖vector g i‖⁻¹ • vector g i=
        ‖vector g i‖⁻¹ • (operator g (vector g i)-vector g i) := by rw [map_smul,smul_sub]
    rw [heq,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hn,mul_pow]
    have h := mul_le_mul_of_nonneg_left (relative_residual g i c η hc hη hvar he)
      (sq_nonneg ‖vector g i‖⁻¹)
    have hh : ‖vector g i‖⁻¹^2*(((2048*η^2+256*η)/c)*‖vector g i‖^2)=
        (2048*η^2+256*η)/c := by field_simp
    rw [hh] at h
    exact h

theorem normalized_scale_criterion (hb : 16777216≤β) (i : Fin 3) (c η : ℝ)
    (hc : 0<c) (hη : 0≤η)
    (hvar : c*secondMoment g i≤variance (evenWinding i) g.stationary)
    (he : 8*ratioConstant/β^2≤η^2*secondMoment g i) :
    let F : StateL2 g := ‖vector g i‖⁻¹ • vector g i
    ‖F‖=1 ∧ (∫ U,F U ∂g.stationary)=0 ∧
      ‖operator g F-F‖^2≤(2048*η^2+256*η)/c :=
  normalized_criterion g i c η hc hη hvar ((energy_square_uniform β hb g).trans he)

end OperatorDerivativeRewrite.Foundation.PeriodicEvenWindingCriterion
