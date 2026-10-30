import Foundation.PeriodicLoopVariation
import Foundation.PeriodicCenteredHolonomy
/-! Native periodic stationary transfer quasimodes and finite-iteration obstructions.
All laws and operator domains are the actual verified ground-transform objects.
No continuum or infinite-volume mass-gap conclusion is asserted. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicTransferVariation
open PeriodicTemporalSlab PeriodicSlabGround PeriodicSlabL2 PeriodicSlabJoint
open PeriodicTemporalConcentration PeriodicCenteredHolonomy
variable {beta : ℝ} (g : GroundData beta)
private instance stationary_probability : IsProbabilityMeasure g.stationary := g.stationary_probability
private instance joint_probability : IsProbabilityMeasure (tripleLaw g) := triple_probability g

theorem operator_residual (F : StateL2 g) :
    ‖operator g F-F‖ ≤ ‖rightEmbedding g F-leftEmbedding g F‖ := by
  let L := leftEmbedding g
  let R := rightEmbedding g
  have he : operator g F-F=HilbertRepresentation.predictableAdjoint L (R F-L F) := by
    rw [map_sub,HilbertRepresentation.predictableAdjoint_isometry_apply]
    rfl
  rw [he]
  have hd := HilbertRepresentation.representation_norm_decomposition L (R F-L F)
  nlinarith [norm_nonneg (HilbertRepresentation.predictableAdjoint L (R F-L F)),
    norm_nonneg (R F-L F),sq_nonneg (‖R F-L F-
      HilbertRepresentation.representationProjection L (R F-L F)‖)]

theorem edge_norm_square (f : State → ℝ) (hf : MemLp f 2 g.stationary) :
    ‖rightEmbedding g (hf.toLp f)-leftEmbedding g (hf.toLp f)‖^2=
      ∫ p : State × State,(f p.2-f p.1)^2 ∂edgeLaw g := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  have hr := (right_preserving g).quasiMeasurePreserving.ae_eq_comp (MemLp.coeFn_toLp hf)
  have hl := (left_preserving g).quasiMeasurePreserving.ae_eq_comp (MemLp.coeFn_toLp hf)
  filter_upwards [Lp.coeFn_sub (rightEmbedding g (hf.toLp f)) (leftEmbedding g (hf.toLp f)),
    Lp.coeFn_compMeasurePreserving (hf.toLp f) (right_preserving g),
    Lp.coeFn_compMeasurePreserving (hf.toLp f) (left_preserving g),hr,hl] with p hsub hr0 hl0 hr1 hl1
  change rightEmbedding g (hf.toLp f) p=(hf.toLp f) p.2 at hr0
  change leftEmbedding g (hf.toLp f) p=(hf.toLp f) p.1 at hl0
  change (hf.toLp f) p.2=f p.2 at hr1
  change (hf.toLp f) p.1=f p.1 at hl1
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hr0,hl0,hr1,hl1]
  simp [pow_two]

theorem variation_bound (f : State → ℝ) (hf : MemLp f 2 g.stationary)
    (hm : Measurable f) (C : ℝ)
    (h : ∀ q : Triple,(f q.1.2-f q.1.1)^2 ≤ C*temporalEnergy q) :
    ‖operator g (hf.toLp f)-hf.toLp f‖^2 ≤ C*(∫ q,temporalEnergy q ∂tripleLaw g) := by
  have hres := operator_residual g (hf.toLp f)
  have hsq := mul_self_le_mul_self (norm_nonneg _) hres
  have hnorm := edge_norm_square g f hf
  have hm2 : Measurable (fun p : State × State => (f p.2-f p.1)^2) :=
    ((hm.comp measurable_snd).sub (hm.comp measurable_fst)).pow_const 2
  have hp : (∫ q : Triple,(f q.1.2-f q.1.1)^2 ∂tripleLaw g)=
      ∫ p : State × State,(f p.2-f p.1)^2 ∂edgeLaw g := by
    have he := integral_map (μ := tripleLaw g) (φ := (Prod.fst : Triple → State × State)) measurable_fst.aemeasurable hm2.aestronglyMeasurable
    rw [(pair_preserving g).map_eq] at he
    exact he.symm
  have hi := (temporal_integrable g).const_mul C
  have hle : (∫ q : Triple,(f q.1.2-f q.1.1)^2 ∂tripleLaw g) ≤
      ∫ q,C*temporalEnergy q ∂tripleLaw g := by
    apply integral_mono_of_nonneg
    · exact ae_of_all _ (fun _ => sq_nonneg _)
    · exact hi
    · exact ae_of_all _ h
  rw [integral_const_mul] at hle
  change (∫ q : Triple,(f q.1.2-f q.1.1)^2 ∂tripleLaw g)=_ at hp
  nlinarith



theorem state_norm_square (f : State → ℝ) (hf : MemLp f 2 g.stationary) :
    ‖hf.toLp f‖^2=∫ U,f U^2 ∂g.stationary := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hf] with U hU
  rw [hU]
  simp [pow_two]

theorem eventual_trial : ∀ᶠ beta : ℝ in atTop,∀ g : GroundData beta,
    ∃ f : State → ℝ,Measurable f ∧ ∃ hf : MemLp f 2 g.stationary,
      (∫ U,f U ∂g.stationary)=0 ∧ (1/24 : ℝ) ≤ ‖hf.toLp f‖^2 ∧
      ‖operator g (hf.toLp f)-hf.toLp f‖^2 ≤ 128*(∫ q,temporalEnergy q ∂tripleLaw g) := by
  filter_upwards [eventual_variance_channel] with beta hb
  intro g
  have hfirst := variation_bound g first (first_memLp g) first_measurable 128 (by
    intro q
    have h := PeriodicLoopVariation.winding_trace_change q.1.1 q.1.2 q.2 origin 0
    change (first q.1.1-first q.1.2)^2 ≤ 32*temporalEnergy q at h
    nlinarith [(temporal_bounds q).1])
  have hsecond := variation_bound g second (second_memLp g) second_measurable 128 (by
    intro q
    have h := PeriodicLoopVariation.winding_trace_change q.1.1 q.1.2 q.2 origin 1
    change (second q.1.1-second q.1.2)^2 ≤ 32*temporalEnergy q at h
    nlinarith [(temporal_bounds q).1])
  have hmixed := variation_bound g mixed (mixed_memLp g) mixed_measurable 128 (by
    intro q
    have h := PeriodicLoopVariation.product_trace_change q.1.1 q.1.2 q.2 origin 0 1
    change (mixed q.1.1-mixed q.1.2)^2 ≤ 128*temporalEnergy q at h
    nlinarith)
  rcases hb g with h|h|h
  · refine ⟨first,first_measurable,first_memLp g,first_mean_zero g,?_,hfirst⟩
    rwa [state_norm_square,← first_variance]
  · refine ⟨second,second_measurable,second_memLp g,second_mean_zero g,?_,hsecond⟩
    rwa [state_norm_square,← second_variance]
  · refine ⟨mixed,mixed_measurable,mixed_memLp g,mixed_mean_zero g,?_,hmixed⟩
    rwa [state_norm_square,← mixed_variance]


theorem eventual_quasimode (eps : ℝ) (he : 0 < eps) :
    ∀ᶠ beta : ℝ in atTop,∀ g : GroundData beta,∃ F : StateL2 g,
      ‖F‖=1 ∧ (∫ U,F U ∂g.stationary)=0 ∧ ‖operator g F-F‖ < eps := by
  filter_upwards [eventual_trial,energy_small (eps^2/12288) (by positivity)] with beta ht hs
  intro g
  obtain ⟨f,hm,hf,hmean,hnorm,hres⟩ := ht g
  let F : StateL2 g := hf.toLp f
  have hF : 0 < ‖F‖ := by
    change (1/24 : ℝ) ≤ ‖F‖^2 at hnorm
    nlinarith [norm_nonneg F]
  have hFm : (∫ U,F U ∂g.stationary)=0 :=
    (integral_congr_ae (MemLp.coeFn_toLp hf)).trans hmean
  have hT : (∫ q,temporalEnergy q ∂tripleLaw g) ≤ eps^2/12288 :=
    (integral_mono (temporal_integrable g) (energy_integrable g) temporal_le_energy).trans (hs g)
  let G : StateL2 g := ‖F‖⁻¹ • F
  have hinv : ‖F‖⁻¹*‖F‖=1 := inv_mul_cancel₀ (ne_of_gt hF)
  have hG : ‖G‖=1 := by
    dsimp [G]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hF),hinv]
  refine ⟨G,hG,?_,?_⟩
  · rw [integral_congr_ae (Lp.coeFn_smul ‖F‖⁻¹ F)]
    simp only [Pi.smul_apply]
    rw [integral_smul,hFm,smul_zero]
  · have hlin : operator g G-G=‖F‖⁻¹ • (operator g F-F) := by
      dsimp [G]
      rw [map_smul,smul_sub]
    rw [hlin,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hF)]
    have hresF : ‖operator g F-F‖^2 ≤ eps^2/96 := by
      change ‖operator g F-F‖^2 ≤ _ at hres
      linarith
    have hrel : ‖operator g F-F‖^2 ≤ (eps^2/4)*‖F‖^2 := by
      have hmul := mul_le_mul_of_nonneg_left hnorm (by positivity : 0 ≤ eps^2/4)
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hrel (sq_nonneg (‖F‖⁻¹))
    have hinv2 : ‖F‖⁻¹^2*‖F‖^2=1 := by nlinarith [sq_nonneg (‖F‖⁻¹*‖F‖-1)]
    have hbound : (‖F‖⁻¹*‖operator g F-F‖)^2 ≤ eps^2/4 := by
      calc
        _ = ‖F‖⁻¹^2*‖operator g F-F‖^2 := by ring
        _ ≤ ‖F‖⁻¹^2*((eps^2/4)*‖F‖^2) := hmul
        _ = eps^2/4 := by nlinarith [hinv2]
    nlinarith [mul_nonneg (inv_nonneg.mpr (norm_nonneg F)) (norm_nonneg (operator g F-F))]


theorem eventual_no_uniform_contraction (q : ℝ) (hq : q < 1) :
    ∀ᶠ beta : ℝ in atTop,∀ g : GroundData beta,
      ¬ ∀ F : StateL2 g,(∫ U,F U ∂g.stationary)=0 → ‖operator g F‖ ≤ q*‖F‖ := by
  filter_upwards [eventual_quasimode ((1-q)/2) (by linarith)] with beta hb
  intro g hc
  obtain ⟨F,hF,hm,hr⟩ := hb g
  have hp := hc F hm
  have ht : ‖F‖ ≤ ‖operator g F‖+‖operator g F-F‖ := by
    calc
      ‖F‖=‖operator g F-(operator g F-F)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  rw [hF] at hp ht
  linarith

theorem iterate_residual (n : ℕ) (F : StateL2 g) :
    ‖(operator g)^[n] F-F‖ ≤ (n : ℝ)*‖operator g F-F‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have he : operator g ((operator g)^[n] F)-F=
        operator g ((operator g)^[n] F-F)+(operator g F-F) := by rw [map_sub]; abel
    have hc : ‖operator g ((operator g)^[n] F-F)‖ ≤ ‖(operator g)^[n] F-F‖ :=
      PeriodicSlabL2.operator_contraction g ((operator g)^[n] F-F)
    rw [he]
    calc
      _ ≤ ‖operator g ((operator g)^[n] F-F)‖+‖operator g F-F‖ := norm_add_le _ _
      _ ≤ ‖(operator g)^[n] F-F‖+‖operator g F-F‖ :=
        add_le_add hc (le_refl ‖operator g F-F‖)
      _ ≤ (n : ℝ)*‖operator g F-F‖+‖operator g F-F‖ := add_le_add ih (le_refl ‖operator g F-F‖)
      _ = _ := by rw [Nat.cast_succ,add_mul,one_mul]

theorem iteration_contraction_requires_distance (n : ℕ) (F : StateL2 g) (q : ℝ)
    (hF : ‖F‖=1) (hq : ‖(operator g)^[n] F‖ ≤ q) :
    1-q ≤ (n : ℝ)*‖operator g F-F‖ := by
  have ht : ‖F‖ ≤ ‖(operator g)^[n] F‖+‖(operator g)^[n] F-F‖ := by
    calc
      ‖F‖=‖(operator g)^[n] F-((operator g)^[n] F-F)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  rw [hF] at ht
  linarith [iterate_residual g n F]


theorem eventual_no_bounded_iteration_contraction (N : ℕ) (q : ℝ) (hq : q < 1) :
    ∀ᶠ beta : ℝ in atTop,∀ g : GroundData beta,∀ n : ℕ,n ≤ N →
      ¬ ∀ F : StateL2 g,(∫ U,F U ∂g.stationary)=0 → ‖(operator g)^[n] F‖ ≤ q*‖F‖ := by
  have hN : 0 < (N : ℝ)+1 := by positivity
  have hpos : 0 < 1-q := by linarith
  filter_upwards [eventual_quasimode ((1-q)/(2*((N : ℝ)+1))) (by positivity)] with beta hb
  intro g n hn hc
  obtain ⟨F,hF,hm,hr⟩ := hb g
  have hp := hc F hm
  have hd := iteration_contraction_requires_distance g n F q hF (by simpa only [hF,mul_one] using hp)
  have hnr : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
  have hmN := mul_le_mul_of_nonneg_right hnr (norm_nonneg (operator g F-F))
  have hx := (lt_div_iff₀ (by positivity : 0 < 2*((N : ℝ)+1))).mp hr
  nlinarith [norm_nonneg (operator g F-F)]
end OperatorDerivativeRewrite.Foundation.PeriodicTransferVariation
