import Foundation.SU2SevenLinkVacuum
import Foundation.HilbertRepresentation
import Foundation.SelfAdjointContractionIteration
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosedProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Actual stationary seven-link L2 transfer, built from the two marginals of
its genuine edge law. The existing Hilbert adjoint construction is reused. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.SU2SevenLinkL2Transfer
open SU2SevenLinkTransfer SU2SevenLinkGroundTransform

private instance su2_secondCountable : SecondCountableTopology QuaternionSU2Representation.SU2 := by
  letI : SecondCountableTopology (Quaternion ℝ) :=
    Quaternion.linearIsometryEquivTuple.toHomeomorph.secondCountableTopology
  exact QuaternionSU2Representation.homeomorph.symm.secondCountableTopology
private instance state_secondCountable : SecondCountableTopology State := by infer_instance
private instance state_borel : BorelSpace State := by infer_instance

variable {β t : ℝ} (d : GroundData β t)
private instance stationary_probability : IsProbabilityMeasure d.stationary := d.stationary_probability
private instance kernel_markov : IsMarkovKernel d.kernel := d.kernel_markov

def edgeLaw : Measure (State × State) := d.stationary ⊗ₘ d.kernel
private instance edge_probability : IsProbabilityMeasure (edgeLaw d) := by unfold edgeLaw; infer_instance

private theorem joint_integrable (f g : State → ℝ) (hf : Measurable f) (hg : Measurable g)
    (B C : ℝ) (hb : ∀ s,|f s| ≤ B) (hc : ∀ s,|g s| ≤ C) :
    Integrable (fun p : State × State => f p.1*g p.2) (edgeLaw d) := by
  apply Integrable.of_bound ((hf.comp measurable_fst).mul (hg.comp measurable_snd)).aestronglyMeasurable
    (|B| * |C|)
  filter_upwards with p
  change ‖f p.1*g p.2‖ ≤ |B| * |C|
  rw [Real.norm_eq_abs,abs_mul]
  exact mul_le_mul ((hb p.1).trans (le_abs_self B)) ((hc p.2).trans (le_abs_self C))
    (abs_nonneg _) (abs_nonneg _)

theorem edge_pairing (f g : State → ℝ) (hf : Measurable f) (hg : Measurable g)
    (B C : ℝ) (hb : ∀ s,|f s| ≤ B) (hc : ∀ s,|g s| ≤ C) :
    (∫ p,f p.1*g p.2 ∂edgeLaw d)=∫ s,f s*(∫ r,g r ∂d.kernel s) ∂d.stationary := by
  change (∫ p,f p.1*g p.2 ∂(d.stationary ⊗ₘ d.kernel))=_
  rw [Measure.integral_compProd (joint_integrable d f g hf hg B C hb hc)]
  apply integral_congr_ae
  filter_upwards with s
  exact integral_const_mul (f s) g

theorem edge_swap : (edgeLaw d).map Prod.swap=edgeLaw d := by
  apply Measure.ext_of_integral_mul_boundedContinuousFunction
  intro f g
  have hf := f.continuous.measurable
  have hg := g.continuous.measurable
  have hm : Measurable (fun p : State × State => f p.1*g p.2) :=
    (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  rw [integral_map measurable_swap.aemeasurable hm.aestronglyMeasurable]
  change (∫ p,f p.2*g p.1 ∂edgeLaw d)=∫ p,f p.1*g p.2 ∂edgeLaw d
  have he : (fun p : State × State => f p.2*g p.1)=(fun p => g p.1*f p.2) :=
    funext (fun p => mul_comm _ _)
  rw [he,edge_pairing d g f hg hf ‖g‖ ‖f‖
    (fun s => by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm s)
    (fun s => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm s),
    edge_pairing d f g hf hg ‖f‖ ‖g‖
      (fun s => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm s)
      (fun s => by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm s)]
  exact d.stationary_reversible g f hg hf ‖g‖ ‖f‖
    (fun s => by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm s)
    (fun s => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm s)

theorem left_preserving : MeasurePreserving Prod.fst (edgeLaw d) d.stationary :=
  ⟨measurable_fst,Measure.fst_compProd d.stationary d.kernel⟩

theorem right_preserving : MeasurePreserving Prod.snd (edgeLaw d) d.stationary := by
  have hs : MeasurePreserving Prod.swap (edgeLaw d) (edgeLaw d) := ⟨measurable_swap,edge_swap d⟩
  exact (left_preserving d).comp hs

abbrev StateL2 := Lp ℝ 2 d.stationary
abbrev EdgeL2 := Lp ℝ 2 (edgeLaw d)

def leftEmbedding : StateL2 d →ₗᵢ[ℝ] EdgeL2 d :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.fst (left_preserving d)
def rightEmbedding : StateL2 d →ₗᵢ[ℝ] EdgeL2 d :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.snd (right_preserving d)

def operator : StateL2 d →L[ℝ] StateL2 d :=
  (HilbertRepresentation.predictableAdjoint (leftEmbedding d)).comp (rightEmbedding d).toContinuousLinearMap

theorem operator_pairing (f g : StateL2 d) : inner ℝ (operator d f) g=
    ∫ p,g p.1*f p.2 ∂edgeLaw d := by
  rw [show inner ℝ (operator d f) g=inner ℝ (rightEmbedding d f) (leftEmbedding d g) from
    HilbertRepresentation.predictableAdjoint_pairing (leftEmbedding d) (rightEmbedding d f) g]
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_compMeasurePreserving f (right_preserving d),
    Lp.coeFn_compMeasurePreserving g (left_preserving d)] with p hf hg
  change rightEmbedding d f p=f p.2 at hf
  change leftEmbedding d g p=g p.1 at hg
  change inner ℝ (rightEmbedding d f p) (leftEmbedding d g p)=_
  rw [hf,hg]
  rfl

theorem operator_contraction (f : StateL2 d) : ‖operator d f‖ ≤ ‖f‖ := by
  have he := HilbertRepresentation.representation_norm_decomposition (leftEmbedding d) (rightEmbedding d f)
  rw [(rightEmbedding d).norm_map] at he
  change ‖f‖^2=‖operator d f‖^2+_ at he
  nlinarith [sq_nonneg (‖rightEmbedding d f-
    HilbertRepresentation.representationProjection (leftEmbedding d) (rightEmbedding d f)‖),
    norm_nonneg f,norm_nonneg (operator d f)]

theorem operator_symmetric (f g : StateL2 d) : inner ℝ (operator d f) g=inner ℝ f (operator d g) := by
  rw [← real_inner_comm f (operator d g),operator_pairing,operator_pairing]
  have hm : Measurable (fun p : State × State => g p.1*f p.2) :=
    ((Lp.stronglyMeasurable g).measurable.comp measurable_fst).mul
      ((Lp.stronglyMeasurable f).measurable.comp measurable_snd)
  have he := integral_map (μ := edgeLaw d) measurable_swap.aemeasurable hm.aestronglyMeasurable
  rw [edge_swap d] at he
  simpa [mul_comm] using he


theorem operator_selfadjoint : (operator d).adjoint=operator d :=
  ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr (operator_symmetric d)).symm

def transfer (f : State → ℝ) (s : State) : ℝ := ∫ r,f r ∂d.kernel s

theorem operator_kernel_pairing (f g : StateL2 d) :
    inner ℝ (operator d f) g=∫ s,g s*transfer d f s ∂d.stationary := by
  have hi : Integrable (fun p : State × State => g p.1*f p.2) (edgeLaw d) := by
    apply (L2.integrable_inner (𝕜 := ℝ) (rightEmbedding d f) (leftEmbedding d g)).congr
    filter_upwards [Lp.coeFn_compMeasurePreserving f (right_preserving d),
      Lp.coeFn_compMeasurePreserving g (left_preserving d)] with p hf hg
    change rightEmbedding d f p=f p.2 at hf
    change leftEmbedding d g p=g p.1 at hg
    change inner ℝ (rightEmbedding d f p) (leftEmbedding d g p)=_
    rw [hf,hg]
    rfl
  rw [operator_pairing]
  change (∫ p,g p.1*f p.2 ∂(d.stationary ⊗ₘ d.kernel))=_
  rw [Measure.integral_compProd hi]
  apply integral_congr_ae
  filter_upwards with s
  simp only [transfer,integral_const_mul]

theorem transfer_measurable (f : State → ℝ) (hf : Measurable f) : Measurable (transfer d f) :=
  (hf.stronglyMeasurable.integral_kernel).measurable

theorem transfer_bound (f : State → ℝ) (B : ℝ) (hb : ∀ s,|f s| ≤ B) (s : State) :
    |transfer d f s| ≤ B := by
  have he := norm_integral_le_of_norm_le_const (μ := d.kernel s) (f := f) (C := B)
    (Filter.Eventually.of_forall fun r => by simpa only [Real.norm_eq_abs] using hb r)
  simpa [transfer,Real.norm_eq_abs] using he

theorem transfer_memLp (f : State → ℝ) (hf : Measurable f) (B : ℝ) (hb : ∀ s,|f s| ≤ B) :
    MemLp (transfer d f) 2 d.stationary :=
  MemLp.of_bound (transfer_measurable d f hf).aestronglyMeasurable B
    (Filter.Eventually.of_forall fun s => by simpa only [Real.norm_eq_abs] using transfer_bound d f B hb s)

def probe (A B : ℝ) : StateL2 d := (d.observable_memLp A B).toLp (d.observable A B)

theorem probe_mean (A B : ℝ) (heven : ∀ s,d.function (SU2SevenLinkParity.flip s)=d.function s) :
    (∫ s,probe d A B s ∂d.stationary)=0 := by
  unfold probe
  rw [integral_congr_ae (MemLp.coeFn_toLp (d.observable_memLp A B))]
  exact d.observable_centered A B heven

theorem probe_square (A B : ℝ) : inner ℝ (probe d A B) (probe d A B)=
    ∫ s,(d.observable A B s)^2 ∂d.stationary := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (d.observable_memLp A B)] with s hs
  change probe d A B s=d.observable A B s at hs
  rw [hs]
  simp [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

theorem probe_lag (A B : ℝ) : inner ℝ (operator d (probe d A B)) (probe d A B)=
    ∫ s,d.observable A B s*(∫ r,d.observable A B r ∂d.kernel s) ∂d.stationary := by
  rw [operator_pairing]
  have hl := (left_preserving d).quasiMeasurePreserving.ae_eq_comp
    (MemLp.coeFn_toLp (d.observable_memLp A B))
  have hr := (right_preserving d).quasiMeasurePreserving.ae_eq_comp
    (MemLp.coeFn_toLp (d.observable_memLp A B))
  calc
    _ = ∫ p,d.observable A B p.1*d.observable A B p.2 ∂edgeLaw d := by
      apply integral_congr_ae
      filter_upwards [hl,hr] with p hp hq
      change probe d A B p.1=d.observable A B p.1 at hp
      change probe d A B p.2=d.observable A B p.2 at hq
      rw [hp,hq]
    _ = _ := edge_pairing d _ _ (d.observable_measurable A B) (d.observable_measurable A B)
      _ _ (d.observable_bound A B) (d.observable_bound A B)


/-- Exact native-kernel agreement on bounded measurable probes, rather than
only an abstract quadratic-form representation. -/
theorem operator_toLp (f : State → ℝ) (hmem : MemLp f 2 d.stationary) (hf : Measurable f)
    (B : ℝ) (hb : ∀ s,|f s| ≤ B) :
    operator d (hmem.toLp f)=(transfer_memLp d f hf B hb).toLp (transfer d f) := by
  let F := hmem.toLp f
  let hP := transfer_memLp d f hf B hb
  let PF := hP.toLp (transfer d f)
  change operator d F=PF
  apply ext_inner_right ℝ
  intro g
  have hi : Integrable (fun p : State × State => g p.1*F p.2) (edgeLaw d) := by
    apply (L2.integrable_inner (𝕜 := ℝ) (rightEmbedding d F) (leftEmbedding d g)).congr
    filter_upwards [Lp.coeFn_compMeasurePreserving F (right_preserving d),
      Lp.coeFn_compMeasurePreserving g (left_preserving d)] with p hp hq
    change rightEmbedding d F p=F p.2 at hp
    change leftEmbedding d g p=g p.1 at hq
    change inner ℝ (rightEmbedding d F p) (leftEmbedding d g p)=_
    rw [hp,hq]
    rfl
  have hr := (right_preserving d).quasiMeasurePreserving.ae_eq_comp (MemLp.coeFn_toLp hmem)
  have hp : (fun p : State × State => g p.1*F p.2) =ᵐ[edgeLaw d]
      (fun p => g p.1*f p.2) := by
    filter_upwards [hr] with p hh
    change F p.2=f p.2 at hh
    rw [hh]
  have hi' := hi.congr hp
  rw [operator_pairing,L2.inner_def,integral_congr_ae hp]
  change (∫ p,g p.1*f p.2 ∂(d.stationary ⊗ₘ d.kernel))=_
  rw [Measure.integral_compProd hi']
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hP] with s hs
  change PF s=transfer d f s at hs
  rw [hs]
  change (∫ r,g s*f r ∂d.kernel s)=g s*transfer d f s
  rw [integral_const_mul]
  rfl

def nativeSteps : ℕ → (State → ℝ) → State → ℝ
  | 0,f => f
  | n+1,f => transfer d (nativeSteps n f)

theorem nativeSteps_measurable (n : ℕ) (f : State → ℝ) (hf : Measurable f) :
    Measurable (nativeSteps d n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact transfer_measurable d _ ih

theorem nativeSteps_bound (n : ℕ) (f : State → ℝ) (B : ℝ) (hb : ∀ s,|f s| ≤ B) (s : State) :
    |nativeSteps d n f s| ≤ B := by
  induction n generalizing s with
  | zero => exact hb s
  | succ n ih => exact transfer_bound d _ B ih s

theorem nativeSteps_memLp (n : ℕ) (f : State → ℝ) (hf : Measurable f) (B : ℝ)
    (hb : ∀ s,|f s| ≤ B) : MemLp (nativeSteps d n f) 2 d.stationary :=
  MemLp.of_bound (nativeSteps_measurable d n f hf).aestronglyMeasurable B
    (Filter.Eventually.of_forall fun s => by
      simpa only [Real.norm_eq_abs] using nativeSteps_bound d n f B hb s)

/-- EVERY operator iterate is the actual iterated Markov integral class on
these probes. The displayed MemLp input is justified by boundedness. -/
theorem steps_toLp (n : ℕ) (f : State → ℝ) (hmem : MemLp f 2 d.stationary)
    (hf : Measurable f) (B : ℝ) (hb : ∀ s,|f s| ≤ B) :
    SelfAdjointContractionIteration.steps (operator d) n (hmem.toLp f)=
      (nativeSteps_memLp d n f hf B hb).toLp (nativeSteps d n f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change operator d (SelfAdjointContractionIteration.steps (operator d) n (hmem.toLp f))=_
    rw [ih]
    exact operator_toLp d (nativeSteps d n f) _ (nativeSteps_measurable d n f hf)
      B (nativeSteps_bound d n f B hb)


theorem steps_pairing (n : ℕ) (f : State → ℝ) (hmem : MemLp f 2 d.stationary)
    (hf : Measurable f) (B : ℝ) (hb : ∀ s,|f s| ≤ B) :
    inner ℝ (SelfAdjointContractionIteration.steps (operator d) n (hmem.toLp f)) (hmem.toLp f)=
      ∫ s,f s*nativeSteps d n f s ∂d.stationary := by
  rw [steps_toLp d n f hmem hf B hb,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (nativeSteps_memLp d n f hf B hb),
    MemLp.coeFn_toLp hmem] with s hs hf'
  rw [hs,hf']
  rfl

theorem nativeSteps_gauge (n : ℕ) (f : State → ℝ) (hf : Measurable f)
    (hfg : ∀ (g : Fin 6 → QuaternionSU2Representation.SU2) s,f (gaugeAction g s)=f s)
    (g : Fin 6 → QuaternionSU2Representation.SU2) (s : State) :
    nativeSteps d n f (gaugeAction g s)=nativeSteps d n f s := by
  induction n generalizing s with
  | zero => exact hfg g s
  | succ n ih =>
    change (∫ r,nativeSteps d n f r ∂d.kernel (gaugeAction g s))=_
    rw [SU2SevenLinkVacuum.kernel_integral_gauge d g _ (nativeSteps_measurable d n f hf)]
    simp_rw [ih]
    rfl

end OperatorDerivativeRewrite.Foundation.SU2SevenLinkL2Transfer
