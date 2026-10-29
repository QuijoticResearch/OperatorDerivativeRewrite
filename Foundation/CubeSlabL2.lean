import Foundation.CubeSlabGround
import Foundation.HilbertRepresentation
import Foundation.SelfAdjointContractionIteration
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosedProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Actual stationary homogeneous Wilson slab L2 transfer, built from the two marginals of
its genuine edge law. The existing Hilbert adjoint construction is reused. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.CubeSlabL2
open CubeTemporalSlab CubeSlabGround

private instance su2_secondCountable : SecondCountableTopology QuaternionSU2Representation.SU2 := by
  letI : SecondCountableTopology (Quaternion ℝ) :=
    Quaternion.linearIsometryEquivTuple.toHomeomorph.secondCountableTopology
  exact QuaternionSU2Representation.homeomorph.symm.secondCountableTopology
private instance state_secondCountable : SecondCountableTopology State := by infer_instance
private instance state_borel : BorelSpace State := by infer_instance

variable {beta : ℝ} (d : GroundData beta)
private instance stationary_probability : IsProbabilityMeasure d.stationary := d.stationary_probability
private instance kernel_markov : IsMarkovKernel d.transition := d.transition_markov

def edgeLaw : Measure (State × State) := d.stationary ⊗ₘ d.transition
private instance edge_probability : IsProbabilityMeasure (edgeLaw d) := by unfold edgeLaw; infer_instance

private theorem joint_integrable (f g : State → ℝ) (hf : Measurable f) (hg : Measurable g)
    (B C : ℝ) (hb : ∀ s, |f s| ≤ B) (hc : ∀ s, |g s| ≤ C) :
    Integrable (fun p : State × State => f p.1*g p.2) (edgeLaw d) := by
  apply Integrable.of_bound ((hf.comp measurable_fst).mul (hg.comp measurable_snd)).aestronglyMeasurable
    (|B| * |C|)
  filter_upwards with p
  change ‖f p.1*g p.2‖ ≤ |B| * |C|
  rw [Real.norm_eq_abs,abs_mul]
  exact mul_le_mul ((hb p.1).trans (le_abs_self B)) ((hc p.2).trans (le_abs_self C))
    (abs_nonneg _) (abs_nonneg _)

theorem edge_pairing (f g : State → ℝ) (hf : Measurable f) (hg : Measurable g)
    (B C : ℝ) (hb : ∀ s, |f s| ≤ B) (hc : ∀ s, |g s| ≤ C) :
    (∫ p,f p.1*g p.2 ∂edgeLaw d)=∫ s,f s*(∫ r,g r ∂d.transition s) ∂d.stationary := by
  change (∫ p,f p.1*g p.2 ∂(d.stationary ⊗ₘ d.transition))=_
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
  ⟨measurable_fst,Measure.fst_compProd d.stationary d.transition⟩

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

def transfer (f : State → ℝ) (s : State) : ℝ := ∫ r,f r ∂d.transition s

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
  change (∫ p,g p.1*f p.2 ∂(d.stationary ⊗ₘ d.transition))=_
  rw [Measure.integral_compProd hi]
  apply integral_congr_ae
  filter_upwards with s
  simp only [transfer,integral_const_mul]

theorem transfer_measurable (f : State → ℝ) (hf : Measurable f) : Measurable (transfer d f) :=
  (hf.stronglyMeasurable.integral_kernel).measurable

theorem transfer_bound (f : State → ℝ) (B : ℝ) (hb : ∀ s, |f s| ≤ B) (s : State) :
    |transfer d f s| ≤ B := by
  have he := norm_integral_le_of_norm_le_const (μ := d.transition s) (f := f) (C := B)
    (Filter.Eventually.of_forall fun r => by simpa only [Real.norm_eq_abs] using hb r)
  simpa [transfer,Real.norm_eq_abs] using he

theorem transfer_memLp (f : State → ℝ) (hf : Measurable f) (B : ℝ) (hb : ∀ s, |f s| ≤ B) :
    MemLp (transfer d f) 2 d.stationary :=
  MemLp.of_bound (transfer_measurable d f hf).aestronglyMeasurable B
    (Filter.Eventually.of_forall fun s => by simpa only [Real.norm_eq_abs] using transfer_bound d f B hb s)

/-- Exact native-kernel agreement on bounded measurable probes, rather than
only an abstract quadratic-form representation. -/
theorem operator_toLp (f : State → ℝ) (hmem : MemLp f 2 d.stationary) (hf : Measurable f)
    (B : ℝ) (hb : ∀ s, |f s| ≤ B) :
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
  change (∫ p,g p.1*f p.2 ∂(d.stationary ⊗ₘ d.transition))=_
  rw [Measure.integral_compProd hi']
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hP] with s hs
  change PF s=transfer d f s at hs
  rw [hs]
  change (∫ r,g s*f r ∂d.transition s)=g s*transfer d f s
  rw [integral_const_mul]
  rfl

/-- Gauge symmetry of the actual probability transition, not a postulated quotient. -/
theorem transition_source_gauge (a : Gauge) (U : State) :
    d.transition (gaugeAction a U)=d.transition U := by
  rw [d.transition_apply,d.transition_apply]
  simp_rw [d.density_gauge_left]

/-- Every literal one-step output has a pointwise gauge-invariant representative. -/
theorem transfer_source_gauge (f : State → ℝ) (a : Gauge) (U : State) :
    transfer d f (gaugeAction a U)=transfer d f U := by
  unfold transfer
  rw [transition_source_gauge]

/-- A nonzero native eigenvalue cannot have a pointwise gauge-variant mode.
This concerns the displayed native equation; no arbitrary L2 representative is assumed. -/
theorem native_eigen_invariant (f : State → ℝ) (r : ℝ) (hr : r ≠ 0)
    (he : ∀ U, transfer d f U = r * f U) (a : Gauge) (U : State) :
    f (gaugeAction a U)=f U := by
  have h := transfer_source_gauge d f a U
  rw [he,he] at h
  exact mul_left_cancel₀ hr h

/-- A concrete raw link trace fails the actual pointwise nonzero-eigenmode equation.
This does not identify an arbitrary almost-everywhere L2 eigenrepresentative. -/
theorem linkTrace_not_native_eigen (e : SpatialEdge) (r : ℝ) (hr : r ≠ 0) :
    ¬ (∀ U, transfer d (fun V => QuaternionSU2Representation.halfTrace (V e)) U=
      r*QuaternionSU2Representation.halfTrace (U e)) := by
  classical
  intro he
  let a : Gauge := fun v => if v=e.val.1 then SU2StapleExtremes.minusOne else 1
  have hv : shift e.val.1 e.val.2 ≠ e.val.1 := by
    intro h
    have hh := congrFun h e.val.2
    simp only [shift,Function.update_self] at hh
    rw [e.property] at hh
    norm_num at hh
  have h := native_eigen_invariant d _ r hr he a 1
  simp only [gaugeAction,Pi.one_apply,a,ite_true,ite_eq_right hv,mul_one,inv_one] at h
  rw [SU2OpenLinkGaugeObstruction.halfTrace_minusOne,
    SU2OpenLinkGaugeObstruction.halfTrace_one] at h
  norm_num at h


/-- Coordinatewise Haar-preserving boundary gauge equivalence. -/
def boundaryGaugeEquiv (a : Gauge) : State ≃ᵐ State :=
  MeasurableEquiv.piCongrRight (fun e =>
    (MeasurableEquiv.mulLeft (a e.val.1)).trans
      (MeasurableEquiv.mulRight ((a (shift e.val.1 e.val.2))⁻¹)))

theorem boundaryGaugeEquiv_apply (a : Gauge) (U : State) :
    boundaryGaugeEquiv a U=gaugeAction a U := rfl

private theorem haar_sandwich (A B : QuaternionSU2Representation.SU2) :
    MeasurePreserving (fun C : QuaternionSU2Representation.SU2 => A*C*B)
      QuaternionSU2Representation.law QuaternionSU2Representation.law :=
  (measurePreserving_mul_right QuaternionSU2Representation.law B).comp
    (measurePreserving_mul_left QuaternionSU2Representation.law A)

theorem boundary_gauge_preserving (a : Gauge) :
    MeasurePreserving (gaugeAction a) CubeWilsonSlab.boundaryHaar CubeWilsonSlab.boundaryHaar := by
  unfold CubeWilsonSlab.boundaryHaar
  exact measurePreserving_pi (fun _ : SpatialEdge => QuaternionSU2Representation.law)
    (fun _ : SpatialEdge => QuaternionSU2Representation.law)
    (fun e : SpatialEdge => haar_sandwich (a e.val.1) ((a (shift e.val.1 e.val.2))⁻¹))

/-- Exact gauge-odd cancellation under the actual ground-normalized transition. -/
theorem transfer_gauge_odd_zero (f : State → ℝ) (a : Gauge)
    (hf : ∀ V, f (gaugeAction a V) = -f V) (U : State) : transfer d f U=0 := by
  have h := (boundary_gauge_preserving a).integral_comp
    (show MeasurableEmbedding (gaugeAction a) from
      (boundaryGaugeEquiv a).measurableEmbedding)
    (fun V => d.density U V*f V)
  change (∫ V, d.density U (gaugeAction a V)*f (gaugeAction a V)
    ∂CubeWilsonSlab.boundaryHaar)=
    ∫ V, d.density U V*f V ∂CubeWilsonSlab.boundaryHaar at h
  simp_rw [d.density_gauge_right,hf,mul_neg] at h
  rw [integral_neg] at h
  have hz : (∫ V, d.density U V*f V ∂CubeWilsonSlab.boundaryHaar)=0 := by linarith
  unfold transfer
  rw [d.transition_apply,integral_withDensity_eq_integral_toReal_smul
    ((Measurable.of_uncurry_left d.density_measurable).ennreal_ofReal)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simpa only [ENNReal.toReal_ofReal (d.density_pos _ _).le,smul_eq_mul] using hz

/-- Actual gauge projection kills every single-link trace, at every coupling. -/
theorem transfer_linkTrace_zero (e : SpatialEdge) (U : State) :
    transfer d (fun V => QuaternionSU2Representation.halfTrace (V e)) U=0 := by
  classical
  let a : Gauge := fun v => if v=e.val.1 then SU2StapleExtremes.minusOne else 1
  have hv : shift e.val.1 e.val.2 ≠ e.val.1 := by
    intro h
    have hh := congrFun h e.val.2
    simp only [shift,Function.update_self] at hh
    rw [e.property] at hh
    norm_num at hh
  apply transfer_gauge_odd_zero d _ a _ U
  intro V
  simp only [gaugeAction,a,ite_true,ite_eq_right hv,inv_one,mul_one]
  exact SU2StrongCouplingCovariance.halfTrace_center_neg (V e)

theorem linkTrace_memLp (e : SpatialEdge) :
    MemLp (fun V : State => QuaternionSU2Representation.halfTrace (V e)) 2 d.stationary :=
  MemLp.of_bound (QuaternionSU2Representation.halfTrace_measurable.comp
    (measurable_pi_apply e)).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun V => by
      simpa only [Real.norm_eq_abs] using QuaternionSU2Representation.halfTrace_bound (V e)))

/-- Exact annihilation in the actual stationary L2 space, not just on formal coordinates. -/
theorem operator_linkTrace_zero (e : SpatialEdge) :
    operator d ((linkTrace_memLp d e).toLp
      (fun V : State => QuaternionSU2Representation.halfTrace (V e)))=0 := by
  have hf : Measurable (fun V : State => QuaternionSU2Representation.halfTrace (V e)) :=
    QuaternionSU2Representation.halfTrace_measurable.comp (measurable_pi_apply e)
  rw [operator_toLp d _ _ hf 1 (fun V => QuaternionSU2Representation.halfTrace_bound (V e))]
  have he : transfer d (fun V : State => QuaternionSU2Representation.halfTrace (V e))=0 :=
    funext (fun U => transfer_linkTrace_zero d e U)
  simp only [he,MemLp.toLp_zero]

end OperatorDerivativeRewrite.Foundation.CubeSlabL2
