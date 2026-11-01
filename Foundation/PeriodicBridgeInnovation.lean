import Foundation.PeriodicGaugeCompression
import Foundation.PeriodicWindingRate

/-! Actual bridge-innovation energies and the stationary physical comparison.
Every conditional kernel and marginal is the original Wilson one. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicBridgeInnovation
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround
open PeriodicNativeCompression HilbertRepresentation
attribute [local irreducible] spatialAction temporalAction boundaryHaar gaugeHaar
  PeriodicGroundBridge.law PeriodicAugmentedBridge.law PeriodicLinkDisintegration.marginal
  PeriodicLinkDisintegration.split GroundData.stationary GroundData.transition

def inserted (e : SpatialEdge) (q : PeriodicAugmentedBridge.Space) (A : SU2) :
    PeriodicAugmentedBridge.Space :=
  (PeriodicLinkDisintegration.split e).symm (((PeriodicLinkDisintegration.split e) q).1,A)

theorem inserted_measurable (e : SpatialEdge) :
    Measurable (fun p : PeriodicAugmentedBridge.Space × SU2 => inserted e p.1 p.2) :=
  (PeriodicLinkDisintegration.split e).symm.measurable.comp
    ((measurable_fst.comp ((PeriodicLinkDisintegration.split e).measurable.comp measurable_fst)).prodMk measurable_snd)

theorem density_joint_measurable (β : ℝ) : Measurable
    (fun p : (State × State) × PeriodicAugmentedBridge.Space =>
      PeriodicAugmentedBridge.density β p.1.1 p.1.2 p.2) := by
  unfold PeriodicAugmentedBridge.density
  apply Measurable.mul
  · exact (weight_joint_measurable β).comp
      (((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  · exact (weight_joint_measurable β).comp
      (((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_fst)).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_snd)))

def rowMean (e : SpatialEdge) (β : ℝ) (f : State → ℝ)
    (p : (State × State) × PeriodicAugmentedBridge.Space) : ℝ :=
  conditionalMean e β p.1.1 p.1.2 (fun q => f q.1) (((PeriodicLinkDisintegration.split e) p.2).1)

theorem rowMean_quotient (e : SpatialEdge) (β : ℝ) (f : State → ℝ)
    (p : (State × State) × PeriodicAugmentedBridge.Space) :
    rowMean e β f p =
      (∫ A, PeriodicAugmentedBridge.density β p.1.1 p.1.2 (inserted e p.2 A)*f (inserted e p.2 A).1 ∂law)/
      (∫ A, PeriodicAugmentedBridge.density β p.1.1 p.1.2 (inserted e p.2 A) ∂law) :=
  PeriodicConditionalEndpointScore.kernel_integral e β p.1.1 p.1.2
    (((PeriodicLinkDisintegration.split e) p.2).1) _

theorem rowMean_joint_measurable (e : SpatialEdge) (β : ℝ) (f : State → ℝ)
    (hf : Measurable f) : Measurable (rowMean e β f) := by
  have hi : Measurable (fun p : ((State × State) × PeriodicAugmentedBridge.Space) × SU2 =>
      inserted e p.1.2 p.2) :=
    (inserted_measurable e).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hd : Measurable (fun p : ((State × State) × PeriodicAugmentedBridge.Space) × SU2 =>
      PeriodicAugmentedBridge.density β p.1.1.1 p.1.1.2 (inserted e p.1.2 p.2)) :=
    (density_joint_measurable β).comp ((measurable_fst.comp measurable_fst).prodMk hi)
  have hnm : Measurable (fun p : ((State × State) × PeriodicAugmentedBridge.Space) × SU2 =>
      PeriodicAugmentedBridge.density β p.1.1.1 p.1.1.2 (inserted e p.1.2 p.2)*
        f (inserted e p.1.2 p.2).1) := hd.mul (hf.comp (measurable_fst.comp hi))
  have hn := (hnm.stronglyMeasurable.integral_prod_right' (ν := law)).measurable
  have hden := (hd.stronglyMeasurable.integral_prod_right' (ν := law)).measurable
  have he : rowMean e β f = fun p =>
      (∫ A, PeriodicAugmentedBridge.density β p.1.1 p.1.2 (inserted e p.2 A)*f (inserted e p.2 A).1 ∂law)/
      (∫ A, PeriodicAugmentedBridge.density β p.1.1 p.1.2 (inserted e p.2 A) ∂law) :=
    funext (rowMean_quotient e β f)
  rw [he]
  exact hn.div hden

def energy (e : SpatialEdge) (β : ℝ) (f : State → ℝ) (U W : State) : ℝ :=
  ∫ q, (f q.1-rowMean e β f ((U,W),q))^2 ∂PeriodicAugmentedBridge.law β U W

theorem energy_nonneg (e : SpatialEdge) (β : ℝ) (f : State → ℝ) (U W : State) :
    0 ≤ energy e β f U W := integral_nonneg (fun _ => sq_nonneg _)

theorem energy_joint_measurable (e : SpatialEdge) (β : ℝ) (f : State → ℝ)
    (hf : Measurable f) : Measurable (fun p : State × State => energy e β f p.1 p.2) := by
  have hh : Measurable (fun p : (State × State) × PeriodicAugmentedBridge.Space =>
      PeriodicAugmentedBridge.density β p.1.1 p.1.2 p.2*(f p.2.1-rowMean e β f p)^2) :=
    ((density_joint_measurable β).mul
    (((hf.comp (measurable_fst.comp measurable_snd)).sub
      (rowMean_joint_measurable e β f hf)).pow_const 2))
  have h := (hh.stronglyMeasurable.integral_prod_right' (ν := PeriodicAugmentedBridge.reference)).measurable
  have he : (fun p : State × State => energy e β f p.1 p.2) = fun p =>
      (∫ q, PeriodicAugmentedBridge.density β p.1 p.2 q*
        (f q.1-rowMean e β f (p,q))^2 ∂PeriodicAugmentedBridge.reference)/
        PeriodicGroundBridge.normalizer β p.1 p.2 := by
    funext p
    exact PeriodicAugmentedBridge.integral_formula β p.1 p.2 _
  rw [he]
  exact h.div (PeriodicGroundBridge.normalizer_measurable β)

theorem energy_native (e : SpatialEdge) (β : ℝ) (U W : State) (f : State → ℝ)
    (hf : Measurable f) (M : ℝ) (hb : ∀ V, |f V| ≤ M)
    (hm : MemLp f 2 (PeriodicGroundBridge.law β U W)) :
    energy e β f U W = ‖residual e β U W (hm.toLp f)‖^2 := by
  rw [← dirichlet_identity]
  exact (dirichlet_kernel e β U W f hf M hb hm).symm

/-- Actual projection minimality, against arbitrary native rest-L2 predictors. -/
theorem residual_minimal (e : SpatialEdge) (β : ℝ) (U W : State)
    (f : Middle β U W) (g : Rest e β U W) :
    ‖residual e β U W f‖^2 ≤ ‖middleLift β U W f-restLift e β U W g‖^2 := by
  have h := representation_norm_decomposition (restLift e β U W)
    (middleLift β U W f-restLift e β U W g)
  have hd := predictableAdjoint_isometry_apply (restLift e β U W) g
  change _ = ‖predictableAdjoint (restLift e β U W) (middleLift β U W f-restLift e β U W g)‖^2 +
    ‖(middleLift β U W f-restLift e β U W g)-restLift e β U W
      (predictableAdjoint (restLift e β U W) (middleLift β U W f-restLift e β U W g))‖^2 at h
  rw [map_sub, hd] at h
  change _ = ‖channel e β U W f-g‖^2 +
    ‖(middleLift β U W f-restLift e β U W g)-
      restLift e β U W (channel e β U W f-g)‖^2 at h
  have he : (middleLift β U W f-restLift e β U W g)-
      restLift e β U W (channel e β U W f-g) = residual e β U W f := by
    change _ = middleLift β U W f-restLift e β U W (channel e β U W f)
    rw [map_sub]
    abel
  rw [he] at h
  nlinarith [sq_nonneg ‖channel e β U W f-g‖]

theorem energy_le_reference (e : SpatialEdge) (β : ℝ) (U W : State) (f : State → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ V, |f V| ≤ M) (c : ℝ) :
    energy e β f U W ≤ ∫ V, (f V-c)^2 ∂PeriodicGroundBridge.law β U W := by
  letI := PeriodicLinkDisintegration.marginal_probability e β U W
  let hm : MemLp f 2 (PeriodicGroundBridge.law β U W) :=
    MemLp.of_bound hf.aestronglyMeasurable M (ae_of_all _ (fun V => by simpa only [Real.norm_eq_abs] using hb V))
  let hc : MemLp (fun _ : PeriodicLinkDisintegration.Rest e => c) 2
      (PeriodicLinkDisintegration.marginal e β U W) := memLp_const c
  have h := residual_minimal e β U W (hm.toLp f) (hc.toLp _)
  rw [← energy_native e β U W f hf M hb hm] at h
  have he : ‖middleLift β U W (hm.toLp f)-restLift e β U W (hc.toLp _)‖^2 =
      ∫ q, (f q.1-c)^2 ∂PeriodicAugmentedBridge.law β U W := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    have h1 := (hm.comp_measurePreserving (PeriodicAugmentedBridge.projection_preserving β U W)).coeFn_toLp
    have h2 := (hc.comp_measurePreserving (PeriodicConditionalEndpointScore.rest_preserving e β U W)).coeFn_toLp
    filter_upwards [Lp.coeFn_sub (middleLift β U W (hm.toLp f)) (restLift e β U W (hc.toLp _)), h1, h2]
      with q hq hF hC
    change middleLift β U W (hm.toLp f) q = f q.1 at hF
    change restLift e β U W (hc.toLp _) q = c at hC
    rw [hq, Pi.sub_apply, hF, hC]
    simp only [RCLike.inner_apply, conj_trivial, pow_two]
  rw [he] at h
  have hb2 (V : State) : |(f V-c)^2| ≤ (M+|c|)^2 := by
    have hh : |f V-c| ≤ M+|c| := by linarith [abs_sub (f V) c, hb V]
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (f V-c), abs_nonneg (f V-c), abs_nonneg c]
  exact h.trans_eq (PeriodicAugmentedBridge.projection_integral β U W
    (fun V => (f V-c)^2) ((hf.sub measurable_const).pow_const 2) _ hb2)

def increment (β : ℝ) (f : State → ℝ) (p : State × State) : ℝ :=
  ∫ V, (f V-f p.1)^2 ∂PeriodicGroundBridge.bridgeKernel β p

theorem increment_measurable (β : ℝ) (f : State → ℝ) (hf : Measurable f) :
    Measurable (increment β f) := by
  have h : Measurable (fun z : (State × State) × State => (f z.2-f z.1.1)^2) :=
    ((hf.comp measurable_snd).sub (hf.comp (measurable_fst.comp measurable_fst))).pow_const 2
  exact (h.stronglyMeasurable.integral_kernel_prod_right'
    (κ := PeriodicGroundBridge.bridgeKernel β)).measurable

private theorem difference_bound (f : State → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ V, |f V| ≤ M) (U V : State) : |(f V-f U)^2| ≤ 4*M^2 := by
  have h : |f V-f U| ≤ 2*M := by linarith [abs_sub (f V) (f U), hb U, hb V]
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_abs (f V-f U), abs_nonneg (f V-f U)]

theorem increment_bound (β : ℝ) (f : State → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ V, |f V| ≤ M) (p : State × State) : |increment β f p| ≤ 4*M^2 := by
  simpa only [increment, Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := PeriodicGroundBridge.bridgeKernel β p)
      (f := fun V => (f V-f p.1)^2) (C := 4*M^2)
      (ae_of_all _ (fun V => by simpa only [Real.norm_eq_abs] using difference_bound f M hM hb p.1 V))

theorem energy_le_increment (e : SpatialEdge) (β : ℝ) (f : State → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ V, |f V| ≤ M) (U W : State) :
    energy e β f U W ≤ increment β f (U,W) := by
  rw [increment, PeriodicGroundBridge.bridgeKernel_apply]
  exact energy_le_reference e β U W f hf M hM hb (f U)

theorem energy_bound (e : SpatialEdge) (β : ℝ) (f : State → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ V, |f V| ≤ M) (U W : State) :
    |energy e β f U W| ≤ 4*M^2 := by
  rw [abs_of_nonneg (energy_nonneg e β f U W)]
  exact (energy_le_increment e β f hf M hM hb U W).trans
    ((le_abs_self _).trans (increment_bound β f M hM hb (U,W)))

variable {β : ℝ} (d : GroundData β)
private instance stationary_probability : IsProbabilityMeasure d.stationary := d.stationary_probability
private instance transition_markov : IsMarkovKernel d.transition := d.transition_markov

/-- The ACTUAL stationary two-step endpoint distribution, not independent endpoints. -/
def average (F : State × State → ℝ) : ℝ :=
  ∫ U, ∫ W, F (U,W) ∂((d.transition ∘ₖ d.transition) U) ∂d.stationary

private theorem row_integrable (F : State × State → ℝ) (hF : Measurable F)
    (C : ℝ) (hb : ∀ p, |F p| ≤ C) (U : State) :
    Integrable (fun W => F (U,W)) ((d.transition ∘ₖ d.transition) U) :=
  Integrable.of_bound (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable C
    (ae_of_all _ (fun W => by simpa only [Real.norm_eq_abs] using hb (U,W)))

private theorem average_integrable (F : State × State → ℝ) (hF : Measurable F)
    (C : ℝ) (hb : ∀ p, |F p| ≤ C) :
    Integrable (fun U => ∫ W, F (U,W) ∂((d.transition ∘ₖ d.transition) U)) d.stationary := by
  apply Integrable.of_bound
    (hF.stronglyMeasurable.integral_kernel_prod_right' (κ := d.transition ∘ₖ d.transition)).aestronglyMeasurable C
  filter_upwards with U
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := (d.transition ∘ₖ d.transition) U)
      (f := fun W => F (U,W)) (C := C)
      (ae_of_all _ (fun W => by simpa only [Real.norm_eq_abs] using hb (U,W)))

private theorem average_mono (F G : State × State → ℝ) (hG : Measurable G)
    (C : ℝ) (hb : ∀ p, |G p| ≤ C) (hF : ∀ p, 0 ≤ F p) (hFG : ∀ p, F p ≤ G p) :
    average d F ≤ average d G := by
  apply integral_mono_of_nonneg (ae_of_all _ (fun U => integral_nonneg (fun W => hF (U,W))))
    (average_integrable d G hG C hb)
  filter_upwards with U
  exact integral_mono_of_nonneg (ae_of_all _ (fun W => hF (U,W)))
    (row_integrable d G hG C hb U) (ae_of_all _ (fun W => hFG (U,W)))

def averagedEnergy (e : SpatialEdge) (f : State → ℝ) : ℝ :=
  average d (fun p => energy e β f p.1 p.2)

theorem averagedEnergy_nonneg (e : SpatialEdge) (f : State → ℝ) :
    0 ≤ averagedEnergy d e f := integral_nonneg (fun U => integral_nonneg (fun W => energy_nonneg e β f U W))

/-- All inner and outer energies really are integrable under the genuine laws. -/
theorem averagedEnergy_integrable (e : SpatialEdge) (f : State → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ V, |f V| ≤ M) :
    Integrable (fun U => ∫ W, energy e β f U W ∂((d.transition ∘ₖ d.transition) U)) d.stationary ∧
      ∀ U, Integrable (fun W => energy e β f U W) ((d.transition ∘ₖ d.transition) U) :=
  ⟨average_integrable d (fun p => energy e β f p.1 p.2) (energy_joint_measurable e β f hf) (4*M^2)
      (fun p => energy_bound e β f hf M hM hb p.1 p.2),
    fun U => row_integrable d (fun p => energy e β f p.1 p.2) (energy_joint_measurable e β f hf) (4*M^2)
      (fun p => energy_bound e β f hf M hM hb p.1 p.2) U⟩

theorem average_increment (f : State → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ V, |f V| ≤ M) :
    average d (increment β f) =
      ∫ p : State × State, (f p.2-f p.1)^2 ∂PeriodicSlabL2.edgeLaw d := by
  have he : average d (increment β f) =
      ∫ U, ∫ V, (f V-f U)^2 ∂d.transition U ∂d.stationary := by
    apply integral_congr_ae
    filter_upwards with U
    simp only [increment, PeriodicGroundBridge.bridgeKernel_apply]
    exact PeriodicGroundBridge.bridge_average d U (fun V => (f V-f U)^2)
      ((hf.sub measurable_const).pow_const 2) (4*M^2) (fun V => difference_bound f M hM hb U V)
  rw [he]
  symm
  apply Measure.integral_compProd
  letI : IsProbabilityMeasure (PeriodicSlabL2.edgeLaw d) := by
    unfold PeriodicSlabL2.edgeLaw
    infer_instance
  exact Integrable.of_bound
    (((hf.comp measurable_snd).sub (hf.comp measurable_fst)).pow_const 2).aestronglyMeasurable
    (4*M^2) (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using difference_bound f M hM hb p.1 p.2))

/-- Quantitative comparison with the ACTUAL physical temporal-transfer form. -/
theorem averagedEnergy_le_physical (e : SpatialEdge) (f : State → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ V, |f V| ≤ M) (hm : MemLp f 2 d.stationary) :
    averagedEnergy d e f ≤
      2*SelfAdjointContractionIteration.dissipation (PeriodicSlabL2.operator d) (hm.toLp f) := by
  have h := average_mono d (fun p => energy e β f p.1 p.2) (increment β f)
    (increment_measurable β f hf) (4*M^2) (increment_bound β f M hM hb)
    (fun p => energy_nonneg e β f p.1 p.2) (fun p => energy_le_increment e β f hf M hM hb p.1 p.2)
  rw [average_increment d f hf M hM hb] at h
  have hd := PeriodicWindingRate.native_dirichlet d (hm.toLp f)
  rw [PeriodicTransferVariation.edge_norm_square] at hd
  change averagedEnergy d e f ≤ _ at h
  linarith

open PeriodicCenteredHolonomy PeriodicTemporalConcentration PeriodicSlabJoint

def Trial (f : State → ℝ) : Prop := f = first ∨ f = second ∨ f = mixed

private theorem variation_average_bound (f : State → ℝ) (hf : Measurable f)
    (hb : ∀ V, |f V| ≤ 1)
    (hv : ∀ q : Triple, (f q.1.2-f q.1.1)^2 ≤ 128*temporalEnergy q)
    (hβ : 1 ≤ β) (e : SpatialEdge) :
    averagedEnergy d e f ≤ 128*PeriodicEnergyRate.rate β := by
  let hm : MemLp f 2 d.stationary := MemLp.of_bound hf.aestronglyMeasurable 1
    (ae_of_all _ (fun V => by simpa only [Real.norm_eq_abs] using hb V))
  have ha := averagedEnergy_le_physical d e f hf 1 (by norm_num) hb hm
  have hd := PeriodicWindingRate.core_dirichlet_bound d f hm hf 128 hv
  norm_num only [show (128:ℝ)/2 = 64 by norm_num] at hd
  have ht := integral_mono (temporal_integrable d) (energy_integrable d) temporal_le_energy
  have hr := PeriodicEnergyRate.logarithmic_energy_bound d hβ
  change (∫ q, PeriodicTemporalConcentration.energy q ∂tripleLaw d) ≤ PeriodicEnergyRate.rate β at hr
  nlinarith

private theorem trial_properties (f : State → ℝ) (hf : Trial f) (hβ : 1 ≤ β) :
    Measurable f ∧ (∀ V, |f V| ≤ 1) ∧
      (∀ g V, f (PeriodicSlabGauge.gaugeAction g V) = f V) ∧
      (∫ V, f V ∂d.stationary) = 0 ∧
      ∀ e, averagedEnergy d e f ≤ 128*PeriodicEnergyRate.rate β := by
  rcases hf with rfl | rfl | rfl
  · refine ⟨first_measurable, (fun V => halfTrace_bound _),
      (fun g V => PeriodicSpatialHolonomy.trace_gauge g V origin 0), first_mean_zero d, ?_⟩
    intro e
    apply variation_average_bound d first first_measurable (fun V => halfTrace_bound _) _ hβ e
    intro q
    have h := PeriodicLoopVariation.winding_trace_change q.1.1 q.1.2 q.2 origin 0
    change (first q.1.1-first q.1.2)^2 ≤ 32*temporalEnergy q at h
    nlinarith [(temporal_bounds q).1]
  · refine ⟨second_measurable, (fun V => halfTrace_bound _),
      (fun g V => PeriodicSpatialHolonomy.trace_gauge g V origin 1), second_mean_zero d, ?_⟩
    intro e
    apply variation_average_bound d second second_measurable (fun V => halfTrace_bound _) _ hβ e
    intro q
    have h := PeriodicLoopVariation.winding_trace_change q.1.1 q.1.2 q.2 origin 1
    change (second q.1.1-second q.1.2)^2 ≤ 32*temporalEnergy q at h
    nlinarith [(temporal_bounds q).1]
  · refine ⟨mixed_measurable, (fun V => halfTrace_bound _),
      (fun g V => PeriodicSpatialHolonomy.product_trace_gauge g V origin 0 1), mixed_mean_zero d, ?_⟩
    intro e
    apply variation_average_bound d mixed mixed_measurable (fun V => halfTrace_bound _) _ hβ e
    intro q
    have h := PeriodicLoopVariation.product_trace_change q.1.1 q.1.2 q.2 origin 0 1
    change (mixed q.1.1-mixed q.1.2)^2 ≤ 128*temporalEnergy q at h
    nlinarith

/-- The SAME bounded physical winding probe defeats all192 averaged link channels. -/
theorem eventual_trial : ∀ᶠ β : ℝ in atTop, ∀ d : GroundData β,
    ∃ f : State → ℝ, Trial f ∧ Measurable f ∧ (∀ V, |f V| ≤ 1) ∧
      (∀ g V, f (PeriodicSlabGauge.gaugeAction g V) = f V) ∧
      (∫ V, f V ∂d.stationary) = 0 ∧ (1/24:ℝ) ≤ variance f d.stationary ∧
      (∑ e : SpatialEdge, averagedEnergy d e f) ≤ 24576*PeriodicEnergyRate.rate β := by
  filter_upwards [PeriodicCenteredHolonomy.eventual_variance_channel, eventually_ge_atTop (1:ℝ)] with β hv hβ
  intro d
  obtain ⟨f,hf,hv⟩ : ∃ f : State → ℝ, Trial f ∧ (1/24:ℝ) ≤ variance f d.stationary := by
    rcases hv d with h | h | h
    · exact ⟨first, Or.inl rfl, h⟩
    · exact ⟨second, Or.inr (Or.inl rfl), h⟩
    · exact ⟨mixed, Or.inr (Or.inr rfl), h⟩
  obtain ⟨hm,hb,hg,hz,he⟩ := trial_properties d f hf hβ
  refine ⟨f,hf,hm,hb,hg,hz,hv,?_⟩
  calc
    _ ≤ ∑ _ : SpatialEdge, 128*PeriodicEnergyRate.rate β := Finset.sum_le_sum (fun e _ => he e)
    _ = _ := by simp [edge_count]; ring

/-- No coupling-uniform lower frame relative to ORIGINAL stationary variance,
even with every spatial link and bounded centered gauge-invariant observables.
This does not disprove a bound relative to each FIXED-BRIDGE variance. -/
theorem no_uniform_stationary_frame (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ β : ℝ in atTop, ∀ d : GroundData β,
      ¬ ∀ f : State → ℝ, Measurable f → (∀ V, |f V| ≤ 1) →
        (∀ g V, f (PeriodicSlabGauge.gaugeAction g V) = f V) →
        (∫ V, f V ∂d.stationary) = 0 →
        κ*variance f d.stationary ≤ ∑ e : SpatialEdge, averagedEnergy d e f := by
  have hs := PeriodicEnergyRate.rate_tendsto_zero.eventually
    (gt_mem_nhds (by positivity : (0:ℝ) < κ/589824))
  filter_upwards [eventual_trial, hs] with β hv hs
  intro d hc
  obtain ⟨f,_,hm,hb,hg,hz,hv,he⟩ := hv d
  have hp := hc f hm hb hg hz
  have hsmall := (lt_div_iff₀ (by norm_num : (0:ℝ) < 589824)).mp hs
  have hpos := mul_le_mul_of_nonneg_left hv hκ.le
  nlinarith

end OperatorDerivativeRewrite.Foundation.PeriodicBridgeInnovation
