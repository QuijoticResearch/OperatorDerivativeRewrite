import Foundation.PeriodicCancellingBoundaryResponse
import Foundation.PeriodicPositiveMassAnchor
import Mathlib.Topology.Maps.Proper.Basic
/-! Open rough-rest neighborhoods of the actual cancelling lattice field.
Stationary averaging, not a fixed-boundary tail or a physical mass gap. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicCancellingRestTail
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround
open PeriodicCancellingBoundaryResponse
attribute [local irreducible] edge flux minusFace plusFace spatialWord spatialAction

-- Preserve the decider used by the existing exact selected-link section.
private abbrev vertexDecidable : DecidableEq SpatialVertex :=
  fun a b => Fintype.decidablePiFintype a b
attribute [local instance] vertexDecidable

private instance su2_secondCountable : SecondCountableTopology SU2 := by
  letI : SecondCountableTopology (Quaternion ℝ) :=
    Quaternion.linearIsometryEquivTuple.toHomeomorph.secondCountableTopology
  exact QuaternionSU2Representation.homeomorph.symm.secondCountableTopology

private theorem trace_word_continuous (p : SpatialFace) :
    Continuous (fun V : State => halfTrace (spatialWord V p)) := by
  have h0 : Continuous (fun V : State => V (p.val.1,p.val.2.1)) := continuous_apply _
  have h1 : Continuous (fun V : State => V (shift p.val.1 p.val.2.1,p.val.2.2)) := continuous_apply _
  have h2 : Continuous (fun V : State => V (shift p.val.1 p.val.2.2,p.val.2.1)) := continuous_apply _
  have h3 : Continuous (fun V : State => V (p.val.1,p.val.2.2)) := continuous_apply _
  unfold spatialWord
  exact PeriodicLowActionBlock.trace_continuous.comp (((h0.mul h1).mul h2.inv).mul h3.inv)

def pairTrace (V : State) : ℝ :=
  halfTrace (spatialWord V (minusFace false))+halfTrace (spatialWord V (plusFace false))

theorem pair_continuous : Continuous pairTrace :=
  (trace_word_continuous _).add (trace_word_continuous _)

theorem pair_gauge (g : Gauge) (V : State) :
    pairTrace (PeriodicSlabGauge.gaugeAction g V)=pairTrace V := by
  unfold pairTrace
  simp only [PeriodicSlabGauge.spatial_word_covariant,halfTrace_conjugate]

private theorem update_continuous :
    Continuous (fun p : State × SU2 => Function.update p.1 edge p.2) := by
  apply continuous_pi
  intro e
  by_cases h : e=edge
  · subst e
    simpa only [Function.update_self] using (continuous_snd : Continuous (fun p : State × SU2 => p.2))
  · simpa only [Function.update_of_ne h,Function.comp_def] using
      (continuous_apply e).comp (continuous_fst : Continuous (fun p : State × SU2 => p.1))

/-- A rest-dependent condition: it holds for EVERY replacement of the selected link. -/
def bad : Set State := {V | ∀ A : SU2,pairTrace (Function.update V edge A)<1}

theorem bad_open : IsOpen bad := by
  have hc : IsClosed {p : State × SU2 | 1≤pairTrace (Function.update p.1 edge p.2)} :=
    isClosed_le continuous_const (pair_continuous.comp update_continuous)
  have he : badᶜ = Prod.fst '' {p : State × SU2 | 1≤pairTrace (Function.update p.1 edge p.2)} := by
    ext V
    simp only [bad,Set.mem_compl_iff,Set.mem_ofPred_eq,not_forall,not_lt,Set.mem_image]
    constructor
    · rintro ⟨A,hA⟩
      exact ⟨(V,A),hA,rfl⟩
    · rintro ⟨⟨U,A⟩,hA,hU⟩
      change U=V at hU
      subst U
      exact ⟨A,hA⟩
  rw [← isClosed_compl_iff,he]
  exact isClosedMap_fst_of_compactSpace _ hc

theorem bad_measurable : MeasurableSet bad := bad_open.measurableSet

theorem bad_update (V : State) (A : SU2) : Function.update V edge A ∈ bad ↔ V ∈ bad := by
  simp only [bad,Set.mem_ofPred_eq,Function.update_idem]

private theorem gauge_update (g : Gauge) (V : State) (A : SU2) :
    PeriodicSlabGauge.gaugeAction g (Function.update V edge A)=
      Function.update (PeriodicSlabGauge.gaugeAction g V) edge
        (g edge.1*A*(g (shift edge.1 edge.2))⁻¹) := by
  funext e
  by_cases he : e=edge
  · subst e
    simp only [PeriodicSlabGauge.gaugeAction,Function.update_self]
  · simp only [PeriodicSlabGauge.gaugeAction,Function.update_of_ne he]

theorem bad_gauge (g : Gauge) (V : State) (hV : V ∈ bad) :
    PeriodicSlabGauge.gaugeAction g V ∈ bad := by
  intro A
  let B := (g edge.1)⁻¹*A*g (shift edge.1 edge.2)
  have hh := pair_gauge g (Function.update V edge B)
  rw [gauge_update] at hh
  have he : g edge.1*B*(g (shift edge.1 edge.2))⁻¹=A := by dsimp [B]; group
  rw [he] at hh
  rw [hh]
  exact hV B

theorem minus_section (A : SU2) :
    halfTrace (spatialWord (Function.update flux edge A) (minusFace false)) = -halfTrace A := by
  have hz : (1:ZMod 4) ≠ 0 := by decide
  have hz0 : (0:ZMod 4) ≠ 1 := by decide
  norm_num [spatialWord,minusFace,edge,flux,shift,Function.update_apply,
    Prod.mk.injEq,funext_iff,Fin.forall_fin_succ,hz,hz0]
  rw [SU2WilsonConvolution.halfTrace_mul_comm,
    SU2StrongCouplingCovariance.halfTrace_center_neg]

theorem pair_section (A : SU2) : pairTrace (Function.update flux edge A)=0 := by
  unfold pairTrace
  rw [minus_section]
  have ho := PeriodicCancellingBoundaryResponse.observable_section A
  unfold PeriodicCancellingBoundaryResponse.observable at ho
  exact (congrArg (fun x : ℝ => -halfTrace A+x) ho).trans (neg_add_cancel _)

theorem flux_bad : flux∈bad := by
  intro A
  rw [pair_section]
  norm_num

theorem section_bad (A : SU2) : Function.update flux edge A ∈ bad :=
  (bad_update flux A).mpr flux_bad

theorem bad_action (V : State) (hV : V ∈ bad) : 1<spatialAction V := by
  have hp := hV (V edge)
  rw [Function.update_eq_self] at hp
  have hd : minusFace false ≠ plusFace false := by decide +kernel
  have hs : (1-halfTrace (spatialWord V (minusFace false)))+
      (1-halfTrace (spatialWord V (plusFace false))) ≤ spatialAction V := by
    unfold spatialAction
    have hi : (∑ p ∈ ({minusFace false,plusFace false} : Finset SpatialFace),
        (1-halfTrace (spatialWord V p))) ≤ ∑ p : SpatialFace,(1-halfTrace (spatialWord V p)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun p _ _ => sub_nonneg.mpr (abs_le.mp (halfTrace_bound (spatialWord V p))).2)
    simpa only [Finset.sum_insert (show minusFace false ∉ ({plusFace false} : Finset SpatialFace) by
      simpa only [Finset.mem_singleton] using hd),Finset.sum_singleton] using hi
  unfold pairTrace at hp
  linarith


theorem bad_gauge_iff (g : Gauge) (V : State) :
    PeriodicSlabGauge.gaugeAction g V ∈ bad ↔ V ∈ bad := by
  constructor
  · intro h
    have hc := bad_gauge (fun v => (g v)⁻¹) (PeriodicSlabGauge.gaugeAction g V) h
    have he : PeriodicSlabGauge.gaugeAction (fun v => (g v)⁻¹)
        (PeriodicSlabGauge.gaugeAction g V)=V := by
      funext e
      unfold PeriodicSlabGauge.gaugeAction
      group
    rwa [he] at hc
  · exact bad_gauge g V


/-- The frozen-rest event is an actual OPEN neighborhood, not just the exact point. -/
def restBad : Set (PeriodicLinkDisintegration.Rest edge) :=
  {r | PeriodicLinkDisintegration.baseField edge r ∈ bad}

private theorem base_apply (r : PeriodicLinkDisintegration.Rest edge) (e : SpatialEdge) :
    PeriodicLinkDisintegration.baseField edge r e =
      if h : e=edge then 1 else r.1 ⟨e,h⟩ := by
  have hc := (PeriodicLinkDisintegration.coordinateSplit edge).apply_symm_apply (1,r.1)
  change PeriodicLinkDisintegration.coordinateSplit edge
    (PeriodicLinkDisintegration.baseField edge r) = (1,r.1) at hc
  rw [PeriodicLinkDisintegration.coordinateSplit_apply] at hc
  by_cases he : e=edge
  · subst e
    simpa using congrArg Prod.fst hc
  · simpa only [dite_eq_right he] using congrFun (congrArg Prod.snd hc) ⟨e,he⟩

private theorem base_continuous :
    Continuous (PeriodicLinkDisintegration.baseField edge) := by
  apply continuous_pi
  intro e
  by_cases he : e=edge
  · simpa only [base_apply,dite_eq_left he] using
      (continuous_const : Continuous (fun _ : PeriodicLinkDisintegration.Rest edge => (1:SU2)))
  · simpa only [base_apply,dite_eq_right he,Function.comp_def] using
      (continuous_apply (⟨e,he⟩ : {j : SpatialEdge // j≠edge})).comp
        (continuous_fst : Continuous (fun r : PeriodicLinkDisintegration.Rest edge => r.1))

theorem restBad_open : IsOpen restBad := bad_open.preimage base_continuous

theorem restBad_measurable : MeasurableSet restBad := by
  apply bad_measurable.preimage
  exact (PeriodicLinkDisintegration.coordinateSplit edge).symm.measurable.comp
    (measurable_const.prodMk measurable_fst)

private theorem base_split (q : PeriodicAugmentedBridge.Space) :
    PeriodicLinkDisintegration.baseField edge
      ((PeriodicLinkDisintegration.split edge q).1)=Function.update q.1 edge 1 := by
  funext e
  rw [base_apply,PeriodicLinkDisintegration.split_apply]
  by_cases he : e=edge
  · subst e
    simp
  · simp only [dite_eq_right he,Function.update_of_ne he]

theorem restBad_contains : PeriodicCancellingBoundaryResponse.rest ∈ restBad := by
  have h := base_split (flux,(1,1))
  change PeriodicLinkDisintegration.baseField edge PeriodicCancellingBoundaryResponse.rest =
    Function.update flux edge 1 at h
  change PeriodicLinkDisintegration.baseField edge PeriodicCancellingBoundaryResponse.rest ∈ bad
  rw [h]
  exact section_bad 1

/-- Probability under the ACTUAL partition-weighted rest marginal. -/
theorem rest_probability_eq_bridge (β : ℝ) (U W : State) :
    (PeriodicLinkDisintegration.marginal edge β U W).real restBad =
      (PeriodicGroundBridge.law β U W).real bad := by
  apply congrArg ENNReal.toReal
  rw [← PeriodicLinkDisintegration.actual_rest_marginal,
    Measure.fst_apply restBad_measurable,
    Measure.map_apply (PeriodicLinkDisintegration.split edge).measurable
      (measurable_fst restBad_measurable)]
  rw [← (PeriodicAugmentedBridge.projection_preserving β U W).map_eq,
    Measure.map_apply measurable_fst bad_measurable]
  congr 1
  ext q
  change PeriodicLinkDisintegration.baseField edge
    ((PeriodicLinkDisintegration.split edge q).1) ∈ bad ↔ q.1∈bad
  rw [base_split,bad_update]

theorem stationary_bad_bound {β : ℝ} (hb : 16777216 ≤ β) (g : GroundData β) :
    g.stationary.real bad ≤
      (PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant)*
        Real.exp (-β) := by
  let _ := g.stationary_probability
  have hs : bad ⊆ PeriodicHighExcursion.region β β := by
    intro V hV
    have ha := bad_action V hV
    change β<β*spatialAction V
    have hβ : 0<β := by linarith
    nlinarith
  exact (measureReal_mono hs).trans (PeriodicPositiveMassAnchor.exponential_tail hb g β)

private theorem indicator_bound (V : State) : |bad.indicator (1 : State → ℝ) V|≤1 := by
  by_cases h : V ∈ bad <;> simp [Set.indicator,h]

theorem averaged_bridge_identity {β : ℝ} (g : GroundData β) :
    (∫ U,∫ W,(PeriodicGroundBridge.law β U W).real bad
      ∂((g.transition ∘ₖ g.transition) U) ∂g.stationary)=g.stationary.real bad := by
  have h := PeriodicGroundBridge.stationary_bridge_average g
    (bad.indicator (1 : State → ℝ)) (measurable_const.indicator bad_measurable) 1 indicator_bound
  simpa only [integral_indicator_one bad_measurable] using h

/-- Exponential suppression AFTER true stationary endpoint averaging.
No fixed-U,W estimate, derivative-weighted bound or mass gap is inferred. -/
theorem averaged_rest_bound {β : ℝ} (hb : 16777216 ≤ β) (g : GroundData β) :
    (∫ U,∫ W,(PeriodicLinkDisintegration.marginal edge β U W).real restBad
      ∂((g.transition ∘ₖ g.transition) U) ∂g.stationary) ≤
      (PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant)*
        Real.exp (-β) := by
  simp_rw [rest_probability_eq_bridge]
  rw [averaged_bridge_identity]
  exact stationary_bad_bound hb g


/-- The neighborhood has positive probability at every finite coupling and endpoint pair. -/
theorem bridge_bad_positive (β : ℝ) (U W : State) :
    0<(PeriodicGroundBridge.law β U W).real bad := by
  letI : boundaryHaar.IsOpenPosMeasure := by unfold boundaryHaar; infer_instance
  have hp : 0<boundaryHaar bad := IsOpen.measure_pos _ bad_open ⟨flux,flux_bad⟩
  let w := PeriodicGroundBridge.bridgeWeight β U W
  have hi : Integrable (bad.indicator w) boundaryHaar :=
    (PeriodicGroundBridge.bridgeWeight_integrable β U W).indicator bad_measurable
  have hn (V : State) : 0≤bad.indicator w V := by
    by_cases h : V∈bad
    · simp only [Set.indicator_of_mem h]
      exact (PeriodicGroundBridge.bridgeWeight_pos β U W V).le
    · simp only [Set.indicator_of_notMem h,le_refl]
  have hs : Function.support (bad.indicator w)=bad := by
    ext V
    by_cases h : V∈bad <;>
      simp [Function.mem_support,Set.indicator,h,w,
        (PeriodicGroundBridge.bridgeWeight_pos β U W V).ne']
  have hpos : 0<∫ V,bad.indicator w V ∂boundaryHaar := by
    apply (integral_pos_iff_support_of_nonneg hn hi).mpr
    rw [hs]
    exact hp
  rw [← integral_indicator_one bad_measurable,PeriodicGroundBridge.integral_formula]
  apply div_pos _ (PeriodicGroundBridge.normalizer_pos β U W)
  convert hpos using 1
  apply integral_congr_ae
  filter_upwards with V
  by_cases h : V∈bad <;> simp [Set.indicator,h,w]

theorem rest_bad_positive (β : ℝ) (U W : State) :
    0<(PeriodicLinkDisintegration.marginal edge β U W).real restBad := by
  rw [rest_probability_eq_bridge]
  exact bridge_bad_positive β U W

end OperatorDerivativeRewrite.Foundation.PeriodicCancellingRestTail
