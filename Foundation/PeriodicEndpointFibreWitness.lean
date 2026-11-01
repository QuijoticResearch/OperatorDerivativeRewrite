import Foundation.PeriodicEndpointWard
/-! Actual nonzero conditional score energy at explicit rough endpoints.
This distinguishes a genuine fibre source from its vanishing scalar physical
projection; the witness observable is not asserted to be a physical middle field. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace OperatorDerivativeRewrite.Foundation.PeriodicEndpointFibreWitness
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab
open PeriodicCancellingBoundaryResponse PeriodicEndpointScore
attribute [local irreducible] spatialAction temporalAction boundaryHaar gaugeHaar
private abbrev vertexDecidable : DecidableEq SpatialVertex := fun a b => Fintype.decidablePiFintype a b
attribute [local instance] vertexDecidable

private instance su2_secondCountable : SecondCountableTopology SU2 := by
  letI : SecondCountableTopology (Quaternion ℝ) :=
    Quaternion.linearIsometryEquivTuple.toHomeomorph.secondCountableTopology
  exact QuaternionSU2Representation.homeomorph.symm.secondCountableTopology

def leftEndpoint : State := Function.update (1 : State) edge (SU2JointPlaquetteCubic.axis 0 (-Real.pi/2))
def rightEndpoint : State := Function.update (1 : State) edge (SU2JointPlaquetteCubic.axis 0 (Real.pi/2))
def point (A : SU2) : PeriodicAugmentedBridge.Space := (Function.update flux edge A,(1,1))

theorem point_bad (A : SU2) : (point A).1∈PeriodicCancellingRestTail.bad := by
  exact (PeriodicCancellingRestTail.bad_update flux A).mpr PeriodicCancellingRestTail.flux_bad

private theorem local_direction (A : SU2) :
    PeriodicConditionalEndpointScore.localDirection leftEndpoint rightEndpoint 1 1 edge A=2*halfTrace A := by
  have hi : SU2JointPlaquetteCubic.axis 0 (-Real.pi/2)=
      (SU2JointPlaquetteCubic.axis 0 (Real.pi/2))⁻¹ := by
    simpa only [neg_div] using (SU2AxisMatrixJets.axis_inv 0 (Real.pi/2)).symm
  have hl : PeriodicEndpointScore.left (Real.pi/2) leftEndpoint edge=1 := by
    simp only [PeriodicEndpointScore.left,leftEndpoint,Function.update_self,hi,mul_inv_cancel]
  have hr : PeriodicEndpointScore.right (Real.pi/2) rightEndpoint edge=1 := by
    simp only [PeriodicEndpointScore.right,rightEndpoint,Function.update_self]
    rw [← SU2AxisMatrixJets.axis_inv]
    exact mul_inv_cancel _
  simp only [PeriodicConditionalEndpointScore.localDirection,PeriodicLinkStaples.leftTemporal,
    PeriodicLinkStaples.rightTemporal,Pi.one_apply,inv_one,one_mul,mul_one,hl,hr]
  ring

/-- Exact separation on TWO configurations in the actual cancelling event. -/
theorem direction_separation :
    direction leftEndpoint rightEndpoint (point SU2StapleExtremes.minusOne)-
      direction leftEndpoint rightEndpoint (point 1)=-4 := by
  have h := PeriodicConditionalEndpointScore.direction_difference leftEndpoint flux rightEndpoint 1 1 edge
    SU2StapleExtremes.minusOne
  change direction leftEndpoint rightEndpoint (point SU2StapleExtremes.minusOne)-
    direction leftEndpoint rightEndpoint (point 1)=_ at h
  rw [local_direction,local_direction,SU2OpenLinkGaugeObstruction.halfTrace_minusOne,
    SU2OpenLinkGaugeObstruction.halfTrace_one] at h
  norm_num at h ⊢
  exact h

theorem score_separation (β : ℝ) :
    score β leftEndpoint rightEndpoint (point SU2StapleExtremes.minusOne)-
      score β leftEndpoint rightEndpoint (point 1)=-4*β := by
  unfold score
  linear_combination β*direction_separation

theorem direction_continuous (U W : State) : Continuous (direction U W) := by
  unfold direction traceSum
  apply continuous_finsetSum
  intro e _
  apply Continuous.add
  · exact PeriodicLowActionBlock.trace_continuous.comp (by unfold temporalWord; fun_prop)
  · exact PeriodicLowActionBlock.trace_continuous.comp (by unfold temporalWord; fun_prop)

theorem score_continuous (β : ℝ) (U W : State) : Continuous (score β U W) :=
  continuous_const.mul ((direction_continuous U W).sub continuous_const)

/-- Strict positivity under the ACTUAL normalized conditional Wilson law.
The source mean cannot cancel both separated configurations in the open event. -/
theorem badEnergy_positive {β : ℝ} (hb : β≠0) :
    0<PeriodicEndpointScore.badEnergy β leftEndpoint rightEndpoint := by
  let E : Set PeriodicAugmentedBridge.Space := (fun q : PeriodicAugmentedBridge.Space => q.1) ⁻¹' PeriodicCancellingRestTail.bad
  let s := score β leftEndpoint rightEndpoint
  let O : Set PeriodicAugmentedBridge.Space := E ∩ {q | s q≠0}
  have hE : IsOpen E := PeriodicCancellingRestTail.bad_open.preimage continuous_fst
  have hO : IsOpen O := hE.inter ((isClosed_eq (score_continuous β leftEndpoint rightEndpoint) continuous_const).isOpen_compl)
  have hex : O.Nonempty := by
    by_cases h0 : s (point 1)=0
    · refine ⟨point SU2StapleExtremes.minusOne,point_bad _,?_⟩
      intro hm
      have h := score_separation β
      change s (point SU2StapleExtremes.minusOne)-s (point 1)=-4*β at h
      rw [hm,h0] at h
      exact hb (by linarith)
    · exact ⟨point 1,point_bad _,h0⟩
  letI : PeriodicAugmentedBridge.reference.IsOpenPosMeasure := by
    unfold PeriodicAugmentedBridge.reference boundaryHaar gaugeHaar
    infer_instance
  have hp : 0<PeriodicAugmentedBridge.reference O := IsOpen.measure_pos _ hO hex
  let F := fun q : PeriodicAugmentedBridge.Space => PeriodicAugmentedBridge.density β leftEndpoint rightEndpoint q*
    E.indicator (fun q => (s q)^2) q
  have hi : Integrable F PeriodicAugmentedBridge.reference := by
    apply Integrable.of_bound
      ((PeriodicAugmentedBridge.density_measurable β leftEndpoint rightEndpoint).mul
        (((score_measurable β leftEndpoint rightEndpoint).pow_const 2).indicator hE.measurableSet)).aestronglyMeasurable
      ((Real.exp (768*|β|)^2)*(768*|β|)^2)
    filter_upwards with q
    change ‖PeriodicAugmentedBridge.density β leftEndpoint rightEndpoint q*E.indicator (fun q => (s q)^2) q‖≤_
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (PeriodicAugmentedBridge.density_pos β leftEndpoint rightEndpoint q)]
    apply mul_le_mul (PeriodicAugmentedBridge.density_upper β leftEndpoint rightEndpoint q) ?_ (abs_nonneg _) (sq_nonneg _)
    by_cases hq : q∈E
    · rw [Set.indicator_of_mem hq,abs_of_nonneg (sq_nonneg _)]
      have hs := score_bound β leftEndpoint rightEndpoint q
      dsimp only [s]
      nlinarith [abs_nonneg (score β leftEndpoint rightEndpoint q),sq_abs (score β leftEndpoint rightEndpoint q)]
    · rw [Set.indicator_of_notMem hq,abs_zero]
      exact sq_nonneg _
  have hn (q : PeriodicAugmentedBridge.Space) : 0≤F q :=
    mul_nonneg (PeriodicAugmentedBridge.density_pos β leftEndpoint rightEndpoint q).le
      (Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)
  have hs : O⊆Function.support F := by
    intro q hq
    change F q≠0
    dsimp only [F]
    rw [Set.indicator_of_mem hq.1]
    exact mul_ne_zero (PeriodicAugmentedBridge.density_pos β leftEndpoint rightEndpoint q).ne' (pow_ne_zero _ hq.2)
  have hpos : 0<∫ q,F q ∂PeriodicAugmentedBridge.reference :=
    (integral_pos_iff_support_of_nonneg hn hi).mpr (hp.trans_le (measure_mono hs))
  change 0<∫ q,E.indicator (fun q => (s q)^2) q ∂PeriodicAugmentedBridge.law β leftEndpoint rightEndpoint
  rw [PeriodicAugmentedBridge.integral_formula]
  exact div_pos hpos (PeriodicGroundBridge.normalizer_pos β leftEndpoint rightEndpoint)

def frozenObservable (β : ℝ) : PeriodicAugmentedBridge.Space → ℝ :=
  ((fun q : PeriodicAugmentedBridge.Space => q.1) ⁻¹' PeriodicCancellingRestTail.bad).indicator
    (score β leftEndpoint rightEndpoint)

theorem frozenObservable_measurable (β : ℝ) : Measurable (frozenObservable β) :=
  (score_measurable β leftEndpoint rightEndpoint).indicator
    (measurable_fst PeriodicCancellingRestTail.bad_measurable)

theorem frozenObservable_bound (β : ℝ) (q : PeriodicAugmentedBridge.Space) :
    |frozenObservable β q|≤768*|β| := by
  let E : Set PeriodicAugmentedBridge.Space := (fun q : PeriodicAugmentedBridge.Space => q.1) ⁻¹' PeriodicCancellingRestTail.bad
  change |E.indicator (score β leftEndpoint rightEndpoint) q|≤_
  by_cases hq : q∈E
  · rw [Set.indicator_of_mem hq]
    exact score_bound β leftEndpoint rightEndpoint q
  · rw [Set.indicator_of_notMem hq,abs_zero]
    positivity

/-- Actual normalized Wilson response with a FROZEN bounded augmented observable.
It is not asserted to be a gauge-invariant middle-only observable. -/
theorem frozenObservable_derivative (β : ℝ) :
    HasDerivAt (fun h => ∫ q,frozenObservable β q ∂PeriodicAugmentedBridge.law β
      (left h leftEndpoint) (right h rightEndpoint))
        (PeriodicEndpointScore.badEnergy β leftEndpoint rightEndpoint) 0 := by
  have h := expectation_score β leftEndpoint rightEndpoint (frozenObservable β)
    (frozenObservable_measurable β) (768*|β|)
    (mul_nonneg (by norm_num) (abs_nonneg _)) (frozenObservable_bound β)
  convert h using 1
  unfold PeriodicEndpointScore.badEnergy
  apply integral_congr_ae
  filter_upwards with q
  let E : Set PeriodicAugmentedBridge.Space := (fun q : PeriodicAugmentedBridge.Space => q.1) ⁻¹' PeriodicCancellingRestTail.bad
  change E.indicator (fun q => (score β leftEndpoint rightEndpoint q)^2) q=
    E.indicator (score β leftEndpoint rightEndpoint) q*score β leftEndpoint rightEndpoint q
  by_cases hq : q∈E
  · rw [Set.indicator_of_mem hq,Set.indicator_of_mem hq,pow_two]
  · rw [Set.indicator_of_notMem hq,Set.indicator_of_notMem hq,zero_mul]

attribute [local irreducible] SU2JointPlaquetteCubic.axis leftEndpoint rightEndpoint point
  PeriodicEndpointScore.badEnergy PeriodicEndpointScore.score PeriodicEndpointScore.direction
  PeriodicStationaryEndpointResponse.law PeriodicStationaryEndpointResponse.endpointLaw
  PeriodicStationaryEndpointResponse.bridgeKernel PeriodicStationaryEndpointResponse.badScoreField
  PeriodicCancellingRestTail.bad

private theorem parametric_continuous {μ : Measure PeriodicAugmentedBridge.Space} [IsFiniteMeasure μ]
    (F : (State × State) × PeriodicAugmentedBridge.Space → ℝ) (hF : Continuous F) :
    Continuous (fun p : State × State => ∫ q,F (p,q) ∂μ) := by
  have h := continuous_parametric_integral_of_continuous (μ := μ)
    (f := fun p q => F (p,q)) hF (s := Set.univ) isCompact_univ
  simpa only [Measure.restrict_univ] using h

private theorem density_joint_continuous (β : ℝ) :
    Continuous (fun p : (State × State) × PeriodicAugmentedBridge.Space => PeriodicAugmentedBridge.density β p.1.1 p.1.2 p.2) := by
  have hw : Continuous (fun p : (State × State) × Gauge => weight β p.1.1 p.1.2 p.2) := by
    unfold weight
    exact Real.continuous_exp.comp (PeriodicLowActionBlock.action_continuous.const_mul (-β))
  have h1 : Continuous (fun p : (State × State) × PeriodicAugmentedBridge.Space => ((p.1.1,p.2.1),p.2.2.1)) := by fun_prop
  have h2 : Continuous (fun p : (State × State) × PeriodicAugmentedBridge.Space => ((p.2.1,p.1.2),p.2.2.2)) := by fun_prop
  exact (hw.comp h1).mul (hw.comp h2)

private theorem direction_joint_continuous :
    Continuous (fun p : (State × State) × PeriodicAugmentedBridge.Space => direction p.1.1 p.1.2 p.2) := by
  unfold direction traceSum
  apply continuous_finsetSum
  intro e _
  apply Continuous.add
  · exact PeriodicLowActionBlock.trace_continuous.comp (by simp only [temporalWord,left,right]; fun_prop)
  · exact PeriodicLowActionBlock.trace_continuous.comp (by simp only [temporalWord,left,right]; fun_prop)

private theorem normalizer_continuous (β : ℝ) :
    Continuous (fun p : State × State => PeriodicGroundBridge.normalizer β p.1 p.2) := by
  simpa only [PeriodicAugmentedBridge.total_integral] using
    parametric_continuous (μ := PeriodicAugmentedBridge.reference) _ (density_joint_continuous β)

private theorem mean_continuous (β : ℝ) :
    Continuous (fun p : State × State => ∫ q,direction p.1 p.2 q ∂PeriodicAugmentedBridge.law β p.1 p.2) := by
  have he : (fun p : State × State => ∫ q,direction p.1 p.2 q ∂PeriodicAugmentedBridge.law β p.1 p.2)=
      (fun p => (∫ q,PeriodicAugmentedBridge.density β p.1 p.2 q*direction p.1 p.2 q
        ∂PeriodicAugmentedBridge.reference)/PeriodicGroundBridge.normalizer β p.1 p.2) := by
    funext p
    exact PeriodicAugmentedBridge.integral_formula β p.1 p.2 _
  rw [he]
  exact (parametric_continuous _ ((density_joint_continuous β).mul direction_joint_continuous)).div
    (normalizer_continuous β) (fun p => (PeriodicGroundBridge.normalizer_pos β p.1 p.2).ne')

private theorem score_joint_continuous (β : ℝ) :
    Continuous (fun p : (State × State) × PeriodicAugmentedBridge.Space => score β p.1.1 p.1.2 p.2) := by
  unfold score
  exact continuous_const.mul (direction_joint_continuous.sub ((mean_continuous β).comp continuous_fst))

/-- The bad event is fixed while the endpoints vary. Its boundary need not have
zero measure: integrate the continuous numerator against the RESTRICTED measure. -/
theorem badEnergy_continuous (β : ℝ) :
    Continuous (fun p : State × State => PeriodicEndpointScore.badEnergy β p.1 p.2) := by
  let E : Set PeriodicAugmentedBridge.Space := (fun q : PeriodicAugmentedBridge.Space => q.1) ⁻¹' PeriodicCancellingRestTail.bad
  have hE : MeasurableSet E := measurable_fst PeriodicCancellingRestTail.bad_measurable
  have hc := parametric_continuous (μ := PeriodicAugmentedBridge.reference.restrict E) _
    ((density_joint_continuous β).mul ((score_joint_continuous β).pow 2))
  have he : (fun p : State × State => PeriodicEndpointScore.badEnergy β p.1 p.2)=
      (fun p => (∫ q,PeriodicAugmentedBridge.density β p.1 p.2 q*(score β p.1 p.2 q)^2
        ∂PeriodicAugmentedBridge.reference.restrict E)/PeriodicGroundBridge.normalizer β p.1 p.2) := by
    funext p
    unfold PeriodicEndpointScore.badEnergy
    rw [PeriodicAugmentedBridge.integral_formula,← integral_indicator hE]
    congr 1
    apply integral_congr_ae
    filter_upwards with q
    by_cases hq : q∈E
    · rw [Set.indicator_of_mem hq,Set.indicator_of_mem hq]
    · rw [Set.indicator_of_notMem hq,Set.indicator_of_notMem hq,mul_zero]
  rw [he]
  exact hc.div (normalizer_continuous β) (fun p => (PeriodicGroundBridge.normalizer_pos β p.1 p.2).ne')

private theorem haar_ac_stationary {β : ℝ} (g : PeriodicSlabGround.GroundData β) :
    boundaryHaar ≪ g.stationary := by
  unfold PeriodicSlabGround.GroundData.stationary SignedDensityProbabilitySampling.sampler
    SignedAbsoluteIntegration.absoluteDensity
  have hAbs (U : State) : |g.function U^2|=g.function U^2 := abs_of_nonneg (sq_nonneg _)
  simp_rw [hAbs]
  have h := withDensity_absolutelyContinuous' (μ := boundaryHaar)
    (g.measurable.pow_const 2).ennreal_ofReal.aemeasurable
    (ae_of_all _ (fun U => (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (g.function_pos U))).ne'))
  exact h.smul_right (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)

private theorem haar_ac_transition {β : ℝ} (g : PeriodicSlabGround.GroundData β) (U : State) :
    boundaryHaar ≪ g.transition U := by
  rw [g.transition_apply]
  have hm : Measurable (fun V : State => g.density U V) :=
    g.density_measurable.comp (measurable_const.prodMk measurable_id)
  exact withDensity_absolutelyContinuous' hm.ennreal_ofReal.aemeasurable
    (ae_of_all _ (fun V => (ENNReal.ofReal_pos.mpr (g.density_pos U V)).ne'))

private theorem haar_ac_twoStep {β : ℝ} (g : PeriodicSlabGround.GroundData β) (U : State) :
    boundaryHaar ≪ (g.transition ∘ₖ g.transition) U := by
  letI := g.transition_markov
  have h : (Kernel.const State boundaryHaar) ∘ₘ (g.transition U) ≪ g.transition ∘ₘ (g.transition U) :=
    Measure.AbsolutelyContinuous.comp_left _ (ae_of_all _ (fun V => haar_ac_transition g V))
  have he : (Kernel.const State boundaryHaar) ∘ₘ (g.transition U)=boundaryHaar := by
    ext S hS
    rw [Measure.bind_apply hS (Kernel.aemeasurable _)]
    simp
  rw [he] at h
  exact h

/-- Positive Haar endpoint sets stay positive under the TRUE stationary TWO-step
endpoint law. This is absolute continuity in the needed REVERSE direction. -/
theorem haar_ac_endpoint {β : ℝ} (g : PeriodicSlabGround.GroundData β) :
    boundaryHaar.prod boundaryHaar ≪ PeriodicStationaryEndpointResponse.endpointLaw g := by
  letI := g.stationary_probability
  letI := g.transition_markov
  have h : boundaryHaar.compProd (Kernel.const State boundaryHaar) ≪
      g.stationary.compProd (g.transition ∘ₖ g.transition) :=
    (haar_ac_stationary g).compProd (ae_of_all _ (fun U => haar_ac_twoStep g U))
  simpa only [Measure.compProd_const,PeriodicStationaryEndpointResponse.endpointLaw] using h

/-- A NONZERO actual joint source whose physical high projection was proved zero.
No fixed-endpoint or fibre response is erased by taking a signed first moment. -/
theorem native_joint_positive {β : ℝ} (hb : β≠0) (g : PeriodicSlabGround.GroundData β) :
    0<‖PeriodicStationaryEndpointResponse.badScoreField g‖^2 := by
  let E : State × State → ℝ := fun p => PeriodicEndpointScore.badEnergy β p.1 p.2
  have hB (p : State × State) : |E p|≤(768*|β|)^2 := by
    rw [abs_of_nonneg (PeriodicEndpointScore.badEnergy_nonneg β p.1 p.2)]
    exact (PeriodicEndpointScore.badEnergy_bound β p.1 p.2).trans
      (mul_le_of_le_one_right (sq_nonneg _) measureReal_le_one)
  have hi : Integrable E (PeriodicStationaryEndpointResponse.endpointLaw g) :=
    Integrable.of_bound (PeriodicEndpointScore.badEnergy_measurable β).aestronglyMeasurable _
      (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using hB p))
  have ho : IsOpen (Function.support E) :=
    (isClosed_eq (badEnergy_continuous β) continuous_const).isOpen_compl
  letI : (boundaryHaar.prod boundaryHaar).IsOpenPosMeasure := by unfold boundaryHaar; infer_instance
  have hp : 0<(boundaryHaar.prod boundaryHaar) (Function.support E) :=
    IsOpen.measure_pos _ ho ⟨(leftEndpoint,rightEndpoint),(badEnergy_positive hb).ne'⟩
  have hh : 0<(PeriodicStationaryEndpointResponse.endpointLaw g) (Function.support E) :=
    pos_iff_ne_zero.mpr (fun hz => hp.ne' (haar_ac_endpoint g hz))
  have hpos : 0<∫ p,E p ∂PeriodicStationaryEndpointResponse.endpointLaw g :=
    (integral_pos_iff_support_of_nonneg (fun p : State × State => PeriodicEndpointScore.badEnergy_nonneg β p.1 p.2) hi).mpr hh
  letI := g.stationary_probability
  letI := g.transition_markov
  rw [PeriodicStationaryEndpointResponse.endpointLaw] at hi hpos
  rw [Measure.integral_compProd hi] at hpos
  rw [PeriodicStationaryEndpointResponse.badScore_norm]
  simpa only [← PeriodicConditionalEndpointScore.badEnergy_split] using hpos

/-- The previous zero Gaussian image is a genuine norm loss on an explicit actual
native source, not evidence that the underlying joint source vanishes. -/
theorem actual_strict_norm_loss {β : ℝ} (hβ : 0≤β) (hb : β≠0) (g : PeriodicSlabGround.GroundData β) (K : ℝ) :
    ‖PeriodicStationaryEndpointResponse.gaussianResponse hβ g K (PeriodicStationaryEndpointResponse.badScoreField g)‖<
      ‖PeriodicStationaryEndpointResponse.badScoreField g‖ := by
  rw [PeriodicEndpointWard.bad_gaussian_zero,norm_zero]
  have h := native_joint_positive hb g
  nlinarith [norm_nonneg (PeriodicStationaryEndpointResponse.badScoreField g)]

/-- A unit vector in the ACTUAL native joint domain, annihilated by both the
physical high realization and its Gaussian image. -/
theorem native_unit_null {β : ℝ} (hβ : 0≤β) (hb : β≠0) (g : PeriodicSlabGround.GroundData β) (K : ℝ) :
    ∃ Z : PeriodicStationaryEndpointResponse.JointSpace g,‖Z‖=1 ∧
      PeriodicStationaryEndpointResponse.realization g K Z=0 ∧
      PeriodicStationaryEndpointResponse.gaussianResponse hβ g K Z=0 := by
  let W := PeriodicStationaryEndpointResponse.badScoreField g
  have hp : 0<‖W‖ := by
    have h := native_joint_positive hb g
    change 0<‖W‖^2 at h
    nlinarith [norm_nonneg W]
  refine ⟨‖W‖⁻¹ • W,?_,?_,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hp,inv_mul_cancel₀ hp.ne']
  · rw [map_smul,PeriodicEndpointWard.bad_realization_zero,smul_zero]
  · rw [map_smul,PeriodicEndpointWard.bad_gaussian_zero,smul_zero]

/-- No positive original-norm lower frame bound survives for THIS actual
source-to-Gaussian operator. This excludes unitary/isometric transport through it. -/
theorem no_positive_lower_frame {β : ℝ} (hβ : 0≤β) (hb : β≠0)
    (g : PeriodicSlabGround.GroundData β) (K : ℝ) :
    ¬∃ c : ℝ,0<c ∧ ∀ Z : PeriodicStationaryEndpointResponse.JointSpace g,
      c*‖Z‖^2≤‖PeriodicStationaryEndpointResponse.gaussianResponse hβ g K Z‖^2 := by
  rintro ⟨c,hc,hframe⟩
  obtain ⟨Z,hZ,_,hz⟩ := native_unit_null hβ hb g K
  have h := hframe Z
  rw [hZ,hz,norm_zero,one_pow,zero_pow (by norm_num : 2≠0),mul_one] at h
  exact (not_le_of_gt hc) h
end OperatorDerivativeRewrite.Foundation.PeriodicEndpointFibreWitness
