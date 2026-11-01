import Foundation.PeriodicSpatialRowDependence
import Foundation.PeriodicCancellingBoundaryResponse
import Foundation.SU2OneWordLargeCoupling

/-! A worst-case spatial-neighbor influence test inside the original periodic
Wilson slab. The rough exterior is explicit; no typical-boundary estimate,
heat-bath commutator, stationary spectral gap or continuum claim is inferred. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace OperatorDerivativeRewrite.Foundation.PeriodicSpatialInfluenceObstruction
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicLinkStaples
open PeriodicCancellingBoundaryResponse
private abbrev vertexDecidableEq : DecidableEq SpatialVertex :=
  fun a b => Fintype.decidablePiFintype a b
attribute [local instance] vertexDecidableEq
attribute [local irreducible] spatialAction temporalAction boundaryHaar gaugeHaar spatialStaple incidentFaces

def neighbor : SpatialEdge := PeriodicSpatialRowDependence.neighbor
def flipped : State := Function.update flux neighbor 1

theorem flipped_agrees_away (j : SpatialEdge) (hj : j≠neighbor) : flipped j=flux j :=
  Function.update_of_ne hj _ _

theorem flipped_incident_sum (A : SU2) :
    (∑ p ∈ incidentFaces edge,halfTrace (spatialWord (Function.update flipped edge A) p))=
      2*halfTrace A := by
  rw [PeriodicCancellingBoundaryResponse.incident_exact]
  rw [Finset.sum_insert (by decide),Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),Finset.sum_singleton]
  have h01 : (0:ZMod 4)≠1 := by decide
  have h10 : (1:ZMod 4)≠0 := by decide
  have h30 : (3:ZMod 4)≠0 := by decide
  have h40 : (4:ZMod 4)=0 := by decide
  norm_num [spatialWord,flipped,neighbor,PeriodicSpatialRowDependence.neighbor,
    flux,edge,minusFace,plusFace,PeriodicTemporalSlab.shift,Function.update_apply,
    funext_iff,Fin.forall_fin_succ,h01,h10,h30,h40,
    SU2StrongCouplingCovariance.halfTrace_center_neg,SU2WilsonConvolution.halfTrace_inv,
    SU2OpenLinkGaugeObstruction.halfTrace_one,SU2OpenLinkGaugeObstruction.halfTrace_minusOne]
  <;> ring

theorem flipped_spatial_change (A : SU2) :
    spatialAction (Function.update flipped edge A)-spatialAction (Function.update flipped edge 1)=
      2*(1-halfTrace A) := by
  have hs := spatial_action_change flipped edge A
  have he (p : SpatialFace) (hp : p∈incidentFaces edge) :
      halfTrace (spatialStaple flipped edge p)-halfTrace (A*spatialStaple flipped edge p)=
        halfTrace (spatialWord (Function.update flipped edge 1) p)-
          halfTrace (spatialWord (Function.update flipped edge A) p) := by
    rw [spatial_trace_incident flipped edge p hp 1,spatial_trace_incident flipped edge p hp A,one_mul]
  rw [Finset.sum_congr rfl (fun p hp => he p hp),Finset.sum_sub_distrib,
    flipped_incident_sum,flipped_incident_sum,SU2OpenLinkGaugeObstruction.halfTrace_one] at hs
  linarith

theorem flipped_central_change (h : ℝ) (A : SU2) :
    PeriodicAugmentedBridge.centralAction (upper h) (lower h)
      (Function.update flipped edge A,(1,1))-
      PeriodicAugmentedBridge.centralAction (upper h) (lower h)
        (Function.update flipped edge 1,(1,1))=
          (2+2*Real.sin h)*(1-halfTrace A) := by
  have hs := flipped_spatial_change A
  have hl := temporal_action_change_left (upper h) flipped 1 edge A
  have hr := temporal_action_change_right flipped (lower h) 1 edge A
  have ht := temporal_pair_trace h A
  have h1 := temporal_pair_trace h 1
  simp only [one_mul,SU2OpenLinkGaugeObstruction.halfTrace_one] at h1
  unfold PeriodicAugmentedBridge.centralAction
  dsimp only
  nlinarith

def prefactor (β h : ℝ) : ℝ := localDensity β (upper h) flipped (lower h) 1 1 edge 1*
  Real.exp (-(β*(2+2*Real.sin h)))

theorem prefactor_pos (β h : ℝ) : 0<prefactor β h :=
  mul_pos (PeriodicAugmentedBridge.density_pos _ _ _ _) (Real.exp_pos _)

theorem density_factor (β h : ℝ) (A : SU2) :
    localDensity β (upper h) flipped (lower h) 1 1 edge A=
      prefactor β h*Real.exp ((β*(2+2*Real.sin h))*halfTrace A) := by
  have hc := flipped_central_change h A
  unfold prefactor localDensity
  rw [PeriodicAugmentedBridge.density_phase,PeriodicAugmentedBridge.density_phase]
  have he : -β*PeriodicAugmentedBridge.centralAction (upper h) (lower h)
      (Function.update flipped edge A,(1,1))=
      -β*PeriodicAugmentedBridge.centralAction (upper h) (lower h)
        (Function.update flipped edge 1,(1,1))-
          (β*(2+2*Real.sin h))+(β*(2+2*Real.sin h))*halfTrace A := by
    linear_combination -β*hc
  rw [he,Real.exp_add,Real.exp_sub,Real.exp_neg]
  field_simp [Real.exp_ne_zero]

def flippedLaw (β h : ℝ) : Measure SU2 := linkLaw β (upper h) flipped (lower h) 1 1 edge

theorem flipped_law_eq_tilt (β h : ℝ) : flippedLaw β h=
    BoundedExponentialTiltResponse.tiltedMeasure law halfTrace (β*(2+2*Real.sin h)) := by
  have hi : (∫ A,localDensity β (upper h) flipped (lower h) 1 1 edge A ∂law)=
      prefactor β h*BoundedExponentialTiltResponse.partition law halfTrace (β*(2+2*Real.sin h)) := by
    simp_rw [density_factor]
    rw [integral_const_mul]
    simp only [BoundedExponentialTiltResponse.partition,BoundedExponentialTiltResponse.weighted,one_mul]
  unfold flippedLaw linkLaw BoundedExponentialTiltResponse.tiltedMeasure
  congr 1
  funext A
  rw [density_factor,hi]
  unfold BoundedExponentialTiltResponse.density
  congr 1
  exact mul_div_mul_left _ _ (prefactor_pos β h).ne'

def parameter : ℝ := -(Real.pi/6)

theorem parameter_sine : 2*Real.sin parameter= -1 := by
  norm_num [parameter,Real.sin_neg,Real.sin_pi_div_six]

theorem minus_law (β : ℝ) : responseLaw β parameter=
    SU2OneWordTransfer.transition law β SU2StapleExtremes.minusOne := by
  rw [PeriodicCancellingBoundaryResponse.law_eq_tilt,SU2OneWordBoundaryInfluence.minus_law]
  congr 1
  calc
    2*β*Real.sin parameter=β*(2*Real.sin parameter) := by ring
    _ = -β := by rw [parameter_sine]; ring

theorem plus_law (β : ℝ) : flippedLaw β parameter=
    SU2OneWordTransfer.transition law β 1 := by
  rw [flipped_law_eq_tilt,SU2OneWordTransfer.transition_identity_law]
  congr 1
  rw [parameter_sine]
  ring

theorem flipped_observable_section (A : SU2) :
    observable (Function.update flipped edge A)=halfTrace A := by
  have h01 : (0:ZMod 4)≠1 := by decide
  have h10 : (1:ZMod 4)≠0 := by decide
  norm_num [observable,spatialWord,flipped,neighbor,PeriodicSpatialRowDependence.neighbor,
    plusFace,edge,flux,PeriodicTemporalSlab.shift,Function.update_apply,
    Prod.mk.injEq,funext_iff,Fin.forall_fin_succ,h01,h10]

def test (V : State) : ℝ := (1+observable V)/2

theorem test_range (V : State) : 0≤test V ∧ test V≤1 := by
  have hh := abs_le.mp (halfTrace_bound (spatialWord V (plusFace false)))
  change -1≤observable V ∧ observable V≤1 at hh
  unfold test
  constructor <;> linarith

theorem test_gauge (g : Gauge) (V : State) : test (PeriodicSlabGauge.gaugeAction g V)=test V := by
  unfold test
  rw [observable_gauge]

theorem test_continuous : Continuous test := by
  unfold test observable
  exact (continuous_const.add (PeriodicLowActionBlock.trace_continuous.comp
    (by unfold spatialWord; fun_prop))).div_const 2

/-- The changed input neighbor is absent from this complete physical plaquette.
Its later expectation change is therefore transmitted by the conditional law. -/
theorem test_neighbor_independent (V : State) (B : SU2) :
    test (Function.update V neighbor B)=test V := by
  have hn : plusFace false∉incidentFaces neighbor := by
    intro hh
    obtain ⟨k,hk⟩ := (mem_incidentFaces neighbor (plusFace false)).mp hh
    have hd := congrArg Prod.snd hk
    fin_cases k <;> norm_num [faceEdge,plusFace,neighbor,PeriodicSpatialRowDependence.neighbor] at hd
  unfold test observable
  rw [spatial_word_nonincident V neighbor (plusFace false) hn B]

private theorem observable_measurable : Measurable observable := by
  unfold observable
  exact halfTrace_measurable.comp (by unfold spatialWord; fun_prop)

def physicalMean (β : ℝ) (V : State) : ℝ := ∫ A,observable (Function.update V edge A)
  ∂linkLaw β (upper parameter) V (lower parameter) 1 1 edge

def testMean (β : ℝ) (V : State) : ℝ := ∫ A,test (Function.update V edge A)
  ∂linkLaw β (upper parameter) V (lower parameter) 1 1 edge

theorem testMean_eq (β : ℝ) (V : State) : testMean β V=(1+physicalMean β V)/2 := by
  let μ := linkLaw β (upper parameter) V (lower parameter) 1 1 edge
  letI : IsProbabilityMeasure μ := linkLaw_probability _ _ _ _ _ _ _
  have hi : Integrable (fun A => observable (Function.update V edge A)) μ := by
    apply Integrable.of_bound (observable_measurable.comp (by fun_prop)).aestronglyMeasurable 1
    filter_upwards with A
    exact halfTrace_bound _
  change (∫ A,(1+observable (Function.update V edge A))/2 ∂μ)=_
  rw [integral_div,integral_add (integrable_const 1) hi,integral_const,probReal_univ,one_smul]
  rfl

theorem testMean_range (β : ℝ) (V : State) : 0≤testMean β V ∧ testMean β V≤1 := by
  let μ := linkLaw β (upper parameter) V (lower parameter) 1 1 edge
  letI : IsProbabilityMeasure μ := linkLaw_probability _ _ _ _ _ _ _
  have hf : Continuous (fun A : SU2 => test (Function.update V edge A)) :=
    test_continuous.comp ((continuous_const : Continuous (fun _ : SU2 => V)).update edge continuous_id)
  have hi : Integrable (fun A => test (Function.update V edge A)) μ := by
    apply Integrable.of_bound hf.measurable.aestronglyMeasurable 1
    filter_upwards with A
    rw [Real.norm_eq_abs,abs_of_nonneg (test_range _).1]
    exact (test_range _).2
  refine ⟨integral_nonneg (fun A => (test_range _).1),?_⟩
  have hh := integral_mono hi (integrable_const (1:ℝ)) (fun A => (test_range _).2)
  simpa only [testMean,μ,integral_const,probReal_univ,one_smul] using hh

theorem physicalMean_minus (β : ℝ) : physicalMean β flux=
    ∫ A,halfTrace A ∂SU2OneWordTransfer.transition law β SU2StapleExtremes.minusOne := by
  change (∫ A,observable (Function.update flux edge A) ∂responseLaw β parameter)=_
  simp_rw [observable_section]
  rw [minus_law]

theorem physicalMean_plus (β : ℝ) : physicalMean β flipped=
    ∫ A,halfTrace A ∂SU2OneWordTransfer.transition law β 1 := by
  change (∫ A,observable (Function.update flipped edge A) ∂flippedLaw β parameter)=_
  simp_rw [flipped_observable_section]
  rw [plus_law]

/-- Same bounded gauge-invariant physical plaquette, actual row probabilities. -/
def influenceGap (β : ℝ) : ℝ := testMean β flipped-testMean β flux

theorem influenceGap_bound (β : ℝ) : |influenceGap β|≤1 := by
  have hp := testMean_range β flipped
  have hm := testMean_range β flux
  rw [abs_le]
  unfold influenceGap
  constructor <;> linarith

theorem influenceGap_tendsto : Tendsto influenceGap atTop (𝓝 1) := by
  have he : influenceGap=(fun β : ℝ =>
      ((∫ A,halfTrace A ∂SU2OneWordTransfer.transition law β 1)-
        ∫ A,halfTrace A ∂SU2OneWordTransfer.transition law β SU2StapleExtremes.minusOne)/2) := by
    funext β
    rw [influenceGap,testMean_eq,testMean_eq,physicalMean_plus,physicalMean_minus]
    ring
  rw [he]
  convert (SU2OneWordLargeCoupling.plus_mean_tendsto_one.sub
    SU2OneWordLargeCoupling.minus_mean_tendsto_neg_one).div_const 2 using 1 <;> norm_num

theorem eventually_exceeds (q : ℝ) (hq : q<1) : ∀ᶠ β : ℝ in atTop, q < influenceGap β :=
  influenceGap_tendsto.eventually (lt_mem_nhds hq)

/-- No worst-case single-neighbor oscillation budget below one survives all
large couplings on these actual rough-exterior row sections. -/
theorem no_uniform_neighbor_budget (q : ℝ) (hq : q<1) :
    ¬ ∃ β₀ : ℝ, ∀ β : ℝ, β₀≤β → ∀ V Z : State,
      (∀ j : SpatialEdge,j≠neighbor → V j=Z j) →
        |testMean β V-testMean β Z|≤q := by
  rintro ⟨β₀,hb⟩
  obtain ⟨β,hβ,hlarge⟩ := ((eventually_exceeds q hq).and (eventually_ge_atTop β₀)).exists
  have hh := hb β hlarge flipped flux flipped_agrees_away
  exact (not_lt_of_ge hh) (hβ.trans_le (le_abs_self _))

def flippedRest : PeriodicLinkDisintegration.Rest edge := ((fun j => flipped j.val),(1,1))

private theorem base_flipped_rest : PeriodicLinkDisintegration.baseField edge flippedRest=
    Function.update flipped edge 1 := by
  apply (PeriodicLinkDisintegration.coordinateSplit edge).injective
  rw [PeriodicLinkDisintegration.baseField,MeasurableEquiv.apply_symm_apply,
    PeriodicLinkDisintegration.coordinateSplit_apply]
  apply Prod.ext
  · simp only [Function.update_self]
  · funext j
    exact (Function.update_of_ne j.property 1 flipped).symm

theorem actual_flipped_kernel (β h : ℝ) :
    PeriodicLinkDisintegration.conditionalKernel edge β (upper h) (lower h) flippedRest=flippedLaw β h := by
  rw [PeriodicLinkDisintegration.kernel_eq_linkLaw,base_flipped_rest,linkLaw_update_base]
  rfl

theorem actual_kernel_plus (β : ℝ) :
    PeriodicLinkDisintegration.conditionalKernel edge β (upper parameter) (lower parameter) flippedRest=
      SU2OneWordTransfer.transition law β 1 := by rw [actual_flipped_kernel,plus_law]

theorem actual_kernel_minus (β : ℝ) :
    PeriodicLinkDisintegration.conditionalKernel edge β (upper parameter) (lower parameter)
      PeriodicCancellingBoundaryResponse.rest=
        SU2OneWordTransfer.transition law β SU2StapleExtremes.minusOne := by
  rw [PeriodicCancellingBoundaryResponse.actual_kernel_section,minus_law]

abbrev Space := PeriodicAugmentedBridge.Space

def rowTest (β : ℝ) (q : Space) : ℝ :=
  ∫ A,test (Function.update q.1 edge A)
    ∂linkLaw β (upper parameter) q.1 (lower parameter) q.2.1 q.2.2 edge

/-- Exact saved conditional kernel at arbitrary original joint coordinates. -/
theorem row_kernel_at (β : ℝ) (q : Space) :
    linkLaw β (upper parameter) q.1 (lower parameter) q.2.1 q.2.2 edge=
      PeriodicLinkDisintegration.conditionalKernel edge β (upper parameter) (lower parameter)
        ((PeriodicLinkDisintegration.split edge q).1) := by
  have hh := PeriodicLinkDisintegration.assemble edge
    ((PeriodicLinkDisintegration.split edge q).1) ((PeriodicLinkDisintegration.split edge q).2)
  rw [Prod.eta,(PeriodicLinkDisintegration.split edge).symm_apply_apply] at hh
  have hb : Function.update
      (PeriodicLinkDisintegration.baseField edge ((PeriodicLinkDisintegration.split edge q).1))
      edge (q.1 edge)=q.1 := by
    simpa only [PeriodicLinkDisintegration.split_apply] using (congrArg Prod.fst hh).symm
  have hu (A : SU2) : Function.update
      (PeriodicLinkDisintegration.baseField edge ((PeriodicLinkDisintegration.split edge q).1))
      edge A=Function.update q.1 edge A := by rw [← hb,Function.update_idem]
  rw [PeriodicLinkDisintegration.kernel_eq_linkLaw]
  unfold linkLaw localDensity
  simp_rw [hu]
  have ht : ((PeriodicLinkDisintegration.split edge q).1.2)=q.2 := rfl
  simp_rw [ht]

theorem rowTest_conditional (β : ℝ) (q : Space) : rowTest β q=
    ∫ A,test (Function.update q.1 edge A)
      ∂PeriodicLinkDisintegration.conditionalKernel edge β (upper parameter) (lower parameter)
        ((PeriodicLinkDisintegration.split edge q).1) := by
  unfold rowTest
  rw [row_kernel_at]

private def jointRaw (β : ℝ) (q : Space) (A : SU2) : ℝ :=
  localDensity β (upper parameter) q.1 (lower parameter) q.2.1 q.2.2 edge A

private theorem jointRaw_continuous (β : ℝ) : Continuous (fun p : Space × SU2 => jointRaw β p.1 p.2) := by
  have hu : Continuous (fun p : Space × SU2 => Function.update p.1.1 edge p.2) :=
    (continuous_fst.comp continuous_fst).update edge continuous_snd
  have hw : Continuous (fun p : (State × State) × Gauge => weight β p.1.1 p.1.2 p.2) := by
    unfold weight
    exact Real.continuous_exp.comp (PeriodicLowActionBlock.action_continuous.const_mul (-β))
  have h1 : Continuous (fun p : Space × SU2 =>
      ((upper parameter,Function.update p.1.1 edge p.2),p.1.2.1)) :=
    (continuous_const.prodMk hu).prodMk (continuous_fst.comp (continuous_snd.comp continuous_fst))
  have h2 : Continuous (fun p : Space × SU2 =>
      ((Function.update p.1.1 edge p.2,lower parameter),p.1.2.2)) :=
    (hu.prodMk continuous_const).prodMk (continuous_snd.comp (continuous_snd.comp continuous_fst))
  exact (hw.comp h1).mul (hw.comp h2)

private theorem haar_integral_continuous (F : Space × SU2 → ℝ) (hF : Continuous F) :
    Continuous (fun q => ∫ A,F (q,A) ∂law) := by
  have hh := continuous_parametric_integral_of_continuous (μ := law)
    (f := fun q A => F (q,A)) hF (s := Set.univ) isCompact_univ
  simpa only [Measure.restrict_univ] using hh

theorem rowTest_quotient (β : ℝ) (q : Space) :
    rowTest β q=(∫ A,test (Function.update q.1 edge A)*jointRaw β q A ∂law)/
      (∫ A,jointRaw β q A ∂law) := by
  have hh := normalized_link_integral β (upper parameter) q.1 (lower parameter) q.2.1 q.2.2 edge
    (fun A => test (Function.update q.1 edge A))
  rw [← linkLaw_eq_stapleLaw] at hh
  exact hh.symm

theorem rowTest_continuous (β : ℝ) : Continuous (rowTest β) := by
  have hu : Continuous (fun p : Space × SU2 => Function.update p.1.1 edge p.2) :=
    (continuous_fst.comp continuous_fst).update edge continuous_snd
  have hn := haar_integral_continuous
    (fun p => test (Function.update p.1.1 edge p.2)*jointRaw β p.1 p.2)
    ((test_continuous.comp hu).mul (jointRaw_continuous β))
  have hd := haar_integral_continuous _ (jointRaw_continuous β)
  have he : rowTest β=(fun q => (∫ A,test (Function.update q.1 edge A)*jointRaw β q A ∂law)/
      (∫ A,jointRaw β q A ∂law)) := funext (rowTest_quotient β)
  rw [he]
  exact hn.div hd (fun q => (localDensity_integral_pos β (upper parameter) q.1
    (lower parameter) q.2.1 q.2.2 edge).ne')

theorem neighborFlip_flux : PeriodicSpatialRowDependence.neighborFlip (flux,(1,1))=(flipped,(1,1)) := by
  apply Prod.ext
  · change PeriodicSpatialRowDependence.field SU2StapleExtremes.minusOne*flux=flipped
    funext j
    by_cases hj : j=neighbor
    · subst j
      have hf : flux neighbor=SU2StapleExtremes.minusOne := by
        norm_num [flux,neighbor,PeriodicSpatialRowDependence.neighbor,PeriodicTemporalSlab.shift]
      change PeriodicSpatialRowDependence.field SU2StapleExtremes.minusOne neighbor*flux neighbor=
        Function.update flux neighbor 1 neighbor
      have hv : PeriodicSpatialRowDependence.field SU2StapleExtremes.minusOne neighbor=
          SU2StapleExtremes.minusOne := by
        unfold PeriodicSpatialRowDependence.field neighbor
        rw [Function.update_self]
      rw [hv,Function.update_self,hf,PeriodicCenterSeam.center_square]
    · rw [flipped_agrees_away j hj]
      change PeriodicSpatialRowDependence.field SU2StapleExtremes.minusOne j*flux j=flux j
      have hv : PeriodicSpatialRowDependence.field SU2StapleExtremes.minusOne j=1 := by
        unfold PeriodicSpatialRowDependence.field
        rw [Function.update_of_ne (show j≠PeriodicSpatialRowDependence.neighbor from hj)]
        rfl
      rw [hv,one_mul]
  · rfl

/-- The support bridge uses these actual endpoints, not the identity-endpoint
specialization from the preceding checkpoint. -/
theorem boundary_ae_iff (β : ℝ) (P : Space → Prop) :
    (∀ᵐ q ∂PeriodicAugmentedBridge.law β (upper parameter) (lower parameter),P q) ↔
      ∀ᵐ q ∂PeriodicAugmentedBridge.reference,P q := by
  rw [PeriodicLinkDisintegration.augmented_withDensity,ae_withDensity_iff
    ((PeriodicAugmentedBridge.density_measurable β (upper parameter) (lower parameter)).div_const _).ennreal_ofReal]
  constructor
  · intro hh
    filter_upwards [hh] with q hq
    exact hq (ne_of_gt (ENNReal.ofReal_pos.mpr (div_pos
      (PeriodicAugmentedBridge.density_pos β (upper parameter) (lower parameter) q)
      (PeriodicGroundBridge.normalizer_pos β (upper parameter) (lower parameter)))))
  · intro hh
    filter_upwards [hh] with q hq
    exact fun _ => hq

theorem neighborFlip_ae (β : ℝ) (P : Space → Prop)
    (hh : ∀ᵐ q ∂PeriodicAugmentedBridge.law β (upper parameter) (lower parameter),P q) :
    ∀ᵐ q ∂PeriodicAugmentedBridge.law β (upper parameter) (lower parameter),
      P (PeriodicSpatialRowDependence.neighborFlip q) := by
  exact (boundary_ae_iff β _).mpr
    (PeriodicSpatialRowDependence.neighborFlip_reference_preserving.quasiMeasurePreserving.ae
      ((boundary_ae_iff β P).mp hh))

/-- Every fixed q<1 eventually fails even as an AE absolute neighbor-influence
bound under the original full augmented law. No lower bound on the probability
of its violating rough-rest region, uniform in beta, is inferred. -/
theorem eventually_no_ae_neighbor_budget (c : ℝ) (hc : c<1) :
    ∀ᶠ β : ℝ in atTop,
      ¬ ∀ᵐ q ∂PeriodicAugmentedBridge.law β (upper parameter) (lower parameter),
        |rowTest β (PeriodicSpatialRowDependence.neighborFlip q)-rowTest β q|≤c := by
  filter_upwards [eventually_exceeds c hc] with β hβ
  intro hh
  have hz : ∀ᵐ q ∂PeriodicAugmentedBridge.reference,
      max ((rowTest β (PeriodicSpatialRowDependence.neighborFlip q)-rowTest β q)-c) 0=0 := by
    apply (boundary_ae_iff β _).mp
    filter_upwards [hh] with q hq
    exact max_eq_right (sub_nonpos.mpr ((le_abs_self _).trans hq))
  have hg : Continuous (fun q =>
      max ((rowTest β (PeriodicSpatialRowDependence.neighborFlip q)-rowTest β q)-c) 0) :=
    (((((rowTest_continuous β).comp PeriodicSpatialRowDependence.neighborFlip_continuous).sub
      (rowTest_continuous β)).sub continuous_const).max continuous_const)
  have he := Measure.eq_of_ae_eq hz hg continuous_const
  have hp := congrFun he (flux,(1,1))
  rw [neighborFlip_flux] at hp
  change max (influenceGap β-c) 0=0 at hp
  have hpos : 0<max (influenceGap β-c) 0 :=
    lt_of_lt_of_le (sub_pos.mpr hβ) (le_max_left _ _)
  exact hpos.ne' hp

/-- The obstruction is unchanged by choosing any other AE version of the
original conditional mean, including coupling-dependent choices of versions. -/
theorem eventually_no_ae_version_neighbor_budget (c : ℝ) (hc : c<1) :
    ∀ᶠ β : ℝ in atTop, ∀ F : Space → ℝ,
      F =ᵐ[PeriodicAugmentedBridge.law β (upper parameter) (lower parameter)] rowTest β →
        ¬ ∀ᵐ q ∂PeriodicAugmentedBridge.law β (upper parameter) (lower parameter),
          |F (PeriodicSpatialRowDependence.neighborFlip q)-F q|≤c := by
  filter_upwards [eventually_no_ae_neighbor_budget c hc] with β hn
  intro F hF hbudget
  apply hn
  have hflip := neighborFlip_ae β _ hF
  filter_upwards [hF,hflip,hbudget] with q hq hf hb
  rwa [hf,hq] at hb

end OperatorDerivativeRewrite.Foundation.PeriodicSpatialInfluenceObstruction
