import Foundation.PeriodicStationaryEndpointResponse
import Foundation.SU2QuadraticWilsonChannel
/-! A nontriviality audit of coherent endpoint response under actual gauge symmetry.
No physical response is discarded before the exact change of variables is proved. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion ENNReal
namespace OperatorDerivativeRewrite.Foundation.PeriodicEndpointWard
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGauge
open PeriodicGaugeSaturatedGround PeriodicSlabGround
attribute [local irreducible] spatialAction temporalAction boundaryHaar gaugeHaar kernel

def field (c : SU2) : State → State := gaugeAction (fun _ => c)
def temporal (c : SU2) (a : Gauge) : Gauge := fun v => c*a v*c⁻¹

def fieldEquiv (c : SU2) : State ≃ᵐ State := gaugeEquiv (fun _ => c)
def temporalEquiv (c : SU2) : Gauge ≃ᵐ Gauge :=
  (MeasurableEquiv.mulLeft (fun _ : SpatialVertex => c)).trans
    (MeasurableEquiv.mulRight (fun _ : SpatialVertex => c⁻¹))

theorem fieldEquiv_apply (c : SU2) (U : State) : fieldEquiv c U=field c U := rfl
theorem temporalEquiv_apply (c : SU2) (a : Gauge) : temporalEquiv c a=temporal c a := rfl

def augmented (c : SU2) : PeriodicAugmentedBridge.Space ≃ᵐ PeriodicAugmentedBridge.Space :=
  (fieldEquiv c).prodCongr ((temporalEquiv c).prodCongr (temporalEquiv c))

theorem augmented_apply (c : SU2) (q : PeriodicAugmentedBridge.Space) :
    augmented c q=(field c q.1,(temporal c q.2.1,temporal c q.2.2)) := rfl

theorem field_preserving (c : SU2) : MeasurePreserving (field c) boundaryHaar boundaryHaar :=
  action_boundary_preserving (fun _ => c)

theorem temporal_preserving (c : SU2) : MeasurePreserving (temporal c) gaugeHaar gaugeHaar := by
  unfold temporal gaugeHaar
  exact measurePreserving_pi (fun _ : SpatialVertex => QuaternionSU2Representation.law)
    (fun _ : SpatialVertex => QuaternionSU2Representation.law)
    (fun _ => (measurePreserving_mul_right QuaternionSU2Representation.law c⁻¹).comp
      (measurePreserving_mul_left QuaternionSU2Representation.law c))

theorem augmented_preserving (c : SU2) :
    MeasurePreserving (augmented c) PeriodicAugmentedBridge.reference PeriodicAugmentedBridge.reference :=
  (field_preserving c).prod ((temporal_preserving c).prod (temporal_preserving c))

theorem temporal_word (c : SU2) (U V : State) (a : Gauge) (e : SpatialEdge) :
    temporalWord (field c U) (field c V) (temporal c a) e=c*temporalWord U V a e*c⁻¹ := by
  unfold temporalWord field temporal gaugeAction
  group

theorem weight_invariant (β : ℝ) (c : SU2) (U V : State) (a : Gauge) :
    weight β (field c U) (field c V) (temporal c a)=weight β U V a := by
  unfold weight halfAction temporalAction
  rw [show spatialAction (field c U)=spatialAction U from spatial_action_invariant _ _,
    show spatialAction (field c V)=spatialAction V from spatial_action_invariant _ _]
  simp_rw [temporal_word,halfTrace_conjugate]

theorem density_invariant (β : ℝ) (c : SU2) (U W : State) (q : PeriodicAugmentedBridge.Space) :
    PeriodicAugmentedBridge.density β (field c U) (field c W) (augmented c q)=
      PeriodicAugmentedBridge.density β U W q := by
  simp only [PeriodicAugmentedBridge.density,augmented_apply,weight_invariant]

theorem normalizer_invariant (β : ℝ) (c : SU2) (U W : State) :
    PeriodicGroundBridge.normalizer β (field c U) (field c W)=PeriodicGroundBridge.normalizer β U W := by
  unfold PeriodicGroundBridge.normalizer PeriodicGroundBridge.bridgeWeight field
  simp_rw [kernel_left_invariant,kernel_right_invariant]

/-- Actual conditional bridge transport, valid even for unbounded integrable probes. -/
theorem bridge_integral (β : ℝ) (c : SU2) (U W : State) (f : PeriodicAugmentedBridge.Space → ℝ) :
    (∫ q,f (augmented c q) ∂PeriodicAugmentedBridge.law β U W)=
      ∫ q,f q ∂PeriodicAugmentedBridge.law β (field c U) (field c W) := by
  rw [PeriodicAugmentedBridge.integral_formula,PeriodicAugmentedBridge.integral_formula,normalizer_invariant]
  have h := (augmented_preserving c).integral_comp (augmented c).measurableEmbedding
    (fun q => PeriodicAugmentedBridge.density β (field c U) (field c W) q*f q)
  simp_rw [density_invariant] at h
  exact congrArg (fun x => x/PeriodicGroundBridge.normalizer β U W) h

def flip : SU2 := hom ⟨SU2QuadraticWilsonChannel.axisRaw 2,SU2QuadraticWilsonChannel.axis_unitary 2⟩

theorem flip_axis (h : ℝ) :
    flip*SU2JointPlaquetteCubic.axis 0 h*flip⁻¹=SU2JointPlaquetteCubic.axis 0 (-h) := by
  unfold flip SU2JointPlaquetteCubic.axis
  rw [← map_inv,← map_mul,← map_mul]
  apply congrArg hom
  apply Subtype.ext
  change SU2QuadraticWilsonChannel.axisRaw 2*SU2JointPlaquetteCubic.axisRaw 0 h*
    star (SU2QuadraticWilsonChannel.axisRaw 2)=SU2JointPlaquetteCubic.axisRaw 0 (-h)
  rw [SU2QuadraticWilsonChannel.axis_conjugate]
  ext <;> simp [SU2QuadraticWilsonChannel.flipRaw,SU2JointPlaquetteCubic.axisRaw,Real.cos_neg,Real.sin_neg]

theorem left_flip (h : ℝ) (U : State) :
    PeriodicEndpointScore.left h (field flip U)=field flip (PeriodicEndpointScore.left (-h) U) := by
  funext e
  change SU2JointPlaquetteCubic.axis 0 h*(flip*U e*flip⁻¹)=
    flip*(SU2JointPlaquetteCubic.axis 0 (-h)*U e)*flip⁻¹
  rw [← neg_neg h,← flip_axis (-h)]
  group

theorem right_flip (h : ℝ) (W : State) :
    PeriodicEndpointScore.right h (field flip W)=field flip (PeriodicEndpointScore.right (-h) W) := by
  funext e
  change (flip*W e*flip⁻¹)*SU2JointPlaquetteCubic.axis 0 (-h)=
    flip*(W e*SU2JointPlaquetteCubic.axis 0 (-(-h)))*flip⁻¹
  rw [neg_neg,← flip_axis h]
  group

theorem traceSum_invariant (c : SU2) (U W : State) (q : PeriodicAugmentedBridge.Space) :
    PeriodicEndpointScore.traceSum (field c U) (field c W) (augmented c q)=
      PeriodicEndpointScore.traceSum U W q := by
  simp only [PeriodicEndpointScore.traceSum,augmented_apply,temporal_word,halfTrace_conjugate]

theorem direction_odd (U W : State) (q : PeriodicAugmentedBridge.Space) :
    PeriodicEndpointScore.direction (field flip U) (field flip W) (augmented flip q)=
      -PeriodicEndpointScore.direction U W q := by
  unfold PeriodicEndpointScore.direction
  rw [left_flip,right_flip,traceSum_invariant,PeriodicEndpointScore.traceSum_rotation]
  simp only [Real.cos_neg,Real.sin_neg,Real.cos_pi_div_two,Real.sin_pi_div_two,zero_mul,neg_mul,one_mul,zero_add]

theorem score_odd (β : ℝ) (U W : State) (q : PeriodicAugmentedBridge.Space) :
    PeriodicEndpointScore.score β (field flip U) (field flip W) (augmented flip q)=
      -PeriodicEndpointScore.score β U W q := by
  have h := bridge_integral β flip U W (PeriodicEndpointScore.direction (field flip U) (field flip W))
  simp_rw [direction_odd] at h
  rw [integral_neg] at h
  unfold PeriodicEndpointScore.score
  rw [direction_odd,← h]
  ring

def endpoints (c : SU2) : (State × State) ≃ᵐ (State × State) := (fieldEquiv c).prodCongr (fieldEquiv c)
def whole (c : SU2) : PeriodicStationaryEndpointResponse.Space ≃ᵐ PeriodicStationaryEndpointResponse.Space :=
  (endpoints c).prodCongr (augmented c)

private theorem preserving_of_integrals {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (T : Ω ≃ᵐ Ω)
    (h : ∀ f : Ω → ℝ,Measurable f → (∀ x,|f x|≤1) → (∫ x,f (T x) ∂μ)=∫ x,f x ∂μ) :
    MeasurePreserving T μ μ := by
  refine ⟨T.measurable,?_⟩
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply T.measurable hS]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have hi := h (S.indicator (fun _ => (1:ℝ))) (measurable_const.indicator hS)
    (fun x => by by_cases hx : x∈S <;> simp [hx])
  have he : (fun x => S.indicator (fun _ => (1:ℝ)) (T x))=
      (T ⁻¹' S).indicator (fun _ => (1:ℝ)) := by
    funext x
    by_cases hx : T x∈S <;> simp [hx]
  rw [he] at hi
  have hL := integral_indicator_one (μ := μ) (T.measurable hS)
  have hR := integral_indicator_one (μ := μ) hS
  exact hL.symm.trans (hi.trans hR)

variable {β : ℝ} (g : GroundData β)

theorem twoStep_invariant (c : SU2) (U W : State) :
    PeriodicGroundBridge.twoStepDensity g (field c U) (field c W)=PeriodicGroundBridge.twoStepDensity g U W := by
  rw [PeriodicGroundBridge.twoStep_factor,PeriodicGroundBridge.twoStep_factor,normalizer_invariant]
  simp only [field,g.invariant]

private theorem endpoint_integral (f : State × State → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ p,|f p|≤B) :
    (∫ p,f p ∂PeriodicStationaryEndpointResponse.endpointLaw g)=
      (∫ U,g.function U^2*(∫ W,PeriodicGroundBridge.twoStepDensity g U W*f (U,W)
        ∂boundaryHaar) ∂boundaryHaar)/g.normalizer := by
  letI := g.stationary_probability
  letI := g.transition_markov
  have hi : Integrable f (PeriodicStationaryEndpointResponse.endpointLaw g) :=
    Integrable.of_bound hf.aestronglyMeasurable B (ae_of_all _ (fun p => by
      simpa only [Real.norm_eq_abs] using hb p))
  rw [PeriodicStationaryEndpointResponse.endpointLaw,Measure.integral_compProd hi]
  have hh (U : State) := PeriodicGroundBridge.composed_transition_integral g U (fun W => f (U,W))
    (hf.comp (measurable_const.prodMk measurable_id)) B (fun W => hb (U,W))
  simp_rw [hh]
  exact g.stationary_integral _

theorem endpoint_integral_invariant (c : SU2) (f : State × State → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ p,|f p|≤B) :
    (∫ p,f (endpoints c p) ∂PeriodicStationaryEndpointResponse.endpointLaw g)=
      ∫ p,f p ∂PeriodicStationaryEndpointResponse.endpointLaw g := by
  rw [endpoint_integral g (fun p => f (endpoints c p)) (hf.comp (endpoints c).measurable) B (fun p => hb _),
    endpoint_integral g f hf B hb]
  have hrow (U : State) :
      (∫ W,PeriodicGroundBridge.twoStepDensity g U W*f (field c U,field c W) ∂boundaryHaar)=
        ∫ W,PeriodicGroundBridge.twoStepDensity g (field c U) W*f (field c U,W) ∂boundaryHaar := by
    have h := (field_preserving c).integral_comp (fieldEquiv c).measurableEmbedding
      (fun W => PeriodicGroundBridge.twoStepDensity g (field c U) W*f (field c U,W))
    simpa only [twoStep_invariant] using h
  change (∫ U,g.function U^2*(∫ W,PeriodicGroundBridge.twoStepDensity g U W*f (field c U,field c W)
    ∂boundaryHaar) ∂boundaryHaar)/g.normalizer=_
  simp_rw [hrow]
  have h := (field_preserving c).integral_comp (fieldEquiv c).measurableEmbedding
    (fun U => g.function U^2*(∫ W,PeriodicGroundBridge.twoStepDensity g U W*f (U,W) ∂boundaryHaar))
  simp only [field,g.invariant] at h
  exact congrArg (fun x => x/g.normalizer) h

theorem endpoint_preserving (c : SU2) :
    MeasurePreserving (endpoints c) (PeriodicStationaryEndpointResponse.endpointLaw g)
      (PeriodicStationaryEndpointResponse.endpointLaw g) := by
  apply preserving_of_integrals
  intro f hf hb
  exact endpoint_integral_invariant g c f hf 1 hb

theorem joint_integral_invariant (c : SU2) (f : PeriodicStationaryEndpointResponse.Space → ℝ)
    (hf : Measurable f) (B : ℝ) (hb : ∀ p,|f p|≤B) :
    (∫ p,f (whole c p) ∂PeriodicStationaryEndpointResponse.law g)=
      ∫ p,f p ∂PeriodicStationaryEndpointResponse.law g := by
  have hi : Integrable f (PeriodicStationaryEndpointResponse.law g) :=
    Integrable.of_bound hf.aestronglyMeasurable B (ae_of_all _ (fun p => by
      simpa only [Real.norm_eq_abs] using hb p))
  have ht : Integrable (fun p => f (whole c p)) (PeriodicStationaryEndpointResponse.law g) :=
    Integrable.of_bound (hf.comp (whole c).measurable).aestronglyMeasurable B (ae_of_all _ (fun p => by
      simpa only [Real.norm_eq_abs] using hb (whole c p)))
  rw [PeriodicStationaryEndpointResponse.law,Measure.integral_compProd ht,Measure.integral_compProd hi]
  simp_rw [PeriodicStationaryEndpointResponse.bridgeKernel_apply]
  have hr (p : State × State) :
      (∫ q,f (whole c (p,q)) ∂PeriodicAugmentedBridge.law β p.1 p.2)=
        ∫ q,f (endpoints c p,q) ∂PeriodicAugmentedBridge.law β (field c p.1) (field c p.2) :=
    bridge_integral β c p.1 p.2 (fun q => f (endpoints c p,q))
  simp_rw [hr]
  exact (endpoint_preserving g c).integral_comp (endpoints c).measurableEmbedding
    (fun p => ∫ q,f (p,q) ∂PeriodicAugmentedBridge.law β p.1 p.2)

theorem joint_preserving (c : SU2) :
    MeasurePreserving (whole c) (PeriodicStationaryEndpointResponse.law g)
      (PeriodicStationaryEndpointResponse.law g) := by
  apply preserving_of_integrals
  intro f hf hb
  exact joint_integral_invariant g c f hf 1 hb

theorem badScore_odd (p : PeriodicStationaryEndpointResponse.Space) :
    PeriodicStationaryEndpointResponse.badScore (β := β) (whole flip p)=
      -PeriodicStationaryEndpointResponse.badScore (β := β) p := by
  have hi := PeriodicCancellingRestTail.bad_gauge_iff (fun _ => flip) p.2.1
  by_cases hp : p.2.1∈PeriodicCancellingRestTail.bad
  · have ht : (whole flip p).2.1∈PeriodicCancellingRestTail.bad := hi.mpr hp
    have h0 : p∈(fun p : PeriodicStationaryEndpointResponse.Space => p.2.1) ⁻¹' PeriodicCancellingRestTail.bad := hp
    have h1 : whole flip p∈(fun p : PeriodicStationaryEndpointResponse.Space => p.2.1) ⁻¹' PeriodicCancellingRestTail.bad := ht
    simp only [PeriodicStationaryEndpointResponse.badScore,Set.indicator_of_mem h0,Set.indicator_of_mem h1,
      PeriodicStationaryEndpointResponse.score]
    exact score_odd β p.1.1 p.1.2 p.2
  · have ht : (whole flip p).2.1∉PeriodicCancellingRestTail.bad := fun h => hp (hi.mp h)
    have h0 : p∉(fun p : PeriodicStationaryEndpointResponse.Space => p.2.1) ⁻¹' PeriodicCancellingRestTail.bad := hp
    have h1 : whole flip p∉(fun p : PeriodicStationaryEndpointResponse.Space => p.2.1) ⁻¹' PeriodicCancellingRestTail.bad := ht
    simp only [PeriodicStationaryEndpointResponse.badScore,Set.indicator_of_notMem h0,Set.indicator_of_notMem h1,neg_zero]

private theorem odd_pairing (f : State → ℝ) (hInv : ∀ a V,f (gaugeAction a V)=f V)
    (s : PeriodicStationaryEndpointResponse.Space → ℝ) (hs : ∀ p,s (whole flip p)=-s p) :
    (∫ p,f p.2.1*s p ∂PeriodicStationaryEndpointResponse.law g)=0 := by
  have h := (joint_preserving g flip).integral_comp (whole flip).measurableEmbedding
    (fun p => f p.2.1*s p)
  have he (p : PeriodicStationaryEndpointResponse.Space) :
      f (whole flip p).2.1*s (whole flip p)=-(f p.2.1*s p) := by
    change f (gaugeAction (fun _ => flip) p.2.1)*s (whole flip p)=_
    rw [hInv,hs]
    ring
  simp_rw [he] at h
  rw [integral_neg] at h
  linarith

/-- Genuine stationary-averaged Ward cancellation, on the ORIGINAL native L2
physical domain. The pairing is integrable before the zero identity is used. -/
theorem physical_score_pairing (f : State → ℝ) (hm : MemLp f 2 g.stationary)
    (hInv : ∀ a V,f (gaugeAction a V)=f V) :
    Integrable (fun p : PeriodicStationaryEndpointResponse.Space => f p.2.1*PeriodicStationaryEndpointResponse.score (β := β) p)
      (PeriodicStationaryEndpointResponse.law g) ∧
    (∫ p,f p.2.1*PeriodicStationaryEndpointResponse.score (β := β) p ∂PeriodicStationaryEndpointResponse.law g)=0 := by
  constructor
  · exact (hm.comp_measurePreserving (PeriodicStationaryEndpointResponse.middle_preserving g)).integrable_mul
      (PeriodicStationaryEndpointResponse.score_memLp g)
  · apply odd_pairing g f hInv
    intro p
    exact score_odd β p.1.1 p.1.2 p.2

theorem physical_bad_pairing (f : State → ℝ) (hm : MemLp f 2 g.stationary)
    (hInv : ∀ a V,f (gaugeAction a V)=f V) :
    Integrable (fun p : PeriodicStationaryEndpointResponse.Space => f p.2.1*PeriodicStationaryEndpointResponse.badScore (β := β) p)
      (PeriodicStationaryEndpointResponse.law g) ∧
    (∫ p,f p.2.1*PeriodicStationaryEndpointResponse.badScore (β := β) p ∂PeriodicStationaryEndpointResponse.law g)=0 := by
  constructor
  · exact (hm.comp_measurePreserving (PeriodicStationaryEndpointResponse.middle_preserving g)).integrable_mul
      (PeriodicStationaryEndpointResponse.badScore_memLp g)
  · exact odd_pairing g f hInv _ (badScore_odd (β := β))

/-- The actual bad score has ZERO realization on the completed physical high
space. Closure is handled by a continuous native pairing, without asserting that
every completed field has a pointwise invariant representative. -/
theorem bad_realization_zero (K : ℝ) :
    PeriodicStationaryEndpointResponse.realization g K (PeriodicStationaryEndpointResponse.badScoreField g)=0 := by
  let Z := PeriodicStationaryEndpointResponse.badScoreField g
  let C := HilbertRepresentation.predictableAdjoint (PeriodicStationaryEndpointResponse.middleEmbedding g) Z
  have hcore : (PeriodicHighActionL2.represented g K : Set (PeriodicSlabL2.StateL2 g)) ⊆
      {F | inner ℝ C F=0} := by
    rintro F ⟨f,hf,hm,hInv,hs,rfl⟩
    have he : inner ℝ C (hm.toLp f)=
        ∫ p,f p.2.1*PeriodicStationaryEndpointResponse.badScore (β := β) p
          ∂PeriodicStationaryEndpointResponse.law g := by
      dsimp only [C]
      rw [HilbertRepresentation.predictableAdjoint_pairing,L2.inner_def]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_compMeasurePreserving (hm.toLp f)
        (PeriodicStationaryEndpointResponse.middle_preserving g),
        (PeriodicStationaryEndpointResponse.middle_preserving g).quasiMeasurePreserving.ae_eq_comp hm.coeFn_toLp,
        (PeriodicStationaryEndpointResponse.badScore_memLp g).coeFn_toLp] with p hE hf hZ
      change inner ℝ (Z p) (PeriodicStationaryEndpointResponse.middleEmbedding g (hm.toLp f) p)=_
      change PeriodicStationaryEndpointResponse.middleEmbedding g (hm.toLp f) p=hm.toLp f p.2.1 at hE
      change Z p=PeriodicStationaryEndpointResponse.badScore p at hZ
      change hm.toLp f p.2.1=f p.2.1 at hf
      rw [hE,hf,hZ]
      rfl
    exact he.trans (physical_bad_pairing g f hm hInv).2
  have hclosed : IsClosed {F : PeriodicSlabL2.StateL2 g | inner ℝ C F=0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hall := closure_minimal hcore hclosed
  apply ext_inner_right ℝ
  intro F
  have hmem : (F : PeriodicSlabL2.StateL2 g)∈closure (PeriodicHighActionL2.represented g K : Set (PeriodicSlabL2.StateL2 g)) :=
    F.property
  have hF : inner ℝ C (F : PeriodicSlabL2.StateL2 g)=0 := hall hmem
  rw [PeriodicStationaryEndpointResponse.realization_eq_projection,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  simpa only [inner_zero_left] using hF

/-- Therefore the preceding Gaussian high response bound has identically zero
physical signal for THIS stationary-averaged coherent-axis source. -/
theorem bad_gaussian_zero (hb : 0≤β) (K : ℝ) :
    PeriodicStationaryEndpointResponse.gaussianResponse hb g K
      (PeriodicStationaryEndpointResponse.badScoreField g)=0 := by
  simp only [PeriodicStationaryEndpointResponse.gaussianResponse,ContinuousLinearMap.comp_apply,
    bad_realization_zero,map_zero]
end OperatorDerivativeRewrite.Foundation.PeriodicEndpointWard
