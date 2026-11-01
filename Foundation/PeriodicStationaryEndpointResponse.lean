import Foundation.PeriodicConditionalEndpointScore
import Foundation.PeriodicJointHighResponse
/-! Actual stationary two-slab endpoint-score realization in original native norms.
The endpoint law is stationary times the actual TWO-step transition; the
conditional augmented law is the genuine Wilson bridge, with both normalizers.
Only the explicitly projected physical high response is controlled. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.PeriodicStationaryEndpointResponse
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround
open PeriodicSlabL2 PeriodicNativeGaussianAnalysis
attribute [local irreducible] spatialAction temporalAction boundaryHaar gaugeHaar kernel
abbrev Space := (State × State) × PeriodicAugmentedBridge.Space

theorem density_measurable (β : ℝ) :
    Measurable (fun p : Space => PeriodicAugmentedBridge.density β p.1.1 p.1.2 p.2) := by
  have h1 : Measurable (fun p : Space => ((p.1.1,p.2.1),p.2.2.1)) := by fun_prop
  have h2 : Measurable (fun p : Space => ((p.2.1,p.1.2),p.2.2.2)) := by fun_prop
  unfold PeriodicAugmentedBridge.density
  exact ((weight_joint_measurable β).comp h1).mul ((weight_joint_measurable β).comp h2)

private theorem bridge_withDensity (β : ℝ) (U W : State) :
    PeriodicAugmentedBridge.law β U W=PeriodicAugmentedBridge.reference.withDensity
      (fun q => ENNReal.ofReal (PeriodicAugmentedBridge.density β U W q/PeriodicGroundBridge.normalizer β U W)) := by
  unfold PeriodicAugmentedBridge.law SignedDensityProbabilitySampling.sampler
  rw [PeriodicAugmentedBridge.mass_identity]
  unfold SignedAbsoluteIntegration.absoluteDensity
  simp_rw [abs_of_pos (PeriodicAugmentedBridge.density_pos β U W _)]
  rw [← withDensity_smul _ (PeriodicAugmentedBridge.density_measurable β U W).ennreal_ofReal]
  apply congrArg (fun f : PeriodicAugmentedBridge.Space → ℝ≥0∞ => PeriodicAugmentedBridge.reference.withDensity f)
  funext q
  change (ENNReal.ofReal (PeriodicGroundBridge.normalizer β U W))⁻¹*ENNReal.ofReal (PeriodicAugmentedBridge.density β U W q)=_
  rw [ENNReal.ofReal_div_of_pos (PeriodicGroundBridge.normalizer_pos β U W),div_eq_mul_inv]
  exact mul_comm _ _

def bridgeKernel (β : ℝ) : Kernel (State × State) PeriodicAugmentedBridge.Space :=
  (Kernel.const (State × State) PeriodicAugmentedBridge.reference).withDensity
    (fun p q => ENNReal.ofReal (PeriodicAugmentedBridge.density β p.1 p.2 q/PeriodicGroundBridge.normalizer β p.1 p.2))

theorem bridgeKernel_apply (β : ℝ) (p : State × State) :
    bridgeKernel β p=PeriodicAugmentedBridge.law β p.1 p.2 := by
  have hm := ((density_measurable β).div ((PeriodicGroundBridge.normalizer_measurable β).comp measurable_fst)).ennreal_ofReal
  unfold bridgeKernel
  rw [Kernel.withDensity_apply _ hm,bridge_withDensity]
  rfl

instance bridgeKernel_markov (β : ℝ) : IsMarkovKernel (bridgeKernel β) := by
  constructor
  intro p
  rw [bridgeKernel_apply]
  infer_instance

variable {β : ℝ} (g : GroundData β)

def endpointLaw : Measure (State × State) := g.stationary.compProd (g.transition ∘ₖ g.transition)

instance endpoint_probability : IsProbabilityMeasure (endpointLaw g) := by
  letI := g.stationary_probability
  letI := g.transition_markov
  unfold endpointLaw
  infer_instance

def law : Measure Space := (endpointLaw g).compProd (bridgeKernel β)

instance law_probability : IsProbabilityMeasure (law g) := by unfold law; infer_instance

/-- Both actual endpoints retain their stationary TWO-step law. -/
theorem endpoint_preserving : MeasurePreserving Prod.fst (law g) (endpointLaw g) :=
  ⟨measurable_fst,by change (law g).fst=endpointLaw g; exact Measure.fst_compProd _ _⟩

/-- Exact original-measure disintegration, for every integrable joint observable. -/
theorem integral_formula (f : Space → ℝ) (hf : Integrable f (law g)) :
    (∫ p,f p ∂law g)=∫ U,∫ W,∫ q,f ((U,W),q)
      ∂PeriodicAugmentedBridge.law β U W ∂((g.transition ∘ₖ g.transition) U) ∂g.stationary := by
  letI := g.stationary_probability
  letI := g.transition_markov
  change Integrable f ((endpointLaw g).compProd (bridgeKernel β)) at hf
  have hi : Integrable (fun p => ∫ q,f (p,q) ∂bridgeKernel β p) (endpointLaw g) := by
    simpa only [Kernel.prodMkLeft_apply,Kernel.const_apply] using hf.integral_compProd
  rw [law,Measure.integral_compProd hf]
  rw [endpointLaw,Measure.integral_compProd hi]
  simp_rw [bridgeKernel_apply]

/-- The middle marginal is the actual stationary law, not spatial Gibbs/Haar. -/
theorem middle_integral (f : State → ℝ) (hf : Measurable f) (B : ℝ) (hb : ∀ V,|f V|≤B) :
    (∫ p,f p.2.1 ∂law g)=∫ V,f V ∂g.stationary := by
  have hi : Integrable (fun p : Space => f p.2.1) (law g) :=
    Integrable.of_bound (hf.comp (measurable_fst.comp measurable_snd)).aestronglyMeasurable B
      (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using hb p.2.1))
  rw [integral_formula g _ hi]
  simp_rw [PeriodicAugmentedBridge.projection_integral β _ _ f hf B hb]
  exact PeriodicGroundBridge.stationary_bridge_average g f hf B hb

theorem middle_preserving :
    MeasurePreserving (fun p : Space => p.2.1) (law g) g.stationary := by
  letI := g.stationary_probability
  have hm : Measurable (fun p : Space => p.2.1) := measurable_fst.comp measurable_snd
  refine ⟨hm,?_⟩
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply hm hS]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have h := middle_integral g (S.indicator (fun _ => (1:ℝ))) (measurable_const.indicator hS) 1
    (fun V => by by_cases hV : V∈S <;> simp [hV])
  have he : (fun p : Space => S.indicator (fun _ => (1:ℝ)) p.2.1)=
      ((fun p : Space => p.2.1) ⁻¹' S).indicator (fun _ => (1:ℝ)) := by
    funext p
    by_cases hp : p.2.1∈S <;> simp [hp]
  rw [he] at h
  have hL := integral_indicator_one (μ := law g) (hS.preimage (measurable_fst.comp measurable_snd))
  have hR := integral_indicator_one (μ := g.stationary) hS
  exact hL.symm.trans (h.trans hR)

abbrev JointSpace (g : GroundData β) := Lp ℝ 2 (law g)

def middleEmbedding {β : ℝ} (g : GroundData β) : StateL2 g →ₗᵢ[ℝ] JointSpace g :=
  Lp.compMeasurePreservingₗᵢ ℝ _ (middle_preserving g)

def highEmbedding {β : ℝ} (g : GroundData β) (K : ℝ) :
    Completed g K →ₗᵢ[ℝ] JointSpace g where
  toFun F := middleEmbedding g F.val
  map_add' F G := (middleEmbedding g).map_add F.val G.val
  map_smul' c F := by simpa using (middleEmbedding g).map_smul c F.val
  norm_map' F := (middleEmbedding g).norm_map F.val

/-- Riesz realization of the TRUE joint pairing on the ORIGINAL physical high space. -/
def realization {β : ℝ} (g : GroundData β) (K : ℝ) :
    JointSpace g →L[ℝ] Completed g K :=
  HilbertRepresentation.predictableAdjoint (highEmbedding g K)

theorem realization_pairing {β : ℝ} (g : GroundData β) (K : ℝ)
    (Z : JointSpace g) (F : Completed g K) :
    inner ℝ (realization g K Z) F = ∫ q,F.val q.2.1*Z q ∂law g := by
  rw [realization,HilbertRepresentation.predictableAdjoint_pairing,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_compMeasurePreserving F.val (middle_preserving g)] with q hq
  change inner ℝ (Z q) (middleEmbedding g F.val q)=_
  change middleEmbedding g F.val q=F.val q.2.1 at hq
  rw [hq]
  rfl

/-- This is the physical HIGH projection of the actual middle conditional adjoint. -/
theorem realization_eq_projection {β : ℝ} (g : GroundData β) (K : ℝ) (Z : JointSpace g) :
    realization g K Z=(Completed g K).orthogonalProjectionOnto
      (HilbertRepresentation.predictableAdjoint (middleEmbedding g) Z) := by
  apply ext_inner_right ℝ
  intro F
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    realization,HilbertRepresentation.predictableAdjoint_pairing,
    HilbertRepresentation.predictableAdjoint_pairing]
  rfl

theorem realization_contraction {β : ℝ} (g : GroundData β) (K : ℝ) (Z : JointSpace g) :
    ‖realization g K Z‖ ≤ ‖Z‖ := by
  have h := HilbertRepresentation.representation_norm_decomposition (highEmbedding g K) Z
  change ‖Z‖^2=‖realization g K Z‖^2+_ at h
  nlinarith [sq_nonneg (‖Z-HilbertRepresentation.representationProjection (highEmbedding g K) Z‖),
    norm_nonneg (realization g K Z),norm_nonneg Z]

/-- Exact residual: all omitted components are orthogonal, not silently reconstructed. -/
theorem residual_pairing {β : ℝ} (g : GroundData β) (K : ℝ)
    (Z : JointSpace g) (F : Completed g K) :
    inner ℝ (Z-highEmbedding g K (realization g K Z)) (highEmbedding g K F)=0 :=
  HilbertRepresentation.representation_residual_pairing (highEmbedding g K) Z F

def gaussianResponse {β : ℝ} (hb : 0≤β) (g : GroundData β) (K : ℝ) :
    JointSpace g →L[ℝ] GaussianSpace :=
  (completedAnalysis hb g K).comp (realization g K)

theorem gaussianResponse_bound {β : ℝ} (hb : 16777216≤β) (g : GroundData β)
    (K : ℝ) (Z : JointSpace g) :
    ‖gaussianResponse (by linarith) g K Z‖^2 ≤
      (PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant)*
        Real.exp (-K)*‖Z‖^2 := by
  have h := completedAnalysis_high_bound hb g K (realization g K Z)
  have hn := pow_le_pow_left₀ (norm_nonneg _) (realization_contraction g K Z) 2
  have hp : 0≤(PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant)*Real.exp (-K) :=
    mul_nonneg (div_nonneg PeriodicGroundHaarScale.upperConstant_pos.le
      PeriodicGaugeSaturatedGround.eigenLowerConstant_pos.le) (Real.exp_pos _).le
  exact h.trans (mul_le_mul_of_nonneg_left hn hp)

/-- Bounded actual joint fields supported on the cancelling event pay its TRUE mass. -/
theorem supported_norm {β : ℝ} (g : GroundData β) (Z : JointSpace g)
    (C : ℝ) (hC : 0≤C)
    (hb : ∀ᵐ q ∂law g, ‖Z q‖≤C)
    (hs : ∀ᵐ q ∂law g, q.2.1∉PeriodicCancellingRestTail.bad → Z q=0) :
    ‖Z‖^2 ≤ C^2*g.stationary.real PeriodicCancellingRestTail.bad := by
  let E : Set Space := (fun q : Space => q.2.1) ⁻¹' PeriodicCancellingRestTail.bad
  have hE : MeasurableSet E := (middle_preserving g).measurable PeriodicCancellingRestTail.bad_measurable
  have hi : Integrable (E.indicator (fun _ : Space => C^2)) (law g) :=
    (integrable_const _).indicator hE
  rw [BochnerL2Dominated.norm_sq_integral]
  calc
    _ ≤ ∫ q,E.indicator (fun _ : Space => C^2) q ∂law g := by
      apply integral_mono_ae (Lp.memLp Z).norm.integrable_sq hi
      filter_upwards [hb,hs] with q hq hr
      by_cases he : q∈E
      · rw [Set.indicator_of_mem he]
        exact pow_le_pow_left₀ (norm_nonneg _) hq 2
      · rw [Set.indicator_of_notMem he,hr he,norm_zero]
        norm_num
    _ = C^2*g.stationary.real PeriodicCancellingRestTail.bad := by
      rw [integral_indicator_const _ hE]
      have he : (law g) E=g.stationary PeriodicCancellingRestTail.bad := by
        rw [← (middle_preserving g).map_eq,
          Measure.map_apply (middle_preserving g).measurable PeriodicCancellingRestTail.bad_measurable]
      change ((law g) E).toReal*(C^2)=_
      rw [he]
      exact mul_comm _ _

/-- Actual joint norm plus actual high compression give TWO suppressions.
This controls only the displayed projected high channel, not the omitted residual. -/
theorem supported_gaussianResponse {β : ℝ} (hb : 16777216≤β) (g : GroundData β)
    (Z : JointSpace g) (C : ℝ) (hC : 0≤C)
    (hz : ∀ᵐ q ∂law g, ‖Z q‖≤C)
    (hs : ∀ᵐ q ∂law g, q.2.1∉PeriodicCancellingRestTail.bad → Z q=0) :
    ‖gaussianResponse (by linarith) g β Z‖^2 ≤
      ((PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant)*
        Real.exp (-β))^2*C^2 := by
  have h := gaussianResponse_bound hb g β Z
  have hn := (supported_norm g Z C hC hz hs).trans
    (mul_le_mul_of_nonneg_left (PeriodicCancellingRestTail.stationary_bad_bound hb g) (sq_nonneg C))
  have hp : 0≤(PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant)*Real.exp (-β) :=
    mul_nonneg (div_nonneg PeriodicGroundHaarScale.upperConstant_pos.le
      PeriodicGaugeSaturatedGround.eigenLowerConstant_pos.le) (Real.exp_pos _).le
  calc
    _ ≤ _ := h.trans (mul_le_mul_of_nonneg_left hn hp)
    _ = _ := by ring

attribute [local irreducible] law endpointLaw bridgeKernel
  PeriodicEndpointScore.traceSum PeriodicEndpointScore.direction SU2JointPlaquetteCubic.axis

open PeriodicEndpointScore in
private theorem traceSum_joint :
    Measurable (fun p : Space => traceSum p.1.1 p.1.2 p.2) := by
  unfold traceSum
  apply Finset.measurable_sum
  intro e _
  apply Measurable.add
  · exact halfTrace_measurable.comp (by unfold temporalWord; fun_prop)
  · exact halfTrace_measurable.comp (by unfold temporalWord; fun_prop)


open PeriodicEndpointScore in
private theorem direction_joint :
    Measurable (fun p : Space => direction p.1.1 p.1.2 p.2) := by
  have hL : Measurable (fun p : Space => left (Real.pi/2) p.1.1) := by
    apply measurable_pi_lambda
    intro e
    change Measurable (fun p : Space => SU2JointPlaquetteCubic.axis 0 (Real.pi/2)*p.1.1 e)
    exact measurable_const.mul ((measurable_pi_apply e).comp (measurable_fst.comp measurable_fst))
  have hR : Measurable (fun p : Space => right (Real.pi/2) p.1.2) := by
    apply measurable_pi_lambda
    intro e
    change Measurable (fun p : Space => p.1.2 e*SU2JointPlaquetteCubic.axis 0 (-(Real.pi/2)))
    exact ((measurable_pi_apply e).comp (measurable_snd.comp measurable_fst)).mul measurable_const
  unfold direction
  change Measurable (fun p : Space =>
    traceSum (left (Real.pi/2) p.1.1) (right (Real.pi/2) p.1.2) p.2)
  exact traceSum_joint.comp ((hL.prodMk hR).prodMk measurable_snd)


/-- The pointwise stationary/endpoint/bridge densities retain BOTH ground factors. -/
theorem density_cancellation (U W : State) (q : PeriodicAugmentedBridge.Space) :
    (g.function U^2/g.normalizer)*PeriodicGroundBridge.twoStepDensity g U W*
      (PeriodicAugmentedBridge.density β U W q/PeriodicGroundBridge.normalizer β U W)=
      PeriodicAugmentedBridge.density β U W q*(g.function U*g.function W)/(g.value^2*g.normalizer) := by
  rw [PeriodicGroundBridge.twoStep_factor]
  field_simp [(PeriodicGroundBridge.normalizer_pos β U W).ne',g.normalizer_pos.ne',
    (g.function_pos U).ne',g.value_pos.ne']
  <;> ring

private theorem meanDirection_measurable :
    Measurable (fun p : State × State => ∫ q,PeriodicEndpointScore.direction p.1 p.2 q
      ∂PeriodicAugmentedBridge.law β p.1 p.2) := by
  have he : (fun p : State × State => ∫ q,PeriodicEndpointScore.direction p.1 p.2 q
      ∂PeriodicAugmentedBridge.law β p.1 p.2)=
      (fun p => (∫ q,PeriodicAugmentedBridge.density β p.1 p.2 q*PeriodicEndpointScore.direction p.1 p.2 q
        ∂PeriodicAugmentedBridge.reference)/PeriodicGroundBridge.normalizer β p.1 p.2) := by
    funext p
    exact PeriodicAugmentedBridge.integral_formula β p.1 p.2 _
  rw [he]
  exact ((density_measurable β).mul direction_joint).stronglyMeasurable.integral_prod_right.measurable.div
    (PeriodicGroundBridge.normalizer_measurable β)

def score (p : Space) : ℝ := PeriodicEndpointScore.score β p.1.1 p.1.2 p.2

theorem score_measurable : Measurable (score (β := β)) := by
  unfold score PeriodicEndpointScore.score
  exact (direction_joint.sub ((meanDirection_measurable (β := β)).comp measurable_fst)).const_mul β

theorem score_bound (p : Space) : |score (β := β) p|≤768*|β| :=
  PeriodicEndpointScore.score_bound β p.1.1 p.1.2 p.2

theorem score_memLp : MemLp (score (β := β)) 2 (law g) :=
  MemLp.of_bound score_measurable.aestronglyMeasurable (768*|β|)
    (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using score_bound p))

def badScore (p : Space) : ℝ :=
  ((fun p : Space => p.2.1) ⁻¹' PeriodicCancellingRestTail.bad).indicator (score (β := β)) p

theorem badScore_memLp : MemLp (badScore (β := β)) 2 (law g) :=
  (score_memLp g).indicator ((middle_preserving g).measurable PeriodicCancellingRestTail.bad_measurable)

def badScoreField : JointSpace g := (badScore_memLp g).toLp (badScore (β := β))

/-- The completed joint norm equals the actual TWO-step endpoint average of
both derivative channels established in the preceding checkpoint. -/
theorem badScore_norm :
    ‖badScoreField g‖^2=∫ U,∫ W,
      (PeriodicConditionalEndpointScore.badLinkEnergy β U W+PeriodicConditionalEndpointScore.badRestEnergy β U W)
      ∂((g.transition ∘ₖ g.transition) U) ∂g.stationary := by
  have he : ‖badScoreField g‖^2=∫ p,(badScore (β := β) p)^2 ∂law g := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [(badScore_memLp g).coeFn_toLp] with p hp
    change badScoreField g p=badScore p at hp
    rw [hp,Real.norm_eq_abs,sq_abs]
  rw [he,integral_formula g _ (badScore_memLp g).integrable_sq]
  apply integral_congr_ae
  filter_upwards with U
  apply integral_congr_ae
  filter_upwards with W
  rw [← PeriodicConditionalEndpointScore.badEnergy_split]
  unfold PeriodicEndpointScore.badEnergy
  apply integral_congr_ae
  filter_upwards with q
  by_cases hq : q.1∈PeriodicCancellingRestTail.bad
  · have hj : ((U,W),q)∈(fun p : Space => p.2.1) ⁻¹' PeriodicCancellingRestTail.bad := hq
    have hb : q∈(fun q : PeriodicAugmentedBridge.Space => q.1) ⁻¹' PeriodicCancellingRestTail.bad := hq
    simp only [badScore,Set.indicator_of_mem hj,Set.indicator_of_mem hb,score]
  · have hj : ((U,W),q)∉(fun p : Space => p.2.1) ⁻¹' PeriodicCancellingRestTail.bad := hq
    have hb : q∉(fun q : PeriodicAugmentedBridge.Space => q.1) ⁻¹' PeriodicCancellingRestTail.bad := hq
    simp only [badScore,Set.indicator_of_notMem hj,Set.indicator_of_notMem hb,zero_pow (by norm_num : 2≠0)]

/-- Concrete derivative of the original endpoint-conditioned two-slab Wilson law,
not the frozen one-slab coupling perturbation. Only its physical HIGH projection
is mapped to Gaussian space; all orthogonal and low components are retained. -/
theorem actual_bad_gaussian_bound (hb : 16777216≤β) :
    ‖gaussianResponse (by linarith) g β (badScoreField g)‖^2≤
      ((PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant)*
        Real.exp (-β))^2*(768*|β|)^2 := by
  apply supported_gaussianResponse hb g (badScoreField g) (768*|β|)
    (mul_nonneg (by norm_num) (abs_nonneg _))
  · filter_upwards [(badScore_memLp g).coeFn_toLp] with p hp
    change badScoreField g p=badScore p at hp
    rw [hp,Real.norm_eq_abs]
    by_cases he : p.2.1∈PeriodicCancellingRestTail.bad
    · have hm : p∈(fun p : Space => p.2.1) ⁻¹' PeriodicCancellingRestTail.bad := he
      simpa only [badScore,Set.indicator_of_mem hm] using score_bound (β := β) p
    · have hm : p∉(fun p : Space => p.2.1) ⁻¹' PeriodicCancellingRestTail.bad := he
      simp only [badScore,Set.indicator_of_notMem hm,abs_zero]
      positivity
  · filter_upwards [(badScore_memLp g).coeFn_toLp] with p hp
    intro he
    change badScoreField g p=badScore p at hp
    rw [hp]
    exact Set.indicator_of_notMem (show p∉(fun p : Space => p.2.1) ⁻¹' PeriodicCancellingRestTail.bad from he) _
end OperatorDerivativeRewrite.Foundation.PeriodicStationaryEndpointResponse
