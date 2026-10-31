import Foundation.PeriodicNativeGaussianAnalysis
import Foundation.PeriodicSlabJoint
/-! Actual joint-law response restricted to the EXISTING physical high space.
The orthogonal residual is retained; this does not identify an arbitrary score
with a full physical native field or prove a low-sector/scale-uniform bound. -/
noncomputable section
open MeasureTheory Filter
namespace OperatorDerivativeRewrite.Foundation.PeriodicJointHighResponse
open PeriodicTemporalSlab PeriodicSlabGround PeriodicSlabL2 PeriodicSlabJoint
open PeriodicNativeGaussianAnalysis
attribute [local irreducible] PeriodicWilsonSlab.spatialAction PeriodicWilsonSlab.temporalAction

abbrev JointSpace {β : ℝ} (g : GroundData β) := Lp ℝ 2 (tripleLaw g)

theorem middle_preserving {β : ℝ} (g : GroundData β) :
    MeasurePreserving (fun q : Triple => q.1.2) (tripleLaw g) g.stationary :=
  (right_preserving g).comp (pair_preserving g)

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
    inner ℝ (realization g K Z) F = ∫ q,F.val q.1.2*Z q ∂tripleLaw g := by
  rw [realization,HilbertRepresentation.predictableAdjoint_pairing,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_compMeasurePreserving F.val (middle_preserving g)] with q hq
  change inner ℝ (Z q) (middleEmbedding g F.val q)=_
  change middleEmbedding g F.val q=F.val q.1.2 at hq
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
    (hb : ∀ᵐ q ∂tripleLaw g, ‖Z q‖≤C)
    (hs : ∀ᵐ q ∂tripleLaw g, q.1.2∉PeriodicCancellingRestTail.bad → Z q=0) :
    ‖Z‖^2 ≤ C^2*g.stationary.real PeriodicCancellingRestTail.bad := by
  let E : Set Triple := (fun q : Triple => q.1.2) ⁻¹' PeriodicCancellingRestTail.bad
  have hE : MeasurableSet E := (middle_preserving g).measurable PeriodicCancellingRestTail.bad_measurable
  have hi : Integrable (E.indicator (fun _ : Triple => C^2)) (tripleLaw g) :=
    (integrable_const _).indicator hE
  rw [BochnerL2Dominated.norm_sq_integral]
  calc
    _ ≤ ∫ q,E.indicator (fun _ : Triple => C^2) q ∂tripleLaw g := by
      apply integral_mono_ae (Lp.memLp Z).norm.integrable_sq hi
      filter_upwards [hb,hs] with q hq hr
      by_cases he : q∈E
      · rw [Set.indicator_of_mem he]
        exact pow_le_pow_left₀ (norm_nonneg _) hq 2
      · rw [Set.indicator_of_notMem he,hr he,norm_zero]
        norm_num
    _ = C^2*g.stationary.real PeriodicCancellingRestTail.bad := by
      rw [integral_indicator_const _ hE]
      have he : (tripleLaw g) E=g.stationary PeriodicCancellingRestTail.bad := by
        rw [← (middle_preserving g).map_eq,
          Measure.map_apply (middle_preserving g).measurable PeriodicCancellingRestTail.bad_measurable]
      change ((tripleLaw g) E).toReal*(C^2)=_
      rw [he]
      exact mul_comm _ _

/-- Actual joint norm plus actual high compression give TWO suppressions.
This controls only the displayed projected high channel, not the omitted residual. -/
theorem supported_gaussianResponse {β : ℝ} (hb : 16777216≤β) (g : GroundData β)
    (Z : JointSpace g) (C : ℝ) (hC : 0≤C)
    (hz : ∀ᵐ q ∂tripleLaw g, ‖Z q‖≤C)
    (hs : ∀ᵐ q ∂tripleLaw g, q.1.2∉PeriodicCancellingRestTail.bad → Z q=0) :
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
/-- A genuine action perturbation of the actual joint law, with ground data FROZEN. -/
def actionSource (q : Triple) : ℝ :=
  -PeriodicWilsonSlab.halfAction q.1.1 q.1.2 q.2/768

theorem actionSource_measurable : Measurable actionSource := by
  unfold actionSource PeriodicWilsonSlab.halfAction
  exact ((((PeriodicWilsonSlab.spatial_action_measurable.comp
    (measurable_fst.comp measurable_fst)).div_const 2).add
    PeriodicWilsonSlab.temporal_action_joint_measurable).add
    ((PeriodicWilsonSlab.spatial_action_measurable.comp
      (measurable_snd.comp measurable_fst)).div_const 2)).neg.div_const 768

theorem actionSource_bound (q : Triple) : |actionSource q|≤1 := by
  have h := PeriodicWilsonSlab.half_action_bounds q.1.1 q.1.2 q.2
  unfold actionSource
  rw [abs_div,abs_neg,abs_of_nonneg h.1]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<768)]
  exact (div_le_one (by norm_num : (0:ℝ)<768)).mpr h.2

def score {β : ℝ} (g : GroundData β) (q : Triple) : ℝ :=
  actionSource q-∫ p,actionSource p ∂tripleLaw g

theorem score_bound {β : ℝ} (g : GroundData β) (q : Triple) : |score g q|≤2 := by
  have hm : ‖∫ p,actionSource p ∂tripleLaw g‖≤1 :=
    by
      simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
        (μ := tripleLaw g) (f := actionSource) (C := 1)
        (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using actionSource_bound p))
  have h := abs_sub (actionSource q) (∫ p,actionSource p ∂tripleLaw g)
  apply h.trans
  rw [Real.norm_eq_abs] at hm
  linarith [actionSource_bound q]

theorem score_memLp {β : ℝ} (g : GroundData β) : MemLp (score g) 2 (tripleLaw g) :=
  MemLp.of_bound (actionSource_measurable.sub measurable_const).aestronglyMeasurable 2
    (ae_of_all _ (fun q => by simpa only [Real.norm_eq_abs] using score_bound g q))

def scoreField {β : ℝ} (g : GroundData β) : JointSpace g := (score_memLp g).toLp (score g)

def frozenTilt {β : ℝ} (g : GroundData β) (t : ℝ) : Measure Triple :=
  BoundedExponentialTiltResponse.tiltedMeasure (tripleLaw g) actionSource t

/-- Exact coupling shift of the Wilson weight, retaining the FROZEN ground factor. -/
theorem reweighted_jointWeight {β : ℝ} (g : GroundData β) (t : ℝ) (q : Triple) :
    jointWeight g q*Real.exp (t*actionSource q)=
      PeriodicWilsonSlab.weight (β+t/768) q.1.1 q.1.2 q.2*
        (g.function q.1.1*g.function q.1.2) := by
  unfold jointWeight PeriodicWilsonSlab.weight actionSource
  rw [show -(β+t/768)*PeriodicWilsonSlab.halfAction q.1.1 q.1.2 q.2 =
    (-β*PeriodicWilsonSlab.halfAction q.1.1 q.1.2 q.2)+
      t*(-PeriodicWilsonSlab.halfAction q.1.1 q.1.2 q.2/768) by ring,Real.exp_add]
  ring

/-- Normalizer retained: exact ratio for the genuinely shifted Wilson weight.
The two ground factors are fixed at g, not replaced by a putative g(beta+t/768). -/
theorem frozenTilt_integral {β : ℝ} (g : GroundData β) (t : ℝ) (f : Triple → ℝ) :
    (∫ q,f q ∂frozenTilt g t)=
      (∫ q,PeriodicWilsonSlab.weight (β+t/768) q.1.1 q.1.2 q.2*
        (g.function q.1.1*g.function q.1.2)*f q ∂reference)/
      (∫ q,PeriodicWilsonSlab.weight (β+t/768) q.1.1 q.1.2 q.2*
        (g.function q.1.1*g.function q.1.2) ∂reference) := by
  rw [frozenTilt,BoundedExponentialTiltResponse.tilted_integral (tripleLaw g)
    actionSource f actionSource_measurable actionSource_bound]
  unfold BoundedExponentialTiltResponse.expectation BoundedExponentialTiltResponse.partition
    BoundedExponentialTiltResponse.weighted
  simp only [one_mul]
  rw [integral_formula,integral_formula]
  have hN : (∫ q,jointWeight g q*(f q*Real.exp (t*actionSource q)) ∂reference)=
      ∫ q,PeriodicWilsonSlab.weight (β+t/768) q.1.1 q.1.2 q.2*
        (g.function q.1.1*g.function q.1.2)*f q ∂reference := by
    apply integral_congr_ae
    filter_upwards with q
    rw [show jointWeight g q*(f q*Real.exp (t*actionSource q))=
      (jointWeight g q*Real.exp (t*actionSource q))*f q by ring,reweighted_jointWeight]
  rw [hN]
  simp_rw [reweighted_jointWeight]
  exact div_div_div_cancel_right₀ (mul_pos g.value_pos g.normalizer_pos).ne' _ _

/-- Actual normalized-law response; this differentiates the stated frozen-ground
perturbation, NOT the stationary family with its eigenfunction also varying. -/
theorem frozenTilt_derivative {β : ℝ} (g : GroundData β) (K : ℝ)
    (F : Completed g K) (M : ℝ) (hM : 0≤M) (hf : ∀ V,|F.val V|≤M) :
    HasDerivAt (fun t => ∫ q,F.val q.1.2 ∂frozenTilt g t)
      (inner ℝ (realization g K (scoreField g)) F) 0 := by
  let f : Triple → ℝ := fun q => F.val q.1.2
  have hfm : Measurable f := (Lp.stronglyMeasurable F.val).measurable.comp
    (middle_preserving g).measurable
  have hfb : ∀ q,|f q|≤M := fun q => hf q.1.2
  have hfi : Integrable f (tripleLaw g) := Integrable.of_bound hfm.aestronglyMeasurable M
    (ae_of_all _ (fun q => by simpa only [Real.norm_eq_abs] using hfb q))
  have hxi : Integrable (fun q => f q*actionSource q) (tripleLaw g) :=
    Integrable.of_bound (hfm.mul actionSource_measurable).aestronglyMeasurable M
      (ae_of_all _ (fun q => by
        rw [Real.norm_eq_abs,abs_mul]
        exact (mul_le_mul_of_nonneg_left (actionSource_bound q) (abs_nonneg _)).trans
          (by simpa only [mul_one] using hfb q)))
  have he : inner ℝ (realization g K (scoreField g)) F =
      (∫ q,f q*actionSource q ∂tripleLaw g)-
        (∫ q,f q ∂tripleLaw g)*(∫ q,actionSource q ∂tripleLaw g) := by
    rw [realization_pairing]
    calc
      _ = ∫ q,f q*score g q ∂tripleLaw g := by
        apply integral_congr_ae
        filter_upwards [(score_memLp g).coeFn_toLp] with q hq
        exact congrArg (fun z => f q*z) hq
      _ = _ := by
        simp only [score,mul_sub]
        rw [integral_sub hxi (hfi.mul_const _),integral_mul_const]
  rw [he]
  simp_rw [frozenTilt,BoundedExponentialTiltResponse.tilted_integral
    (tripleLaw g) actionSource _ actionSource_measurable actionSource_bound]
  exact BoundedExponentialTiltResponse.expectation_hasDerivAt_zero
    (tripleLaw g) actionSource f actionSource_measurable hfm actionSource_bound M hM hfb

def badScore {β : ℝ} (g : GroundData β) (q : Triple) : ℝ :=
  ((fun q : Triple => q.1.2) ⁻¹' PeriodicCancellingRestTail.bad).indicator (score g) q

theorem badScore_memLp {β : ℝ} (g : GroundData β) : MemLp (badScore g) 2 (tripleLaw g) :=
  (score_memLp g).indicator ((middle_preserving g).measurable PeriodicCancellingRestTail.bad_measurable)

def badScoreField {β : ℝ} (g : GroundData β) : JointSpace g :=
  (badScore_memLp g).toLp (badScore g)

/-- Concrete bad-event part of the actual frozen-ground action score. -/
theorem badScore_gaussian_bound {β : ℝ} (hb : 16777216≤β) (g : GroundData β) :
    ‖gaussianResponse (by linarith) g β (badScoreField g)‖^2 ≤
      ((PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant)*
        Real.exp (-β))^2*4 := by
  apply (supported_gaussianResponse hb g (badScoreField g) 2 (by norm_num) ?_ ?_).trans_eq
  · norm_num
  · filter_upwards [(badScore_memLp g).coeFn_toLp] with q hq
    change badScoreField g q=badScore g q at hq
    rw [hq,Real.norm_eq_abs]
    by_cases he : q.1.2∈PeriodicCancellingRestTail.bad
    · have hmem : q∈(fun q : Triple => q.1.2) ⁻¹' PeriodicCancellingRestTail.bad := he
      simpa only [badScore,Set.indicator_of_mem hmem] using score_bound g q
    · have hmem : q∉(fun q : Triple => q.1.2) ⁻¹' PeriodicCancellingRestTail.bad := he
      simp only [badScore,Set.indicator_of_notMem hmem,abs_zero]
      norm_num
  · filter_upwards [(badScore_memLp g).coeFn_toLp] with q hq
    intro he
    change badScoreField g q=badScore g q at hq
    rw [hq]
    exact Set.indicator_of_notMem (show q∉(fun q : Triple => q.1.2) ⁻¹'
      PeriodicCancellingRestTail.bad from he) _
end OperatorDerivativeRewrite.Foundation.PeriodicJointHighResponse
