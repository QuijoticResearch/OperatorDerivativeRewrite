import Foundation.StochasticCauchyContinuousPolynomials
import Foundation.AmbientNullAugmentation
import Mathlib.Probability.Process.Stopping

/-! Genuine random-time observables enter the ORIGINAL joint-past stochastic
reconstruction domain via an explicitly proved null-augmentation bridge.
No Malliavin derivative of a random-time value is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyStoppedDomains
open InfiniteGaussian ComplexL2Isometry GaussianTimeProcess
open StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyPastReconstruction StochasticCauchyComplexChannels
open StochasticCauchyPolynomialPrediction StochasticCauchyContinuousPolynomials
attribute [local instance] StochasticCauchyParameterizedObstruction.finiteL2Exponent
  StochasticCauchyParameterizedObstruction.predictableTime
  StochasticCauchyJointPastIntegral.input_complete StochasticCauchyComplexChannels.complexInput_complete

private abbrev μ := gaussianProduct.prod gaussianProduct

private abbrev rawJoint := StochasticCauchyExponentialPrediction.jointFiltration

def augmentedJoint : Filtration ℝ≥0 (inferInstance : MeasurableSpace (SampleSpace × SampleSpace)) :=
  AmbientNullAugmentation.filtration μ rawJoint

theorem augmented_joint_le (T : ℝ≥0) : augmentedJoint T≤(inferInstance : MeasurableSpace (SampleSpace × SampleSpace)) :=
  augmentedJoint.le T

theorem continuous_stronglyAdapted : StronglyAdapted augmentedJoint StochasticCauchyBrownianRealization.value := by
  intro t
  apply Measurable.stronglyMeasurable
  apply AmbientNullAugmentation.measurable_of_raw_aestronglyMeasurable (jointPast t) μ
    (StochasticCauchyBrownianRealization.value_measurable t)
  exact (position_stronglyMeasurable t).aestronglyMeasurable.congr (continuous_value_ae t).symm

/-- Clipped at a deterministic horizon; tau itself may be unbounded. -/
def stopped (T : ℝ≥0) (τ : (SampleSpace × SampleSpace) → ℝ≥0) (w : SampleSpace × SampleSpace) : ℂ :=
  StochasticCauchyBrownianRealization.value (min T (τ w)) w

theorem stopped_stronglyMeasurable (T : ℝ≥0) (τ : (SampleSpace × SampleSpace) → ℝ≥0)
    (hτ : IsStoppingTime augmentedJoint (fun w => (τ w : WithTop ℝ≥0))) :
    StronglyMeasurable[augmentedJoint T] (stopped T τ) := by
  have hs := (continuous_stronglyAdapted.stoppedProcess
    (fun w => StochasticCauchyBrownianRealization.value_continuous w) hτ) T
  have he : MeasureTheory.stoppedProcess StochasticCauchyBrownianRealization.value
      (fun w => (τ w : WithTop ℝ≥0)) T=stopped T τ := by
    funext w
    change StochasticCauchyBrownianRealization.value
      (min (T:WithTop ℝ≥0) (τ w)).untopA w=_
    rw [← WithTop.coe_min]
    rfl
  rwa [he] at hs

theorem stopped_path_continuous (τ : (SampleSpace × SampleSpace) → ℝ≥0)
    (w : SampleSpace × SampleSpace) : Continuous (fun T => stopped T τ w) :=
  (StochasticCauchyBrownianRealization.value_continuous w).comp (continuous_id.min continuous_const)

theorem stopped_jointly_measurable (τ : (SampleSpace × SampleSpace) → ℝ≥0)
    (hτ : IsStoppingTime augmentedJoint (fun w => (τ w : WithTop ℝ≥0))) :
    Measurable (fun q : ℝ≥0 × (SampleSpace × SampleSpace) => stopped q.1 τ q.2) :=
  measurable_uncurry_of_continuous_of_measurable (stopped_path_continuous τ)
    (fun T => ((stopped_stronglyMeasurable T τ hτ).mono (augmented_joint_le T)).measurable)

/-- An actual integrable augmented-past variable has a RAW-past AE version.
Conditional-expectation invariance discharges this, rather than identifying sigma algebras. -/
theorem raw_past_of_augmented (T : ℝ≥0) (F : JointL2)
    (hF : AEStronglyMeasurable[augmentedJoint T] F μ) : F∈jointPastL2 T := by
  have hi : Integrable F μ := (Lp.memLp F).integrable (by norm_num)
  have ha := condExp_of_aestronglyMeasurable' (augmented_joint_le T) hF hi
  have he := AmbientNullAugmentation.condExp_invariant (jointPast T) μ (jointPast_le T) F hi
  have hr : μ[F | jointPast T] =ᵐ[μ] F := he.trans ha
  apply mem_lpMeas_iff_aestronglyMeasurable.mpr
  exact stronglyMeasurable_condExp.aestronglyMeasurable.congr hr

theorem observable_memLp (T : ℝ≥0) (τ : (SampleSpace × SampleSpace) → ℝ≥0)
    (hτ : IsStoppingTime augmentedJoint (fun w => (τ w : WithTop ℝ≥0)))
    (φ : ℂ → ℝ) (hφ : Continuous φ) (M : ℝ)
    (hM : ∀ᵐ w ∂μ,‖φ (stopped T τ w)‖≤M) : MemLp (fun w => φ (stopped T τ w)) 2 μ := by
  apply MemLp.of_bound (C := M)
  · exact ((hφ.comp_stronglyMeasurable (stopped_stronglyMeasurable T τ hτ)).mono
      (augmented_joint_le T)).aestronglyMeasurable
  · exact hM

def observable (T : ℝ≥0) (τ : (SampleSpace × SampleSpace) → ℝ≥0)
    (hτ : IsStoppingTime augmentedJoint (fun w => (τ w : WithTop ℝ≥0)))
    (φ : ℂ → ℝ) (hφ : Continuous φ) (M : ℝ)
    (hM : ∀ᵐ w ∂μ,‖φ (stopped T τ w)‖≤M) : JointL2 :=
  (observable_memLp T τ hτ φ hφ M hM).toLp _

theorem observable_actual (T : ℝ≥0) (τ : (SampleSpace × SampleSpace) → ℝ≥0)
    (hτ : IsStoppingTime augmentedJoint (fun w => (τ w : WithTop ℝ≥0)))
    (φ : ℂ → ℝ) (hφ : Continuous φ) (M : ℝ)
    (hM : ∀ᵐ w ∂μ,‖φ (stopped T τ w)‖≤M) :
    observable T τ hτ φ hφ M hM =ᵐ[μ] fun w => φ (stopped T τ w) := MemLp.coeFn_toLp _

theorem observable_mem_past (T : ℝ≥0) (τ : (SampleSpace × SampleSpace) → ℝ≥0)
    (hτ : IsStoppingTime augmentedJoint (fun w => (τ w : WithTop ℝ≥0)))
    (φ : ℂ → ℝ) (hφ : Continuous φ) (M : ℝ)
    (hM : ∀ᵐ w ∂μ,‖φ (stopped T τ w)‖≤M) : observable T τ hτ φ hφ M hM∈jointPastL2 T := by
  apply raw_past_of_augmented
  exact (hφ.comp_stronglyMeasurable (stopped_stronglyMeasurable T τ hτ)).aestronglyMeasurable.congr
    (observable_actual T τ hτ φ hφ M hM).symm

theorem stopped_reconstruction (T : ℝ≥0) (τ : (SampleSpace × SampleSpace) → ℝ≥0)
    (hτ : IsStoppingTime augmentedJoint (fun w => (τ w : WithTop ℝ≥0)))
    (φ : ℂ → ℝ) (hφ : Continuous φ) (M : ℝ)
    (hM : ∀ᵐ w ∂μ,‖φ (stopped T τ w)‖≤M) :
    integralX T (adjointX T (center (observable T τ hτ φ hφ M hM)))+
      integralY T (adjointY T (center (observable T τ hτ φ hφ M hM)))=
        center (observable T τ hτ φ hφ M hM) :=
  joint_past_representation T _ (observable_mem_past T τ hτ φ hφ M hM)

/-- A concrete decision based on BOTH observed sources at time1. -/
def twoStage (w : SampleSpace × SampleSpace) : ℝ≥0 :=
  if (StochasticCauchyBrownianRealization.value 1 w).re+
      (StochasticCauchyBrownianRealization.value 1 w).im≤0 then 1 else 2

theorem twoStage_bounds (w : SampleSpace × SampleSpace) : 1≤twoStage w ∧ twoStage w≤2 := by
  unfold twoStage
  split <;> norm_num

theorem twoStage_isStoppingTime : IsStoppingTime augmentedJoint (fun w => (twoStage w : WithTop ℝ≥0)) := by
  have hm : Measurable[augmentedJoint 1] (StochasticCauchyBrownianRealization.value 1) :=
    (continuous_stronglyAdapted 1).measurable
  have hA : MeasurableSet[augmentedJoint 1] {w | (StochasticCauchyBrownianRealization.value 1 w).re+
      (StochasticCauchyBrownianRealization.value 1 w).im≤0} :=
    measurableSet_le ((Complex.continuous_re.measurable.comp hm).add
      (Complex.continuous_im.measurable.comp hm)) measurable_const
  intro t
  by_cases h2 : (2:ℝ≥0)≤t
  · have he : {w | (twoStage w : WithTop ℝ≥0)≤t}=univ := by
      ext w
      simp only [mem_ofPred_eq,mem_univ,iff_true,WithTop.coe_le_coe]
      exact (twoStage_bounds w).2.trans h2
    rw [he]
    exact @MeasurableSet.univ _ (augmentedJoint t)
  by_cases h1 : (1:ℝ≥0)≤t
  · have he : {w | (twoStage w : WithTop ℝ≥0)≤t}={w | (StochasticCauchyBrownianRealization.value 1 w).re+
        (StochasticCauchyBrownianRealization.value 1 w).im≤0} := by
      ext w
      simp only [mem_ofPred_eq,WithTop.coe_le_coe,twoStage]
      by_cases hw : (StochasticCauchyBrownianRealization.value 1 w).re+
          (StochasticCauchyBrownianRealization.value 1 w).im≤0 <;> simp [hw,h1,h2]
    rw [he]
    exact augmentedJoint.mono h1 _ hA
  · have he : {w | (twoStage w : WithTop ℝ≥0)≤t}=∅ := by
      ext w
      simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false,WithTop.coe_le_coe]
      exact fun h => h1 ((twoStage_bounds w).1.trans h)
    rw [he]
    exact (augmentedJoint t).measurableSet_empty

private def score (w : SampleSpace × SampleSpace) : ℝ :=
  (StochasticCauchyBrownianRealization.value 1 w).re+(StochasticCauchyBrownianRealization.value 1 w).im

theorem score_law : μ.map score=ProbabilityTheory.gaussianReal 0 2 := by
  have hi := StochasticCauchyBrownianRealization.components_independent.comp
    (measurable_pi_apply (1:ℝ≥0)) (measurable_pi_apply (1:ℝ≥0))
  have hx := StochasticCauchyBrownianRealization.real_isBrownian.toIsPreBrownianReal.hasLaw_eval 1
  have hy := StochasticCauchyBrownianRealization.imag_isBrownian.toIsPreBrownianReal.hasLaw_eval 1
  have hs := ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun hi hx hy
  have hfun : score=((fun w => (StochasticCauchyBrownianRealization.value 1 w).re)+
      (fun w => (StochasticCauchyBrownianRealization.value 1 w).im)) := by funext w; rfl
  rw [hfun]
  simpa only [Function.comp_def,IBMSourceLaws.jointMeasure,zero_add,one_add_one_eq_two] using hs

/-- BOTH branches have positive probability: the clock is genuinely random. -/
theorem twoStage_branches_positive : 0<μ {w | twoStage w=1} ∧ 0<μ {w | twoStage w=2} := by
  have hm : Measurable score :=
    (Complex.continuous_re.measurable.comp (StochasticCauchyBrownianRealization.value_measurable 1)).add
      (Complex.continuous_im.measurable.comp (StochasticCauchyBrownianRealization.value_measurable 1))
  have hleft : 0<ProbabilityTheory.gaussianReal 0 2 (Iic (0:ℝ)) := by
    apply bot_lt_iff_ne_bot.mpr
    intro hz
    have hv := ProbabilityTheory.gaussianReal_absolutelyContinuous' (0:ℝ) (by norm_num : (2:ℝ≥0)≠0) hz
    simpa using hv
  have hright : 0<ProbabilityTheory.gaussianReal 0 2 (Ioi (0:ℝ)) := by
    apply bot_lt_iff_ne_bot.mpr
    intro hz
    have hv := ProbabilityTheory.gaussianReal_absolutelyContinuous' (0:ℝ) (by norm_num : (2:ℝ≥0)≠0) hz
    simpa using hv
  have he1 : {w | twoStage w=1}=score ⁻¹' Iic (0:ℝ) := by
    ext w
    simp [twoStage,score]
  have he2 : {w | twoStage w=2}=score ⁻¹' Ioi (0:ℝ) := by
    ext w
    simp [twoStage,score,not_le]
  rw [he1,he2]
  rw [← score_law,Measure.map_apply hm measurableSet_Iic] at hleft
  rw [← score_law,Measure.map_apply hm measurableSet_Ioi] at hright
  exact ⟨hleft,hright⟩

theorem twoStage_unclipped (w : SampleSpace × SampleSpace) :
    stopped 2 twoStage w=StochasticCauchyBrownianRealization.value (twoStage w) w := by
  rw [stopped,min_eq_right (twoStage_bounds w).2]

/-- Domain transfer for arbitrary actual augmented-past complex L2 observables. -/
theorem augmented_complex_residual (T : ℝ≥0) (F : JointComplex)
    (hF : AEStronglyMeasurable[augmentedJoint T] F μ) :
    residual T (StochasticCauchyMeanResidual.complexCenter F)=0 := by
  have hr : AEStronglyMeasurable[augmentedJoint T] (realPart μ F) μ :=
    (Complex.continuous_re.comp_aestronglyMeasurable hF).congr (Complex.reCLM.coeFn_compLpL F).symm
  have hi : AEStronglyMeasurable[augmentedJoint T] (imagPart μ F) μ :=
    (Complex.continuous_im.comp_aestronglyMeasurable hF).congr (Complex.imCLM.coeFn_compLpL F).symm
  have hp := complex_joint_past_reconstruction T (realPart μ F) (imagPart μ F)
    (raw_past_of_augmented T _ hr) (raw_past_of_augmented T _ hi)
  rw [← StochasticCauchyMeanResidual.complexCenter_combine,combine_parts] at hp
  exact hp

/-- The actual sampled Brownian point is L2 because this concrete clock takes only1 and2. -/
theorem twoStage_value_memLp : MemLp (fun w => StochasticCauchyBrownianRealization.value (twoStage w) w) 2 μ := by
  have h1 := StochasticCauchyBrownianRealization.value_memLp 1
  have h2 := StochasticCauchyBrownianRealization.value_memLp 2
  have hm : StronglyMeasurable (fun w => StochasticCauchyBrownianRealization.value (twoStage w) w) := by
    have hs := (stopped_stronglyMeasurable 2 twoStage twoStage_isStoppingTime).mono (augmented_joint_le 2)
    simpa only [funext twoStage_unclipped] using hs
  apply (h1.norm.add h2.norm).mono hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro w
  unfold twoStage
  split <;> simp only [Pi.add_apply,Real.norm_eq_abs,
    abs_of_nonneg (add_nonneg (norm_nonneg (StochasticCauchyBrownianRealization.value 1 w))
      (norm_nonneg (StochasticCauchyBrownianRealization.value 2 w)))]
  · exact le_add_of_nonneg_right (norm_nonneg (StochasticCauchyBrownianRealization.value 2 w))
  · exact le_add_of_nonneg_left (norm_nonneg (StochasticCauchyBrownianRealization.value 1 w))

def twoStageValue : JointComplex := twoStage_value_memLp.toLp _

theorem twoStage_value_actual : twoStageValue =ᵐ[μ]
    fun w => StochasticCauchyBrownianRealization.value (twoStage w) w := MemLp.coeFn_toLp _

theorem twoStage_value_augmented : AEStronglyMeasurable[augmentedJoint 2] twoStageValue μ := by
  have hs : AEStronglyMeasurable[augmentedJoint 2] (stopped 2 twoStage) μ :=
    (stopped_stronglyMeasurable 2 twoStage twoStage_isStoppingTime).aestronglyMeasurable
  have he : stopped 2 twoStage = (fun w => StochasticCauchyBrownianRealization.value (twoStage w) w) := funext twoStage_unclipped
  rw [he] at hs
  exact hs.congr twoStage_value_actual.symm

theorem twoStage_value_residual : residual 2 (StochasticCauchyMeanResidual.complexCenter twoStageValue)=0 :=
  augmented_complex_residual 2 twoStageValue twoStage_value_augmented

/-- Direct reuse of the old native channels after actual augmented-past membership. -/
theorem augmented_complex_formula (T : ℝ≥0) (F : JointComplex)
    (hF : AEStronglyMeasurable[augmentedJoint T] F μ) :
    channel T false (channelAdjoint T false (StochasticCauchyMeanResidual.complexCenter F))+
      channel T true (channelAdjoint T true (StochasticCauchyMeanResidual.complexCenter F))=
        StochasticCauchyMeanResidual.complexCenter F := by
  have hz := augmented_complex_residual T F hF
  rw [← cauchyProjection_apply,← cauchyProjection_apply]
  let H := StochasticCauchyMeanResidual.complexCenter F
  change H-cauchyProjection T false H-cauchyProjection T true H=0 at hz
  have he : H=(H-cauchyProjection T false H-cauchyProjection T true H)+
      (cauchyProjection T false H+cauchyProjection T true H) := by abel
  simpa only [hz,zero_add] using he.symm

def twoStageInput (anti : Bool) : ComplexInput 2 :=
  channelAdjoint 2 anti (StochasticCauchyMeanResidual.complexCenter twoStageValue)

theorem twoStage_stochastic_formula :
    channel 2 false (twoStageInput false)+channel 2 true (twoStageInput true)=
      StochasticCauchyMeanResidual.complexCenter twoStageValue :=
  augmented_complex_formula 2 twoStageValue twoStage_value_augmented

/-- Actual unique native inputs, not a formal representation with unknown domains. -/
theorem twoStage_input_unique (u v : ComplexInput 2)
    (h : channel 2 false u+channel 2 true v=StochasticCauchyMeanResidual.complexCenter twoStageValue) :
    u=twoStageInput false ∧ v=twoStageInput true := by
  have he := channel_coefficients_recover 2 u v
  rw [h] at he
  exact ⟨he.1.symm,he.2.symm⟩

theorem twoStage_stochastic_actual :
    (fun w => channel 2 false (twoStageInput false) w+channel 2 true (twoStageInput true) w)
      =ᵐ[μ] fun w => StochasticCauchyBrownianRealization.value (twoStage w) w-
        ∫ x,StochasticCauchyBrownianRealization.value (twoStage x) x ∂μ := by
  have he := StochasticCauchyMeanResidual.complexCenter_ae twoStageValue
  have hm : (∫ w,twoStageValue w ∂μ)=∫ w,StochasticCauchyBrownianRealization.value (twoStage w) w ∂μ :=
    integral_congr_ae twoStage_value_actual
  rw [← twoStage_stochastic_formula] at he
  filter_upwards [he,Lp.coeFn_add (channel 2 false (twoStageInput false)) (channel 2 true (twoStageInput true)),
    twoStage_value_actual] with w he ha hv
  simp only [Pi.add_apply] at ha
  rw [← ha,he,hv,hm]

end OperatorDerivativeRewrite.Foundation.StochasticCauchyStoppedDomains
