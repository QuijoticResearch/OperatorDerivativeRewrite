import Foundation.StochasticCauchyStoppedDomains
import Foundation.StochasticCauchyPolynomialReconstruction
import Foundation.BochnerClosedOperator

/-! Actual native stochastic steps for ALL joint-past L2 coefficients.
The input domain and the two integrators remain the existing ones. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyJointSteps
open InfiniteGaussian ProductL2Curry GaussianTimeProcess
open StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyPastReconstruction StochasticCauchyPhysicalInput StochasticCauchyExponentialInput
attribute [local instance] StochasticCauchyParameterizedObstruction.finiteL2Exponent
  StochasticCauchyJointPastIntegral.input_complete
private abbrev μ := gaussianProduct.prod gaussianProduct
private def sections (T : ℝ≥0) : Input T →ₗᵢ[ℝ] Lp JointL2 2 (timeLaw T) :=
  (timeSections T).comp (fieldEmbedding T)
private def cellScalar (T s t : ℝ≥0) : Lp ℝ 2 (timeLaw T) :=
  indicatorConstLp 2 (measurableSet_Ioc (a := (s:ℝ)) (b := (t:ℝ))) (measure_ne_top _ _) 1
private def cellMap (T s t : ℝ≥0) : JointL2 →L[ℝ] Lp JointL2 2 (timeLaw T) :=
  ((ContinuousLinearMap.lsmul ℝ ℝ).flip.compLpL₂ 2 (timeLaw T)).flip (cellScalar T s t)
private theorem cellMap_ae (T s t : ℝ≥0) (C : JointL2) :
    cellMap T s t C =ᵐ[timeLaw T] (Ioc (s:ℝ) (t:ℝ)).indicator (fun _ => C) := by
  have hs : cellScalar T s t =ᵐ[timeLaw T] (Ioc (s:ℝ) (t:ℝ)).indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn
  have hm : cellMap T s t C =ᵐ[timeLaw T] fun r => cellScalar T s t r • C :=
    ((ContinuousLinearMap.lsmul ℝ ℝ).flip C).coeFn_compLp (cellScalar T s t)
  filter_upwards [hs,hm] with r hs hm
  rw [hm,hs]
  by_cases hr : r∈Ioc (s:ℝ) (t:ℝ) <;> simp [hr]
private theorem cell_tensor (T s t : ℝ≥0) (hst : s≤t) (htT : t≤T)
    (A B : GaussianL2) (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct) :
    sections T (stepInput T s t hst htT A B hA hB)=cellMap T s t (productTensor gaussianProduct gaussianProduct A B) :=
  Lp.ext ((timeSections_step T s t hst htT A B hA hB).trans (cellMap_ae T s t _).symm)
private def liftStep (T s t : ℝ≥0) : JointL2 →L[ℝ] Input T :=
  (HilbertRepresentation.predictableAdjoint (sections T)).comp (cellMap T s t)
private theorem liftStep_tensor (T s t : ℝ≥0) (hst : s≤t) (htT : t≤T)
    (A B : GaussianL2) (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct) :
    liftStep T s t (productTensor gaussianProduct gaussianProduct A B)=stepInput T s t hst htT A B hA hB := by
  rw [liftStep,ContinuousLinearMap.comp_apply,← cell_tensor T s t hst htT A B hA hB]
  exact HilbertRepresentation.predictableAdjoint_isometry_apply _ _

private theorem rectangle_tensor (s : ℝ≥0) (A B : Set SampleSpace)
    (hA : MeasurableSet[naturalFiltration s] A) (hB : MeasurableSet[naturalFiltration s] B) :
    indicatorConstLp 2 ((naturalFiltration.le s A hA).prod (naturalFiltration.le s B hB))
      (measure_ne_top μ (A ×ˢ B)) (1:ℝ)=
      productTensor gaussianProduct gaussianProduct
        (indicatorConstLp 2 (naturalFiltration.le s A hA) (measure_ne_top gaussianProduct A) (1:ℝ))
        (indicatorConstLp 2 (naturalFiltration.le s B hB) (measure_ne_top gaussianProduct B) (1:ℝ)) := by
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (p := 2) (c := (1:ℝ)) (hμs := by finiteness)
      (μ := μ) (hs := (naturalFiltration.le s A hA).prod (naturalFiltration.le s B hB)),
    productTensor_coeFn gaussianProduct gaussianProduct
      (indicatorConstLp 2 (naturalFiltration.le s A hA) (measure_ne_top gaussianProduct A) (1:ℝ))
      (indicatorConstLp 2 (naturalFiltration.le s B hB) (measure_ne_top gaussianProduct B) (1:ℝ)),
    (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
      (indicatorConstLp_coeFn (p := 2) (c := (1:ℝ)) (hμs := by finiteness) (μ := gaussianProduct) (hs := naturalFiltration.le s A hA)),
    (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
      (indicatorConstLp_coeFn (p := 2) (c := (1:ℝ)) (hμs := by finiteness) (μ := gaussianProduct) (hs := naturalFiltration.le s B hB))]
    with w hw ht ha hb
  simp only [Function.comp_apply] at ha hb
  rw [hw,ht,ha,hb]
  simp only [smul_eq_mul]
  by_cases hwa : w.1∈A <;> by_cases hwb : w.2∈B <;> simp [hwa,hwb]

private theorem past_le_of_tensors (s : ℝ≥0) (K : Submodule ℝ JointL2)
    (hK : IsClosed (K : Set JointL2))
    (hTensor : ∀ A B : GaussianL2, AEStronglyMeasurable[naturalFiltration s] A gaussianProduct →
      AEStronglyMeasurable[naturalFiltration s] B gaussianProduct → productTensor gaussianProduct gaussianProduct A B∈K) :
    jointPastL2 s≤K := by
  let S : Set (Set (SampleSpace × SampleSpace)) :=
    image2 (· ×ˢ ·) {A | MeasurableSet[naturalFiltration s] A} {B | MeasurableSet[naturalFiltration s] B}
  have hd : (generatingIndicatorSpan μ S).topologicalClosure=jointPastL2 s :=
    generatingIndicatorSpan_closure μ (jointPast_le s) S
      (@generateFrom_prod SampleSpace SampleSpace (naturalFiltration s) (naturalFiltration s))
      (@isPiSystem_prod SampleSpace SampleSpace (naturalFiltration s) (naturalFiltration s))
      ⟨univ,(show MeasurableSet[naturalFiltration s] univ from MeasurableSet.univ),
        univ,(show MeasurableSet[naturalFiltration s] univ from MeasurableSet.univ),univ_prod_univ⟩
  have hspan : generatingIndicatorSpan μ S≤K := by
    apply Submodule.span_le.mpr
    rintro f ⟨q,⟨A,hA,B,hB,rfl⟩,hq,rfl⟩
    rw [rectangle_tensor s A B hA hB]
    let a : GaussianL2 := indicatorConstLp 2 (naturalFiltration.le s A hA) (measure_ne_top gaussianProduct A) (1:ℝ)
    let b : GaussianL2 := indicatorConstLp 2 (naturalFiltration.le s B hB) (measure_ne_top gaussianProduct B) (1:ℝ)
    have ha : AEStronglyMeasurable[naturalFiltration s] a gaussianProduct :=
      (mem_lpMeas_iff_aestronglyMeasurable (𝕜 := ℝ)).mp (mem_lpMeas_indicatorConstLp (naturalFiltration.le s) hA (measure_ne_top gaussianProduct A))
    have hb : AEStronglyMeasurable[naturalFiltration s] b gaussianProduct :=
      (mem_lpMeas_iff_aestronglyMeasurable (𝕜 := ℝ)).mp (mem_lpMeas_indicatorConstLp (naturalFiltration.le s) hB (measure_ne_top gaussianProduct B))
    exact hTensor a b ha hb
  have hc : (generatingIndicatorSpan μ S).topologicalClosure≤K :=
    (generatingIndicatorSpan μ S).topologicalClosure_minimal hspan hK
  exact hd.symm.le.trans hc

private theorem past_field (T s t : ℝ≥0) (hst : s≤t) (htT : t≤T) (C : jointPastL2 s) :
    sections T (liftStep T s t C)=cellMap T s t C := by
  let K := ((sections T).toContinuousLinearMap.comp (liftStep T s t)-cellMap T s t).ker
  have hk : jointPastL2 s≤K := past_le_of_tensors s K (ContinuousLinearMap.isClosed_ker _) (by
    intro A B hA hB
    change sections T (liftStep T s t (productTensor gaussianProduct gaussianProduct A B))-
      cellMap T s t (productTensor gaussianProduct gaussianProduct A B)=0
    rw [liftStep_tensor T s t hst htT A B hA hB,cell_tensor T s t hst htT A B hA hB,sub_self])
  exact sub_eq_zero.mp (hk C.property)

/-- An ACTUAL bounded input operator on the independently specified joint past. -/
def jointStep (T s t : ℝ≥0) : jointPastL2 s →L[ℝ] Input T :=
  (liftStep T s t).comp (jointPastL2 s).subtypeL

theorem jointStep_sections (T s t : ℝ≥0) (hst : s≤t) (htT : t≤T) (C : jointPastL2 s) :
    timeSections T (fieldEmbedding T (jointStep T s t C))=cellMap T s t C :=
  past_field T s t hst htT C

theorem jointStep_slices (T s t : ℝ≥0) (hst : s≤t) (htT : t≤T) (C : jointPastL2 s) :
    timeSections T (fieldEmbedding T (jointStep T s t C)) =ᵐ[timeLaw T]
      (Ioc (s:ℝ) (t:ℝ)).indicator (fun _ => C.val) := by
  rw [jointStep_sections T s t hst htT C]
  exact cellMap_ae T s t C

theorem jointStep_unique (T s t : ℝ≥0) (hst : s≤t) (htT : t≤T) (C : jointPastL2 s) (u : Input T)
    (hu : timeSections T (fieldEmbedding T u)=cellMap T s t C) : u=jointStep T s t C :=
  (sections T).injective (hu.trans (jointStep_sections T s t hst htT C).symm)

private def productRelation (J : JointL2 →L[ℝ] JointL2) (V : (SampleSpace × SampleSpace) → ℝ) : Submodule ℝ JointL2 where
  carrier := {C | J C =ᵐ[μ] fun w => C w*V w}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ)] with w hw
    simp only [map_zero,hw,Pi.zero_apply,zero_mul]
  add_mem' := by
    intro A B hA hB
    change J (A+B) =ᵐ[μ] fun w => (A+B) w*V w
    rw [map_add]
    filter_upwards [hA,hB,Lp.coeFn_add (J A) (J B),Lp.coeFn_add A B] with w ha hb hj hc
    simp only [Pi.add_apply] at hj hc
    rw [hj,hc,ha,hb,add_mul]
  smul_mem' := by
    intro c A hA
    change J (c • A) =ᵐ[μ] fun w => (c • A) w*V w
    rw [map_smul]
    filter_upwards [hA,Lp.coeFn_smul c (J A),Lp.coeFn_smul c A] with w ha hj hc
    simp only [Pi.smul_apply,smul_eq_mul] at hj hc
    rw [hj,hc,ha,mul_assoc]

/-- The multiplier is NOT assumed bounded on L2. Both coordinates converge
in L2, and a common AE subsequence identifies the actual pointwise product. -/
private theorem productRelation_closed (J : JointL2 →L[ℝ] JointL2)
    (V : (SampleSpace × SampleSpace) → ℝ) : IsClosed (productRelation J V : Set JointL2) := by
  apply IsSeqClosed.isClosed
  intro C F hC hlim
  obtain ⟨ns,hns,hn⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hj := (J.continuous.tendsto F).comp hlim
  obtain ⟨ms,hms,hm⟩ := (tendstoInMeasure_of_tendsto_Lp (hj.comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  have hall : ∀ᵐ w ∂μ,∀ n,J (C n) w=C n w*V w := ae_all_iff.mpr hC
  filter_upwards [hn,hm,hall] with w hn hm hall
  have hp := (hn.comp hms.tendsto_atTop).mul_const (V w)
  simp only [Function.comp_apply,hall] at hm
  exact tendsto_nhds_unique hm hp

private def noiseIntegral (T : ℝ≥0) (j : Bool) : Input T →ₗᵢ[ℝ] JointL2 :=
  if j then integralY T else integralX T
private def noiseIncrement (s t : ℝ≥0) (j : Bool) (w : SampleSpace × SampleSpace) : ℝ :=
  if j then process t w.2-process s w.2 else process t w.1-process s w.1

private theorem tensor_step_actual (T s t : ℝ≥0) (hst : s≤t) (htT : t≤T) (A B : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct) (j : Bool) :
    noiseIntegral T j (stepInput T s t hst htT A B hA hB) =ᵐ[μ] fun w =>
      productTensor gaussianProduct gaussianProduct A B w*noiseIncrement s t j w := by
  cases j
  · change integralX T (stepInput T s t hst htT A B hA hB) =ᵐ[μ] fun w =>
      productTensor gaussianProduct gaussianProduct A B w*(process t w.1-process s w.1)
    rw [integralX_stepInput]
    filter_upwards [productTensor_coeFn gaussianProduct gaussianProduct
        (GaussianPastStepCompletion.pastIncrement s t hst A hA) B,
      productTensor_coeFn gaussianProduct gaussianProduct A B,
      (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
        (GaussianPastStepCompletion.pastIncrement_coeFn s t hst A hA)] with w ho hc hi
    simp only [Function.comp_apply] at hi
    rw [ho,hc,hi]
    simp only [smul_eq_mul]
    ring
  · change integralY T (stepInput T s t hst htT A B hA hB) =ᵐ[μ] fun w =>
      productTensor gaussianProduct gaussianProduct A B w*(process t w.2-process s w.2)
    rw [integralY_stepInput]
    filter_upwards [productTensor_coeFn gaussianProduct gaussianProduct A
        (GaussianPastStepCompletion.pastIncrement s t hst B hB),
      productTensor_coeFn gaussianProduct gaussianProduct A B,
      (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
        (GaussianPastStepCompletion.pastIncrement_coeFn s t hst B hB)] with w ho hc hi
    simp only [Function.comp_apply] at hi
    rw [ho,hc,hi]
    simp only [smul_eq_mul]
    ring

private theorem past_product (T s t : ℝ≥0) (hst : s≤t) (htT : t≤T) (j : Bool) :
    jointPastL2 s≤productRelation ((noiseIntegral T j).toContinuousLinearMap.comp (liftStep T s t))
      (noiseIncrement s t j) := by
  apply past_le_of_tensors s _ (productRelation_closed _ _)
  intro A B hA hB
  change noiseIntegral T j (liftStep T s t (productTensor gaussianProduct gaussianProduct A B)) =ᵐ[μ]
    fun w => productTensor gaussianProduct gaussianProduct A B w*noiseIncrement s t j w
  rw [liftStep_tensor T s t hst htT A B hA hB]
  exact tensor_step_actual T s t hst htT A B hA hB j

/-- The ACTUAL native integrals are the stochastic step products for every
joint-past L2 coefficient, without assuming product L2 integrability. -/
theorem jointStep_integrals (T s t : ℝ≥0) (hst : s≤t) (htT : t≤T) (C : jointPastL2 s) :
    (integralX T (jointStep T s t C) =ᵐ[μ] fun w => C.val w*(process t w.1-process s w.1)) ∧
    (integralY T (jointStep T s t C) =ᵐ[μ] fun w => C.val w*(process t w.2-process s w.2)) :=
  ⟨past_product T s t hst htT false C.property,past_product T s t hst htT true C.property⟩

theorem jointStep_products_memLp (T s t : ℝ≥0) (hst : s≤t) (htT : t≤T) (C : jointPastL2 s) :
    MemLp (fun w => C.val w*(process t w.1-process s w.1)) 2 μ ∧
    MemLp (fun w => C.val w*(process t w.2-process s w.2)) 2 μ :=
  ⟨(Lp.memLp (integralX T (jointStep T s t C))).ae_eq (jointStep_integrals T s t hst htT C).1,
    (Lp.memLp (integralY T (jointStep T s t C))).ae_eq (jointStep_integrals T s t hst htT C).2⟩

theorem jointStep_continuous (T s t : ℝ≥0) : Continuous (jointStep T s t) := (jointStep T s t).continuous

/-- Physical AE-time/AE-source representatives of the actual joint step field. -/
theorem jointStep_physical (T s t : ℝ≥0) (hst : s≤t) (htT : t≤T) (C : jointPastL2 s) :
    ∀ᵐ r ∂timeLaw T, ∀ᵐ w ∂μ,
      fieldEmbedding T (jointStep T s t C) ((r,w.1),w.2)=
        (Ioc (s:ℝ) (t:ℝ)).indicator (fun _ => C.val w) r := by
  filter_upwards [timeSections_ae T (fieldEmbedding T (jointStep T s t C)),jointStep_slices T s t hst htT C]
    with r hr hs
  by_cases hm : r∈Ioc (s:ℝ) (t:ℝ)
  · rw [indicator_of_mem hm] at hs
    rw [hs] at hr
    filter_upwards [hr] with w hw
    simpa only [indicator_of_mem hm] using hw.symm
  · rw [indicator_of_notMem hm] at hs
    rw [hs] at hr
    filter_upwards [hr,Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ)] with w hw hz
    rw [← hw,hz,indicator_of_notMem hm]
    rfl

open StochasticCauchyStoppedDomains StochasticCauchyComplexChannels ComplexL2Isometry
attribute [local instance] StochasticCauchyComplexChannels.complexInput_complete

private def lateEvent : Set (SampleSpace × SampleSpace) := {w | (1:ℝ≥0)<twoStage w}
private theorem lateEvent_past : MeasurableSet[augmentedJoint 1] lateEvent := by
  simpa only [lateEvent,WithTop.coe_lt_coe] using twoStage_isStoppingTime.measurableSet_gt (1:ℝ≥0)

def lateCoefficient : JointL2 :=
  indicatorConstLp 2 (augmented_joint_le 1 lateEvent lateEvent_past) (measure_ne_top μ lateEvent) (1:ℝ)

theorem lateCoefficient_actual : lateCoefficient =ᵐ[μ] lateEvent.indicator (fun _ => (1:ℝ)) :=
  indicatorConstLp_coeFn

theorem lateCoefficient_mem_past : lateCoefficient∈jointPastL2 1 := by
  apply raw_past_of_augmented
  have hm : StronglyMeasurable[augmentedJoint 1] (lateEvent.indicator (fun _ => (1:ℝ))) :=
    stronglyMeasurable_const.indicator lateEvent_past
  exact hm.aestronglyMeasurable.congr lateCoefficient_actual.symm

private def latePast : jointPastL2 1 := ⟨lateCoefficient,lateCoefficient_mem_past⟩
private def onePast : jointPastL2 0 :=
  ⟨jointOne,mem_lpMeas_iff_aestronglyMeasurable.mpr
    (stronglyMeasurable_const.aestronglyMeasurable.congr jointOne_ae.symm)⟩

/-- The actual real stopped-indicator input:1 on(0,1], and the observed
joint decision indicator on(1,2]. Both summands belong to the OLD native domain. -/
def stoppedRealInput : Input 2 :=
  jointStep 2 0 1 onePast+jointStep 2 1 2 latePast


/-- The constructed real input is the actual random stopped-indicator field,
with time/source AE quantifiers explicit. -/
theorem stopped_indicator_physical :
    ∀ᵐ r ∂timeLaw 2, ∀ᵐ w ∂μ,
      fieldEmbedding 2 stoppedRealInput ((r,w.1),w.2)=
        (Ioc (0:ℝ) (twoStage w:ℝ)).indicator (fun _ => (1:ℝ)) r := by
  have he : timeSections 2 (fieldEmbedding 2 stoppedRealInput)=
      cellMap 2 0 1 jointOne+cellMap 2 1 2 lateCoefficient := by
    change sections 2 (jointStep 2 0 1 onePast+jointStep 2 1 2 latePast)=_
    rw [map_add]
    exact congrArg₂ (·+·) (jointStep_sections 2 0 1 (by norm_num) (by norm_num) onePast)
      (jointStep_sections 2 1 2 (by norm_num) (by norm_num) latePast)
  filter_upwards [timeSections_ae 2 (fieldEmbedding 2 stoppedRealInput),
    Lp.coeFn_add (cellMap 2 0 1 jointOne) (cellMap 2 1 2 lateCoefficient),
    cellMap_ae 2 0 1 jointOne,cellMap_ae 2 1 2 lateCoefficient] with r hr ha hb hl
  rw [he] at hr
  simp only [Pi.add_apply] at ha
  rw [ha,hb,hl] at hr
  filter_upwards [hr,jointOne_ae,lateCoefficient_actual,
    Lp.coeFn_add ((Ioc ((0:ℝ≥0):ℝ) ((1:ℝ≥0):ℝ)).indicator (fun _ => jointOne) r)
      ((Ioc ((1:ℝ≥0):ℝ) ((2:ℝ≥0):ℝ)).indicator (fun _ => lateCoefficient) r),
    Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ)] with w hw h1 hL hsum h0
  rw [← hw,hsum]
  simp only [Pi.add_apply]
  have ht : twoStage w=1 ∨ twoStage w=2 := by unfold twoStage; split <;> simp
  rcases ht with ht | ht <;>
    by_cases h01 : r∈Ioc (0:ℝ) (1:ℝ) <;>
    by_cases h12 : r∈Ioc (1:ℝ) (2:ℝ)
  all_goals simp only [mem_Ioc] at h01 h12
  all_goals simp [Set.indicator,Set.mem_Ioc,h01,h12,h1,hL,lateEvent,ht]
  all_goals by_cases h0r : 0 < r <;> by_cases h1r : r≤1 <;> by_cases h2r : r≤2 <;> simp_all <;> linarith

/-- The sqrt2 is the original physical dZ/native dZ/sqrt2 conversion. -/
def stoppedComplexInput : ComplexInput 2 :=
  ((Real.sqrt 2:ℝ):ℂ) • combineInput 2 stoppedRealInput 0

theorem stopped_input_parts :
    realInput 2 stoppedComplexInput=Real.sqrt 2 • stoppedRealInput ∧ imagInput 2 stoppedComplexInput=0 := by
  constructor <;>
    simp only [stoppedComplexInput,realInput_smul,imagInput_smul,realInput_combine,imagInput_combine,
      Complex.ofReal_re,Complex.ofReal_im,zero_smul,sub_zero,add_zero,smul_zero]

/-- The actual physical stochastic integral at the SAME nondegenerate clock. -/
theorem stopped_integral_actual : channel 2 false stoppedComplexInput =ᵐ[μ]
    fun w => StochasticCauchyBrownianRealization.value (twoStage w) w := by
  rw [stoppedComplexInput,StochasticCauchyExponentialReconstruction.normalized_channel_combine,
    map_zero,sub_zero,map_zero,zero_add,stoppedRealInput,map_add,map_add]
  have hb := jointStep_integrals 2 0 1 (by norm_num) (by norm_num) onePast
  have hl := jointStep_integrals 2 1 2 (by norm_num) (by norm_num) latePast
  filter_upwards [combine_ae μ _ _,
    Lp.coeFn_add (integralX 2 (jointStep 2 0 1 onePast)) (integralX 2 (jointStep 2 1 2 latePast)),
    Lp.coeFn_add (integralY 2 (jointStep 2 0 1 onePast)) (integralY 2 (jointStep 2 1 2 latePast)),
    hb.1,hb.2,hl.1,hl.2,jointOne_ae,lateCoefficient_actual,
    (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp process_zero_ae,
    (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp process_zero_ae,
    StochasticCauchyContinuousPolynomials.continuous_value_ae 1,
    StochasticCauchyContinuousPolynomials.continuous_value_ae 2] with w hc hx hy hbX hbY hlX hlY h1 hL h0X h0Y hz1 hz2
  simp only [Function.comp_apply] at h0X h0Y
  change jointOne w=_ at h1
  change lateCoefficient w=_ at hL
  change integralX 2 (jointStep 2 0 1 onePast) w=jointOne w*_ at hbX
  change integralY 2 (jointStep 2 0 1 onePast) w=jointOne w*_ at hbY
  change integralX 2 (jointStep 2 1 2 latePast) w=lateCoefficient w*_ at hlX
  change integralY 2 (jointStep 2 1 2 latePast) w=lateCoefficient w*_ at hlY
  rw [hc,hx,hy]
  simp only [Pi.add_apply]
  rw [hbX,hbY,hlX,hlY,h1,hL,h0X,h0Y]
  have ht : twoStage w=1 ∨ twoStage w=2 := by unfold twoStage; split <;> simp
  rcases ht with ht | ht
  · rw [ht,hz1]
    simp [lateEvent,ht,StochasticCauchyPolynomialPrediction.position]
  · rw [ht,hz2]
    apply Complex.ext <;> simp [lateEvent,ht,StochasticCauchyPolynomialPrediction.position]

/-- Exact L2 identity; the actual sampled value no longer requires an abstract residual representation. -/
theorem stopped_integral : channel 2 false stoppedComplexInput=twoStageValue :=
  Lp.ext (stopped_integral_actual.trans twoStage_value_actual.symm)

theorem stopped_value_mean_zero : (∫ w,twoStageValue w ∂μ)=0 := by
  rw [← stopped_integral]
  exact StochasticCauchyMeanResidual.channel_centered 2 false stoppedComplexInput

theorem stopped_actual_mean_zero :
    (∫ w,StochasticCauchyBrownianRealization.value (twoStage w) w ∂μ)=0 := by
  rw [← integral_congr_ae twoStage_value_actual]
  exact stopped_value_mean_zero

theorem stopped_center_eq : StochasticCauchyMeanResidual.complexCenter twoStageValue=twoStageValue := by
  rw [StochasticCauchyMeanResidual.complexCenter_apply,stopped_value_mean_zero,zero_smul,sub_zero]

/-- The previously constructed CANONICAL inputs equal this explicit stopped
indicator and zero in the conjugate channel. -/
theorem stopped_canonical_inputs : twoStageInput false=stoppedComplexInput ∧ twoStageInput true=0 := by
  have he := twoStage_input_unique stoppedComplexInput 0 (by
    rw [map_zero,add_zero,stopped_integral,stopped_center_eq])
  exact ⟨he.1.symm,he.2.symm⟩

end OperatorDerivativeRewrite.Foundation.StochasticCauchyJointSteps
