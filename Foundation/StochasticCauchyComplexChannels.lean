import Foundation.StochasticCauchyPhysicalInput

/-! Actual complex stochastic channels on the completed common-past domain.
The target range is not assumed to be every centered observable. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyComplexChannels
open InfiniteGaussian GaussianTimeProcess GaussianComplexHorizonIto ComplexL2Isometry
open StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
attribute [local instance] StochasticCauchyParameterizedObstruction.predictableTime
  StochasticCauchyParameterizedObstruction.finiteL2Exponent
  StochasticCauchyJointPastIntegral.input_complete

private theorem realPart_smul {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (c : ℂ) (f : Lp ℂ 2 μ) :
    realPart μ (c • f) = c.re • realPart μ f - c.im • imagPart μ f := by
  apply Lp.ext
  filter_upwards [Complex.reCLM.coeFn_compLpL (c • f),Lp.coeFn_smul c f,
    Complex.reCLM.coeFn_compLpL f,Complex.imCLM.coeFn_compLpL f,
    Lp.coeFn_sub (c.re • realPart μ f) (c.im • imagPart μ f),
    Lp.coeFn_smul c.re (realPart μ f),Lp.coeFn_smul c.im (imagPart μ f)]
    with x ho hc hr hi hd hs ht
  change realPart μ (c • f) x = _ at ho
  change realPart μ f x = _ at hr
  change imagPart μ f x = _ at hi
  simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul] at hc hd hs ht
  rw [ho,hc,hd,hs,ht,hr,hi]
  rfl

private theorem imagPart_smul {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (c : ℂ) (f : Lp ℂ 2 μ) :
    imagPart μ (c • f) = c.re • imagPart μ f + c.im • realPart μ f := by
  apply Lp.ext
  filter_upwards [Complex.imCLM.coeFn_compLpL (c • f),Lp.coeFn_smul c f,
    Complex.reCLM.coeFn_compLpL f,Complex.imCLM.coeFn_compLpL f,
    Lp.coeFn_add (c.re • imagPart μ f) (c.im • realPart μ f),
    Lp.coeFn_smul c.re (imagPart μ f),Lp.coeFn_smul c.im (realPart μ f)]
    with x ho hc hr hi hd hs ht
  change imagPart μ (c • f) x = _ at ho
  change realPart μ f x = _ at hr
  change imagPart μ f x = _ at hi
  simp only [Pi.smul_apply,Pi.add_apply,smul_eq_mul] at hc hd hs ht
  rw [ho,hc,hd,hs,ht,hr,hi]
  simp [Complex.mul_im]

private theorem combine_add {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (a b c d : Lp ℝ 2 μ) :
    combine μ a b + combine μ c d = combine μ (a+c) (b+d) := by
  simp only [combine,map_add,smul_add]
  abel

private theorem complex_ext {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f g : Lp ℂ 2 μ} (hr : realPart μ f = realPart μ g)
    (hi : imagPart μ f = imagPart μ g) : f=g := by
  rw [← combine_parts μ f,← combine_parts μ g,hr,hi]

abbrev nativeMeasure (T : ℝ≥0) := (predictableMeasure T).prod gaussianProduct
abbrev JointComplex := Lp ℂ 2 (gaussianProduct.prod gaussianProduct)

/-- The actual complex native domain has BOTH parts in the verified common past. -/
def ComplexInput (T : ℝ≥0) : Submodule ℂ (Lp ℂ 2 (nativeMeasure T)) where
  carrier := {u | realPart (nativeMeasure T) u ∈ Input T ∧ imagPart (nativeMeasure T) u ∈ Input T}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv
    exact ⟨by simpa only [map_add] using (Input T).add_mem hu.1 hv.1,
      by simpa only [map_add] using (Input T).add_mem hu.2 hv.2⟩
  smul_mem' := by
    intro c u hu
    change realPart (nativeMeasure T) (c • u) ∈ Input T ∧
      imagPart (nativeMeasure T) (c • u) ∈ Input T
    rw [realPart_smul,imagPart_smul]
    exact ⟨(Input T).sub_mem ((Input T).smul_mem c.re hu.1) ((Input T).smul_mem c.im hu.2),
      (Input T).add_mem ((Input T).smul_mem c.re hu.2) ((Input T).smul_mem c.im hu.1)⟩

theorem complexInput_closed (T : ℝ≥0) :
    IsClosed (ComplexInput T : Set (Lp ℂ 2 (nativeMeasure T))) :=
  ((inputSpan T).isClosed_topologicalClosure.preimage (realPart (nativeMeasure T)).continuous).inter
    ((inputSpan T).isClosed_topologicalClosure.preimage (imagPart (nativeMeasure T)).continuous)

theorem complexInput_complete (T : ℝ≥0) : CompleteSpace (ComplexInput T) :=
  (complexInput_closed T).completeSpace_coe

attribute [local instance] complexInput_complete

def realInput (T : ℝ≥0) : ComplexInput T →L[ℝ] Input T :=
  ((realPart (nativeMeasure T)).comp ((ComplexInput T).subtypeL.restrictScalars ℝ)).codRestrict
    (Input T) (fun u => u.property.1)

def imagInput (T : ℝ≥0) : ComplexInput T →L[ℝ] Input T :=
  ((imagPart (nativeMeasure T)).comp ((ComplexInput T).subtypeL.restrictScalars ℝ)).codRestrict
    (Input T) (fun u => u.property.2)

theorem realInput_smul (T : ℝ≥0) (c : ℂ) (u : ComplexInput T) :
    realInput T (c • u)=c.re • realInput T u-c.im • imagInput T u := by
  apply Subtype.ext
  exact realPart_smul (nativeMeasure T) c u.val

theorem imagInput_smul (T : ℝ≥0) (c : ℂ) (u : ComplexInput T) :
    imagInput T (c • u)=c.re • imagInput T u+c.im • realInput T u := by
  apply Subtype.ext
  exact imagPart_smul (nativeMeasure T) c u.val

def combineInput (T : ℝ≥0) (a b : Input T) : ComplexInput T :=
  ⟨combine (nativeMeasure T) a.val b.val,
    by rw [realPart_combine]; exact a.property,
    by rw [imagPart_combine]; exact b.property⟩

theorem realInput_combine (T : ℝ≥0) (a b : Input T) : realInput T (combineInput T a b)=a :=
  Subtype.ext (realPart_combine (nativeMeasure T) a.val b.val)

theorem imagInput_combine (T : ℝ≥0) (a b : Input T) : imagInput T (combineInput T a b)=b :=
  Subtype.ext (imagPart_combine (nativeMeasure T) a.val b.val)

theorem input_norm_sq (T : ℝ≥0) (u : ComplexInput T) :
    ‖u‖^2=‖realInput T u‖^2+‖imagInput T u‖^2 :=
  norm_sq_parts (nativeMeasure T) u.val

/-- Complex-linear extension of an ACTUAL real stochastic isometry on this domain. -/
def liftInput (T : ℝ≥0) (J : Input T →ₗᵢ[ℝ] JointL2) :
    ComplexInput T →ₗᵢ[ℂ] JointComplex where
  toLinearMap :=
    { toFun u := combine (gaussianProduct.prod gaussianProduct)
        (J (realInput T u)) (J (imagInput T u))
      map_add' u v := by
        simp only [map_add]
        exact (combine_add _ _ _ _ _).symm
      map_smul' c u := by
        apply complex_ext (gaussianProduct.prod gaussianProduct)
        · rw [realPart_combine,realPart_smul,realPart_combine,imagPart_combine,
            realInput_smul,map_sub,map_smul,map_smul]
          rfl
        · rw [imagPart_combine,imagPart_smul,realPart_combine,imagPart_combine,
            imagInput_smul,map_add,map_smul,map_smul]
          rfl }
  norm_map' u := by
    change ‖combine (gaussianProduct.prod gaussianProduct)
      (J (realInput T u)) (J (imagInput T u))‖=‖u‖
    have he : ‖combine (gaussianProduct.prod gaussianProduct)
        (J (realInput T u)) (J (imagInput T u))‖^2=‖u‖^2 := by
      rw [combine_norm_sq,J.norm_map,J.norm_map,← input_norm_sq]
    nlinarith [norm_nonneg u,norm_nonneg (combine (gaussianProduct.prod gaussianProduct)
      (J (realInput T u)) (J (imagInput T u)))]

def integralXComplex (T : ℝ≥0) : ComplexInput T →ₗᵢ[ℂ] JointComplex := liftInput T (integralX T)
def integralYComplex (T : ℝ≥0) : ComplexInput T →ₗᵢ[ℂ] JointComplex := liftInput T (integralY T)

theorem liftInput_apply (T : ℝ≥0) (J : Input T →ₗᵢ[ℝ] JointL2) (u : ComplexInput T) :
    liftInput T J u = combine (gaussianProduct.prod gaussianProduct)
      (J (realInput T u)) (J (imagInput T u)) := rfl

/-- The two real-source complexified ranges remain orthogonal in the Hermitian sense. -/
theorem complex_pair_energy (T : ℝ≥0) (u v : ComplexInput T) :
    ‖integralXComplex T u+integralYComplex T v‖^2=‖u‖^2+‖v‖^2 := by
  change ‖combine (gaussianProduct.prod gaussianProduct)
    (integralX T (realInput T u)) (integralX T (imagInput T u))+
      combine (gaussianProduct.prod gaussianProduct)
        (integralY T (realInput T v)) (integralY T (imagInput T v))‖^2 = _
  rw [combine_add,combine_norm_sq,joint_integral_energy,joint_integral_energy,
    input_norm_sq T u,input_norm_sq T v]
  ring

theorem complex_sources_orthogonal (T : ℝ≥0) (u v : ComplexInput T) :
    inner ℂ (integralXComplex T u) (integralYComplex T v)=0 := by
  apply (inner_eq_zero_iff_forall_re_inner_smul_left).mpr
  intro c
  rw [← map_smul]
  have he := complex_pair_energy T (c • u) v
  have hn := norm_add_sq (𝕜 := ℂ) (integralXComplex T (c • u)) (integralYComplex T v)
  rw [(integralXComplex T).norm_map,(integralYComplex T).norm_map] at hn
  linarith

attribute [local irreducible] integralXComplex integralYComplex

/-- The unnormalized channel integrates against dB1+c*dB2. -/
def rawChannel (T : ℝ≥0) (c : ℂ) : ComplexInput T →ₗ[ℂ] JointComplex :=
  (integralXComplex T).toLinearMap+c • (integralYComplex T).toLinearMap

theorem rawChannel_energy (T : ℝ≥0) (c : ℂ) (u : ComplexInput T) :
    ‖rawChannel T c u‖^2=(1+‖c‖^2)*‖u‖^2 := by
  change ‖integralXComplex T u+c • integralYComplex T u‖^2 = _
  rw [norm_add_sq (𝕜 := ℂ),inner_smul_right,complex_sources_orthogonal,mul_zero]
  simp only [map_zero,mul_zero,add_zero,norm_smul,
    (integralXComplex T).norm_map,(integralYComplex T).norm_map]
  ring

private theorem normalizer_sq : ‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ)‖^2*2=1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,sq_abs,inv_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- false is dZ/sqrt2; true is dZbar/sqrt2, for Z=B1+iB2. -/
def channel (T : ℝ≥0) (anti : Bool) : ComplexInput T →ₗᵢ[ℂ] JointComplex where
  toLinearMap := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • rawChannel T (if anti then -Complex.I else Complex.I)
  norm_map' u := by
    change ‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
      rawChannel T (if anti then -Complex.I else Complex.I) u‖=‖u‖
    have hc : ‖(if anti then -Complex.I else Complex.I : ℂ)‖=1 := by cases anti <;> simp
    have hr := rawChannel_energy T (if anti then -Complex.I else Complex.I) u
    rw [hc] at hr
    norm_num only [one_pow,one_add_one_eq_two] at hr
    have he : ‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
        rawChannel T (if anti then -Complex.I else Complex.I) u‖^2=‖u‖^2 := by
      rw [norm_smul,mul_pow,hr]
      calc
        _ = (‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ)‖^2*2)*‖u‖^2 := by ring
        _ = _ := by rw [normalizer_sq,one_mul]
    nlinarith [norm_nonneg u,norm_nonneg ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
      rawChannel T (if anti then -Complex.I else Complex.I) u)]

theorem channels_orthogonal (T : ℝ≥0) (u v : ComplexInput T) :
    inner ℂ (channel T false u) (channel T true v)=0 := by
  have hyx : inner ℂ (integralYComplex T u) (integralXComplex T v)=0 :=
    (inner_eq_zero_symm).mp (complex_sources_orthogonal T v u)
  have hraw : inner ℂ (rawChannel T Complex.I u) (rawChannel T (-Complex.I) v)=0 := by
    change inner ℂ (integralXComplex T u+Complex.I • integralYComplex T u)
      (integralXComplex T v+(-Complex.I) • integralYComplex T v)=0
    simp only [inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,
      complex_sources_orthogonal,hyx,mul_zero,add_zero,zero_add,
      (integralXComplex T).inner_map_map,(integralYComplex T).inner_map_map]
    simp [Complex.conj_I,← mul_assoc]
  change inner ℂ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • rawChannel T Complex.I u)
    ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • rawChannel T (-Complex.I) v)=0
  rw [inner_smul_left,inner_smul_right,hraw,mul_zero,mul_zero]

theorem channel_cross (T : ℝ≥0) (b : Bool) (u v : ComplexInput T) :
    inner ℂ (channel T b u) (channel T (!b) v)=0 := by
  cases b
  · exact channels_orthogonal T u v
  · exact (inner_eq_zero_symm).mp (channels_orthogonal T v u)

theorem channels_energy (T : ℝ≥0) (u v : ComplexInput T) :
    ‖channel T false u+channel T true v‖^2=‖u‖^2+‖v‖^2 := by
  rw [norm_add_sq (𝕜 := ℂ),channels_orthogonal,
    (channel T false).norm_map,(channel T true).norm_map]
  simp

/-- Everywhere-defined bounded complex adjoints, not unbounded Malliavin derivatives. -/
def channelAdjoint (T : ℝ≥0) (b : Bool) : JointComplex →L[ℂ] ComplexInput T :=
  (channel T b).toContinuousLinearMap.adjoint

theorem channelAdjoint_pairing (T : ℝ≥0) (b : Bool) (F : JointComplex) (u : ComplexInput T) :
    inner ℂ (channelAdjoint T b F) u=inner ℂ F (channel T b u) :=
  (channel T b).toContinuousLinearMap.adjoint_inner_left u F

theorem channelAdjoint_self (T : ℝ≥0) (b : Bool) (u : ComplexInput T) :
    channelAdjoint T b (channel T b u)=u :=
  congrArg (fun A : ComplexInput T →L[ℂ] ComplexInput T => A u) (channel T b).adjoint_comp_self

theorem channelAdjoint_cross (T : ℝ≥0) (b : Bool) (u : ComplexInput T) :
    channelAdjoint T b (channel T (!b) u)=0 := by
  apply ext_inner_right ℂ
  intro v
  rw [channelAdjoint_pairing,inner_zero_left]
  exact (inner_eq_zero_symm).mp (channel_cross T b v u)

/-- Correct bounded source-channel Cauchy projections on the actual target L2. -/
def cauchyProjection (T : ℝ≥0) (b : Bool) : JointComplex →L[ℂ] JointComplex :=
  (channel T b).toContinuousLinearMap.comp (channelAdjoint T b)

theorem cauchyProjection_apply (T : ℝ≥0) (b : Bool) (F : JointComplex) :
    cauchyProjection T b F=channel T b (channelAdjoint T b F) := rfl

theorem cauchyProjection_idempotent (T : ℝ≥0) (b : Bool) (F : JointComplex) :
    cauchyProjection T b (cauchyProjection T b F)=cauchyProjection T b F := by
  rw [cauchyProjection_apply,cauchyProjection_apply,channelAdjoint_self]

theorem cauchyProjection_channel (T : ℝ≥0) (b : Bool) (u : ComplexInput T) :
    cauchyProjection T b (channel T b u)=channel T b u := by
  rw [cauchyProjection_apply,channelAdjoint_self]

theorem cauchyProjection_other (T : ℝ≥0) (b : Bool) (u : ComplexInput T) :
    cauchyProjection T b (channel T (!b) u)=0 := by
  rw [cauchyProjection_apply,channelAdjoint_cross,map_zero]

theorem projection_pairing (T : ℝ≥0) (b : Bool) (F : JointComplex) (u : ComplexInput T) :
    inner ℂ (cauchyProjection T b F) (channel T b u)=inner ℂ F (channel T b u) := by
  rw [cauchyProjection_apply,(channel T b).inner_map_map,channelAdjoint_pairing]

theorem projection_cross_pairing (T : ℝ≥0) (b : Bool) (F : JointComplex) (u : ComplexInput T) :
    inner ℂ (cauchyProjection T b F) (channel T (!b) u)=0 := by
  rw [cauchyProjection_apply]
  exact channel_cross T b _ u

/-- Explicit residual is kept until a genuine target range theorem is proved. -/
def residual (T : ℝ≥0) : JointComplex →L[ℂ] JointComplex :=
  ContinuousLinearMap.id ℂ JointComplex-cauchyProjection T false-cauchyProjection T true

theorem residual_pairing (T : ℝ≥0) (b : Bool) (F : JointComplex) (u : ComplexInput T) :
    inner ℂ (residual T F) (channel T b u)=0 := by
  change inner ℂ (F-cauchyProjection T false F-cauchyProjection T true F) (channel T b u)=0
  rw [inner_sub_left,inner_sub_left]
  have h0 : inner ℂ (cauchyProjection T false F) (channel T true u)=0 := by
    simpa using projection_cross_pairing T false F u
  have h1 : inner ℂ (cauchyProjection T true F) (channel T false u)=0 := by
    simpa using projection_cross_pairing T true F u
  cases b
  · rw [projection_pairing,h1]; ring
  · rw [h0,projection_pairing]; ring

/-- Strongest unconditional energy identity has an explicit orthogonal residual. -/
theorem reconstruction_energy (T : ℝ≥0) (F : JointComplex) :
    ‖F‖^2=‖channelAdjoint T false F‖^2+‖channelAdjoint T true F‖^2+‖residual T F‖^2 := by
  let P := cauchyProjection T false F+cauchyProjection T true F
  have hz : inner ℂ (residual T F) P=0 := by
    dsimp only [P]
    rw [inner_add_right,cauchyProjection_apply,cauchyProjection_apply,
      residual_pairing,residual_pairing,add_zero]
  have he := norm_add_sq (𝕜 := ℂ) (residual T F) P
  have hsum : residual T F+P=F := by
    change F-cauchyProjection T false F-cauchyProjection T true F+
      (cauchyProjection T false F+cauchyProjection T true F)=F
    abel
  have hp : ‖P‖^2=‖channelAdjoint T false F‖^2+‖channelAdjoint T true F‖^2 :=
    channels_energy T _ _
  rw [hsum,hz,hp] at he
  simp only [map_zero,mul_zero,add_zero] at he
  linarith

theorem reconstruction_iff (T : ℝ≥0) (F : JointComplex) :
    residual T F=0 ↔ ∃ u v : ComplexInput T, F=channel T false u+channel T true v := by
  constructor
  · intro hz
    refine ⟨channelAdjoint T false F,channelAdjoint T true F,?_⟩
    change F-cauchyProjection T false F-cauchyProjection T true F=0 at hz
    rw [← cauchyProjection_apply,← cauchyProjection_apply]
    have he : F=(F-cauchyProjection T false F-cauchyProjection T true F)+
        (cauchyProjection T false F+cauchyProjection T true F) := by abel
    simpa only [hz,zero_add] using he
  · rintro ⟨u,v,rfl⟩
    change (channel T false u+channel T true v)-
      cauchyProjection T false (channel T false u+channel T true v)-
      cauchyProjection T true (channel T false u+channel T true v)=0
    have h0 : cauchyProjection T false (channel T true v)=0 := by
      simpa using cauchyProjection_other T false v
    have h1 : cauchyProjection T true (channel T false u)=0 := by
      simpa using cauchyProjection_other T true u
    simp only [map_add,cauchyProjection_channel,h0,h1,add_zero,zero_add]
    abel

theorem liftInput_combine (T : ℝ≥0) (J : Input T →ₗᵢ[ℝ] JointL2) (a b : Input T) :
    liftInput T J (combineInput T a b)=
      combine (gaussianProduct.prod gaussianProduct) (J a) (J b) := by
  rw [liftInput_apply,realInput_combine,imagInput_combine]

/-- Exact source-channel value on a real actual common-past integrand. -/
theorem channel_real_input (T : ℝ≥0) (anti : Bool) (a : Input T) :
    channel T anti (combineInput T a 0) = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
      combine (gaussianProduct.prod gaussianProduct) (integralX T a)
        (if anti then -integralY T a else integralY T a) := by
  change (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) •
    (integralXComplex T (combineInput T a 0)+
      (if anti then -Complex.I else Complex.I) • integralYComplex T (combineInput T a 0)) = _
  unfold integralXComplex integralYComplex
  rw [liftInput_combine,liftInput_combine,map_zero,map_zero]
  cases anti <;> simp [combine,map_zero,map_neg,smul_neg,neg_smul]

/-- Agreement with actual stochastic products, including the conjugate-channel sign. -/
theorem channel_real_step (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (A B : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct) (anti : Bool) :
    channel T anti (combineInput T (stepInput T s t hst htT A B hA hB) 0) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • combine (gaussianProduct.prod gaussianProduct)
        (ProductL2Curry.productTensor gaussianProduct gaussianProduct
          (GaussianPastStepCompletion.pastIncrement s t hst A hA) B)
        (if anti then -(ProductL2Curry.productTensor gaussianProduct gaussianProduct A
            (GaussianPastStepCompletion.pastIncrement s t hst B hB))
          else ProductL2Curry.productTensor gaussianProduct gaussianProduct A
            (GaussianPastStepCompletion.pastIncrement s t hst B hB)) := by
  rw [channel_real_input,integralX_stepInput,integralY_stepInput]

theorem channel_coefficients_recover (T : ℝ≥0) (u v : ComplexInput T) :
    channelAdjoint T false (channel T false u+channel T true v)=u ∧
      channelAdjoint T true (channel T false u+channel T true v)=v := by
  have h0 : channelAdjoint T false (channel T true v)=0 := by
    simpa using channelAdjoint_cross T false v
  have h1 : channelAdjoint T true (channel T false u)=0 := by
    simpa using channelAdjoint_cross T true u
  constructor <;> rw [map_add]
  · rw [channelAdjoint_self,h0,add_zero]
  · rw [h1,channelAdjoint_self,zero_add]

theorem channel_closed_range (T : ℝ≥0) (b : Bool) :
    IsClosed ((channel T b).toLinearMap.range : Set JointComplex) :=
  (channel T b).isometry.isClosedEmbedding.isClosed_range

theorem cauchyProjection_eq_self_iff (T : ℝ≥0) (b : Bool) (F : JointComplex) :
    cauchyProjection T b F=F ↔ F ∈ (channel T b).toLinearMap.range := by
  constructor
  · intro he
    exact ⟨channelAdjoint T b F,(cauchyProjection_apply T b F).symm.trans he⟩
  · rintro ⟨u,rfl⟩
    exact cauchyProjection_channel T b u

end OperatorDerivativeRewrite.Foundation.StochasticCauchyComplexChannels
