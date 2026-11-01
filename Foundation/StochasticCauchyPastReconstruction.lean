import Foundation.StochasticCauchyCommonInputBridge
import Foundation.StochasticCauchyComplexChannels
import Foundation.L2GeneratingIndicators
import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-! Reconstruction on the actual independent joint Brownian past. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyPastReconstruction
open InfiniteGaussian GaussianTimeProcess GaussianConditionalIto ProductL2Curry
open StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyCommonInputBridge
attribute [local instance] StochasticCauchyParameterizedObstruction.finiteL2Exponent
  StochasticCauchyJointPastIntegral.input_complete StochasticCauchyJointPastIntegral.swapped_complete

def jointOne : JointL2 := productTensor gaussianProduct gaussianProduct gaussianOne gaussianOne

theorem jointOne_ae : jointOne =ᵐ[gaussianProduct.prod gaussianProduct] fun _ => (1 : ℝ) := by
  filter_upwards [productTensor_coeFn gaussianProduct gaussianProduct gaussianOne gaussianOne,
    (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp gaussianOne_coeFn,
    (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp gaussianOne_coeFn]
    with w ht hx hy
  change jointOne w = _ at ht
  simp only [Function.comp_apply] at hx hy
  simpa only [hx,hy,smul_eq_mul,mul_one] using ht

theorem jointOne_inner (F : JointL2) :
    inner ℝ jointOne F = ∫ w, F w ∂gaussianProduct.prod gaussianProduct := by
  rw [L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [jointOne_ae] with w hw
  simp only [hw,Real.inner_apply,one_mul]

/-- Actual bounded mean-centering, not an abstract replacement for expectation. -/
def center : JointL2 →L[ℝ] JointL2 :=
  ContinuousLinearMap.id ℝ JointL2 -
    (ContinuousLinearMap.toSpanSingleton ℝ jointOne).comp (innerSL ℝ jointOne)

theorem center_apply (F : JointL2) :
    center F = F - (∫ w, F w ∂gaussianProduct.prod gaussianProduct) • jointOne := by
  change F - inner ℝ jointOne F • jointOne = _
  rw [jointOne_inner]

private theorem scalar_tensor (a b : ℝ) :
    productTensor gaussianProduct gaussianProduct (a • gaussianOne) (b • gaussianOne) =
      (a*b) • jointOne := by
  apply Lp.ext
  filter_upwards [productTensor_coeFn gaussianProduct gaussianProduct (a • gaussianOne) (b • gaussianOne),
    (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_smul a gaussianOne),
    (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_smul b gaussianOne),
    Lp.coeFn_smul (a*b) jointOne,productTensor_coeFn gaussianProduct gaussianProduct gaussianOne gaussianOne]
    with w ht ha hb hc ho
  change jointOne w = _ at ho
  simp only [Function.comp_apply,Pi.smul_apply] at ha hb
  simp only [ht,ha,hb,hc,ho,Pi.smul_apply,smul_eq_mul]
  ring

theorem center_tensor (F G : GaussianL2) :
    center (productTensor gaussianProduct gaussianProduct F G) = centeredTensor F G := by
  change productTensor gaussianProduct gaussianProduct F G -
    inner ℝ jointOne (productTensor gaussianProduct gaussianProduct F G) • jointOne = _
  have hi : inner ℝ jointOne (productTensor gaussianProduct gaussianProduct F G) =
      (∫ w, F w ∂gaussianProduct) * (∫ w, G w ∂gaussianProduct) := by
    change inner ℝ (productTensor gaussianProduct gaussianProduct gaussianOne gaussianOne) _ = _
    rw [tensor_inner,gaussianOne_inner_eq_integral,gaussianOne_inner_eq_integral]
  rw [hi]
  exact congrArg (fun x => productTensor gaussianProduct gaussianProduct F G - x)
    (scalar_tensor _ _).symm

def jointPast (T : ℝ≥0) : MeasurableSpace (SampleSpace × SampleSpace) :=
  (naturalFiltration T).prod (naturalFiltration T)

theorem jointPast_le (T : ℝ≥0) : jointPast T ≤ (inferInstance : MeasurableSpace (SampleSpace × SampleSpace)) :=
  sup_le_sup (MeasurableSpace.comap_mono (naturalFiltration.le T))
    (MeasurableSpace.comap_mono (naturalFiltration.le T))

/-- Independently specified target: all actual joint-past measurable L2 observables. -/
def jointPastL2 (T : ℝ≥0) : Submodule ℝ JointL2 :=
  lpMeas ℝ ℝ (jointPast T) 2 (gaussianProduct.prod gaussianProduct)

private theorem indicator_tensor (T : ℝ≥0) (A B : Set SampleSpace)
    (hA : MeasurableSet[naturalFiltration T] A) (hB : MeasurableSet[naturalFiltration T] B) :
    indicatorConstLp 2 ((naturalFiltration.le T A hA).prod (naturalFiltration.le T B hB))
      (measure_ne_top (gaussianProduct.prod gaussianProduct) (A ×ˢ B)) (1 : ℝ) =
    productTensor gaussianProduct gaussianProduct
      (indicatorConstLp 2 (naturalFiltration.le T A hA) (measure_ne_top gaussianProduct A) (1 : ℝ))
      (indicatorConstLp 2 (naturalFiltration.le T B hB) (measure_ne_top gaussianProduct B) (1 : ℝ)) := by
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (p := 2) (c := (1 : ℝ)) (hμs := by finiteness)
      (μ := gaussianProduct.prod gaussianProduct) (hs := (naturalFiltration.le T A hA).prod (naturalFiltration.le T B hB)),
    productTensor_coeFn gaussianProduct gaussianProduct
      (indicatorConstLp 2 (naturalFiltration.le T A hA) (measure_ne_top gaussianProduct A) (1 : ℝ))
      (indicatorConstLp 2 (naturalFiltration.le T B hB) (measure_ne_top gaussianProduct B) (1 : ℝ)),
    (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
      (indicatorConstLp_coeFn (p := 2) (c := (1 : ℝ)) (hμs := by finiteness) (μ := gaussianProduct) (hs := naturalFiltration.le T A hA)),
    (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
      (indicatorConstLp_coeFn (p := 2) (c := (1 : ℝ)) (hμs := by finiteness) (μ := gaussianProduct) (hs := naturalFiltration.le T B hB))]
    with w hw ht ha hb
  simp only [Function.comp_apply] at ha hb
  rw [hw,ht,ha,hb]
  simp only [smul_eq_mul]
  by_cases hwa : w.1 ∈ A <;> by_cases hwb : w.2 ∈ B <;> simp [hwa,hwb]

/-- The real synchronized projection reconstructs every centered ACTUAL joint-past L2 observable. -/
theorem joint_past_representation (T : ℝ≥0) (F : JointL2) (hF : F ∈ jointPastL2 T) :
    integralX T (adjointX T (center F)) + integralY T (adjointY T (center F)) = center F := by
  let K := ((realProjection T).comp center - center).ker
  have hc : IsClosed (K : Set JointL2) := ContinuousLinearMap.isClosed_ker _
  have hK : jointPastL2 T ≤ K := by
    let S : Set (Set (SampleSpace × SampleSpace)) :=
      image2 (· ×ˢ ·) {A | MeasurableSet[naturalFiltration T] A}
        {B | MeasurableSet[naturalFiltration T] B}
    have hd : (generatingIndicatorSpan (gaussianProduct.prod gaussianProduct) S).topologicalClosure =
        jointPastL2 T := by
      exact generatingIndicatorSpan_closure _ (jointPast_le T) S
        (@generateFrom_prod SampleSpace SampleSpace (naturalFiltration T) (naturalFiltration T))
        (@isPiSystem_prod SampleSpace SampleSpace (naturalFiltration T) (naturalFiltration T))
        ⟨univ,(show MeasurableSet[naturalFiltration T] univ from MeasurableSet.univ),
          univ,(show MeasurableSet[naturalFiltration T] univ from MeasurableSet.univ),univ_prod_univ⟩
    rw [← hd]
    apply (generatingIndicatorSpan (gaussianProduct.prod gaussianProduct) S).topologicalClosure_minimal ?_ hc
    apply Submodule.span_le.mpr
    rintro f ⟨s,⟨A,hA,B,hB,rfl⟩,hs,rfl⟩
    change realProjection T (center _) - center _ = 0
    rw [indicator_tensor T A B hA hB,center_tensor]
    exact sub_eq_zero.mpr (realProjection_tensor T _ _
      (mem_lpMeas_indicatorConstLp (naturalFiltration.le T) hA (measure_ne_top gaussianProduct A))
      (mem_lpMeas_indicatorConstLp (naturalFiltration.le T) hB (measure_ne_top gaussianProduct B)))
  exact sub_eq_zero.mp (hK hF)

open StochasticCauchyComplexChannels ComplexL2Isometry

def channelScale : ℂ := (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)
private theorem q_two : channelScale*channelScale*2=1 := by
  have hr : (Real.sqrt 2)⁻¹*(Real.sqrt 2)⁻¹*2=(1 : ℝ) := by
    rw [← pow_two,inv_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  unfold channelScale
  exact_mod_cast hr

/-- Exact unitary change from the two actual real noises to dZ and dZbar. -/
theorem channel_decomposition (T : ℝ≥0) (u v : ComplexInput T) :
    channel T false (channelScale • (u-Complex.I • v)) +
      channel T true (channelScale • (u+Complex.I • v)) =
      integralXComplex T u+integralYComplex T v := by
  change channelScale • (integralXComplex T (channelScale • (u-Complex.I • v))+
    Complex.I • integralYComplex T (channelScale • (u-Complex.I • v)))+
    channelScale • (integralXComplex T (channelScale • (u+Complex.I • v))+
    (-Complex.I) • integralYComplex T (channelScale • (u+Complex.I • v))) = _
  simp only [map_smul,map_sub,map_add,smul_add,smul_sub,smul_smul]
  match_scalars <;> ring_nf <;> simpa only [pow_two,Complex.I_mul_I,mul_neg_one,neg_mul,neg_neg] using q_two

/-- The existing complex residual vanishes on the entire actual complexified pair range. -/
theorem residual_pair (T : ℝ≥0) (u v : ComplexInput T) :
    residual T (integralXComplex T u+integralYComplex T v)=0 :=
  (reconstruction_iff T _).mpr ⟨channelScale • (u-Complex.I • v),channelScale • (u+Complex.I • v),
    (channel_decomposition T u v).symm⟩

/-- Both real components are independently specified ACTUAL joint-past observables. -/
theorem complex_joint_past_reconstruction (T : ℝ≥0) (F G : JointL2)
    (hF : F ∈ jointPastL2 T) (hG : G ∈ jointPastL2 T) :
    residual T (combine (gaussianProduct.prod gaussianProduct) (center F) (center G))=0 := by
  have hx := joint_past_representation T F hF
  have hy := joint_past_representation T G hG
  have he :
      integralXComplex T (combineInput T (adjointX T (center F)) (adjointX T (center G)))+
        integralYComplex T (combineInput T (adjointY T (center F)) (adjointY T (center G))) =
      combine (gaussianProduct.prod gaussianProduct) (center F) (center G) := by
    unfold integralXComplex integralYComplex
    rw [liftInput_combine,liftInput_combine]
    calc
      _ = combine (gaussianProduct.prod gaussianProduct)
          (integralX T (adjointX T (center F)) + integralY T (adjointY T (center F)))
          (integralX T (adjointX T (center G)) + integralY T (adjointY T (center G))) := by
        simp only [combine,map_add,smul_add]
        abel
      _ = _ := congrArg₂ (combine (gaussianProduct.prod gaussianProduct)) hx hy
  rw [← he]
  exact residual_pair T _ _

/-- Exact normalized stochastic Cauchy reconstruction on the actual joint past. -/
theorem complex_joint_past_formula (T : ℝ≥0) (F G : JointL2)
    (hF : F ∈ jointPastL2 T) (hG : G ∈ jointPastL2 T) :
    cauchyProjection T false (combine (gaussianProduct.prod gaussianProduct) (center F) (center G)) +
      cauchyProjection T true (combine (gaussianProduct.prod gaussianProduct) (center F) (center G)) =
      combine (gaussianProduct.prod gaussianProduct) (center F) (center G) := by
  let H := combine (gaussianProduct.prod gaussianProduct) (center F) (center G)
  have hz := complex_joint_past_reconstruction T F G hF hG
  change H - cauchyProjection T false H - cauchyProjection T true H = 0 at hz
  have he : H = (H-cauchyProjection T false H-cauchyProjection T true H) +
      (cauchyProjection T false H+cauchyProjection T true H) := by abel
  simpa only [hz,zero_add] using he.symm

/-- No residual energy remains after the ACTUAL joint-past domain is checked. -/
theorem complex_joint_past_energy (T : ℝ≥0) (F G : JointL2)
    (hF : F ∈ jointPastL2 T) (hG : G ∈ jointPastL2 T) :
    ‖combine (gaussianProduct.prod gaussianProduct) (center F) (center G)‖^2 =
      ‖channelAdjoint T false (combine (gaussianProduct.prod gaussianProduct) (center F) (center G))‖^2 +
      ‖channelAdjoint T true (combine (gaussianProduct.prod gaussianProduct) (center F) (center G))‖^2 := by
  have he := reconstruction_energy T (combine (gaussianProduct.prod gaussianProduct) (center F) (center G))
  simpa only [complex_joint_past_reconstruction T F G hF hG,norm_zero,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0),add_zero] using he

end OperatorDerivativeRewrite.Foundation.StochasticCauchyPastReconstruction
