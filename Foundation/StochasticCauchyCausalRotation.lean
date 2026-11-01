import Foundation.StochasticCauchyMalliavinBridge
import Foundation.StochasticCauchyPhysicalInput

/-! Synchronized causal projections of genuine terminal-direction partial
gradients. The source swap is proved on actual stochastic steps and completed. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyCausalRotation
open InfiniteGaussian GaussianTimeProcess GaussianTimeHilbert GaussianTimeDivergence
open GaussianComplexHorizonIto GaussianFiniteHorizonAdjoint GaussianPredictableAdjoint
open GaussianPredictableFull GaussianContinuousRigidity GaussianTimeFieldNorm
open ProductL2Curry StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyMalliavinBridge
attribute [local instance] StochasticCauchyParameterizedObstruction.predictableTime
  StochasticCauchyParameterizedObstruction.finiteL2Exponent
  StochasticCauchyJointPastIntegral.input_complete StochasticCauchyJointPastIntegral.swapped_complete
  GaussianProductDerivative.coefficientSpace_secondCountable timeHilbert_secondCountable
  GaussianComplexHorizonIto.realPredictableL2_secondCountable

/-- A physical scalar coefficient times an original Gaussian direction. -/
def directionField (h : CoefficientSpace) : JointL2 →L[ℝ] DerivativeField :=
  ((scalarTensor h).compLpL 2 gaussianProduct).comp sourceCurry.toLinearIsometry.toContinuousLinearMap

theorem directionField_tensor (h : CoefficientSpace) (A B : GaussianL2) :
    directionField h (productTensor gaussianProduct gaussianProduct A B)=
      BochnerClosedOperator.tensor gaussianProduct B (scalarTensor h A) := by
  change (scalarTensor h).compLpL 2 gaussianProduct (sourceCurry _)=_
  rw [sourceCurry_tensor]
  apply Lp.ext
  filter_upwards [(scalarTensor h).coeFn_compLpL (BochnerClosedOperator.tensor gaussianProduct B A),
    BochnerClosedOperator.tensor_coeFn gaussianProduct B A,
    BochnerClosedOperator.tensor_coeFn gaussianProduct B (scalarTensor h A)] with w hm ht ho
  rw [hm,ht,ho,map_smul]

theorem directionField_pairing (h k : CoefficientSpace) (F : JointL2) (A B : GaussianL2) :
    inner ℝ (directionField h F) (BochnerClosedOperator.tensor gaussianProduct B (scalarTensor k A))=
      inner ℝ h k * inner ℝ F (productTensor gaussianProduct gaussianProduct A B) := by
  rw [← sourceCurry.inner_map_map F (productTensor gaussianProduct gaussianProduct A B),sourceCurry_tensor]
  rw [L2_inner_eq_integral,L2_inner_eq_integral,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [(scalarTensor h).coeFn_compLpL (sourceCurry F),
    BochnerClosedOperator.tensor_coeFn gaussianProduct B (scalarTensor k A),
    BochnerClosedOperator.tensor_coeFn gaussianProduct B A] with w hm ht ho
  change directionField h F w=scalarTensor h (sourceCurry F w) at hm
  rw [hm,ht,ho,inner_smul_right,inner_smul_right,scalarTensor_pair_inner]
  ring

private theorem finiteField_step (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (A : GaussianL2) (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct) :
    finiteField T (stepMode T s t hst A hA)=scalarTensor (incrementDirection s t) A := by
  have he : extendPredictable T ((trimEquiv T).symm (stepMode T s t hst A hA))=
      ⟨GaussianTimeProductL2.productTensor (intervalVector s t) A,
        past_step_mem_fullPredictable s t A hA⟩ := by
    apply GaussianPredictableFull.itoIntegral.injective
    rw [← finite_integral_eq_extended]
    change realIto T (stepMode T s t hst A hA)=_
    rw [stepMode_integral T s t hst htT]
    exact Lp.ext ((GaussianPastStepCompletion.pastIncrement_coeFn s t hst A hA).trans
      (itoIntegral_past_step s t hst A hA).symm)
  change predictableField (extendPredictable T ((trimEquiv T).symm _))=_
  rw [he]
  exact fieldEmbedding_tensor (intervalVector s t) A

theorem nativeField_tensor (T : ℝ≥0) (a : Lp ℝ 2 (predictableMeasure T)) (B : GaussianL2) :
    StochasticCauchyMalliavinBridge.nativeField T (tensorInput T a B)=
      BochnerClosedOperator.tensor gaussianProduct B (finiteField T a) := by
  change BochnerLinearIsometry.lift gaussianProduct (finiteField T) (nativeFiber T (tensorInput T a B))=_
  rw [nativeFiber_apply]
  change BochnerLinearIsometry.lift gaussianProduct (finiteField T)
    (ProductL2Curry.flip (predictableMeasure T) gaussianProduct
      (curry (predictableMeasure T) gaussianProduct
        (productTensor (predictableMeasure T) gaussianProduct a B)))=_
  rw [curry_productTensor,flip_tensor,BochnerLinearIsometry.lift_tensor]

attribute [local irreducible] directionField StochasticCauchyMalliavinBridge.nativeField
  tensorInput stepMode finiteField

private theorem step_pairing (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (h : CoefficientSpace) (F : JointL2) (A B : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct) :
    inner ℝ (directionField h F)
      (StochasticCauchyMalliavinBridge.nativeField T (tensorInput T (stepMode T s t hst A hA) B)) =
      inner ℝ (directionField h (swap gaussianProduct gaussianProduct F))
        (StochasticCauchyMalliavinBridge.nativeField T (tensorInput T (stepMode T s t hst B hB) A)) := by
  have hx := nativeField_tensor T (stepMode T s t hst A hA) B
  have hy := nativeField_tensor T (stepMode T s t hst B hB) A
  rw [finiteField_step T s t hst htT A hA] at hx
  rw [finiteField_step T s t hst htT B hB] at hy
  rw [hx,hy]
  have hp := directionField_pairing h (incrementDirection s t) F A B
  have hq := directionField_pairing h (incrementDirection s t)
    (swap gaussianProduct gaussianProduct F) B A
  have he := (swap gaussianProduct gaussianProduct).inner_map_map F
    (productTensor gaussianProduct gaussianProduct A B)
  rw [swap_productTensor] at he
  exact hp.trans ((congrArg (inner ℝ h (incrementDirection s t) * ·) he.symm).trans hq.symm)

private theorem relation_pairing (T : ℝ≥0) (h : CoefficientSpace) (F : JointL2)
    (z : Domain T × Domain T) (hz : z ∈ relation T) :
    inner ℝ (directionField h F) (StochasticCauchyMalliavinBridge.nativeField T z.1)=
      inner ℝ (directionField h (swap gaussianProduct gaussianProduct F))
        (StochasticCauchyMalliavinBridge.nativeField T z.2) := by
  refine Submodule.span_induction (p := fun z _ =>
    inner ℝ (directionField h F) (StochasticCauchyMalliavinBridge.nativeField T z.1)=
      inner ℝ (directionField h (swap gaussianProduct gaussianProduct F))
        (StochasticCauchyMalliavinBridge.nativeField T z.2)) ?_ ?_ ?_ ?_ hz
  · rintro z ⟨s,t,A,B,hst,htT,hA,hB,rfl⟩
    exact step_pairing T s t hst htT h F A B hA hB
  · simp
  · intro z w hz hw iz iw
    simpa only [Prod.fst_add,Prod.snd_add,map_add,inner_add_right] using congrArg₂ (·+·) iz iw
  · intro c z hz iz
    simpa only [Prod.smul_fst,Prod.smul_snd,map_smul,inner_smul_right] using congrArg (c*·) iz

theorem paired_fields (T : ℝ≥0) (h : CoefficientSpace) (F : JointL2) (u : Input T) :
    inner ℝ (directionField h F) (fieldX T u)=
      inner ℝ (directionField h (swap gaussianProduct gaussianProduct F)) (fieldY T u) := by
  refine (assemble_dense T).induction_on u ?_ (fun z => ?_)
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · change inner ℝ (directionField h F) (StochasticCauchyMalliavinBridge.nativeField T (assemble T z).val)=
      inner ℝ (directionField h (swap gaussianProduct gaussianProduct F))
        (StochasticCauchyMalliavinBridge.nativeField T (swapInput T (assemble T z)).val)
    rw [swapInput_assemble]
    exact relation_pairing T h F z.val z.property

attribute [local irreducible] fieldX fieldY
/-- Both causal projections of the SAME physical coefficient agree after the
correct source exchange. This is a domain-checked operator identity. -/
theorem causal_rotation (T : ℝ≥0) (h : CoefficientSpace) (F : JointL2) :
    causalY T (directionField h (swap gaussianProduct gaussianProduct F))=
      causalX T (directionField h F) := by
  apply ext_inner_right ℝ
  intro u
  change inner ℝ (HilbertRepresentation.predictableAdjoint (fieldY T) _) u=
    inner ℝ (HilbertRepresentation.predictableAdjoint (fieldX T) _) u
  rw [HilbertRepresentation.predictableAdjoint_pairing,
    HilbertRepresentation.predictableAdjoint_pairing]
  exact (paired_fields T h F u).symm

open StochasticCauchyComplexChannels StochasticCauchyPastReconstruction ComplexL2Isometry
attribute [local instance] StochasticCauchyComplexChannels.complexInput_complete

private theorem combineInput_rotate (T : ℝ≥0) (a b : Input T) :
    combineInput T (-b) a=Complex.I • combineInput T a b := by
  apply Subtype.ext
  change combine (nativeMeasure T) (-b.val) a.val=
    Complex.I • combine (nativeMeasure T) a.val b.val
  simp only [combine,map_neg,smul_add,smul_smul,Complex.I_mul_I,neg_one_smul]
  abel

attribute [local irreducible] channel combineInput sourceDerivative causalX causalY

private theorem channel_CR_reconstruction (T : ℝ≥0) (p q r s : Input T) (K : JointComplex)
    (hr : r= -q) (hs : s=p)
    (he : channel T false (channelScale • (combineInput T p q-Complex.I • combineInput T r s)) +
      channel T true (channelScale • (combineInput T p q+Complex.I • combineInput T r s))=K) :
    ∃ u : ComplexInput T, channel T false u=K := by
  subst r
  subst s
  rw [combineInput_rotate,smul_smul,Complex.I_mul_I,neg_one_smul,
    add_neg_cancel,smul_zero,map_zero,add_zero] at he
  exact ⟨channelScale • (combineInput T p q-(-combineInput T p q)),he⟩

/-- Forward analytic reconstruction on the exact original four-graph class.
No existence of analytic-function derivatives is assumed without these graphs. -/
theorem analytic_graph_reconstruction (T : ℝ≥0) (h : CoefficientSpace) (F G a b : JointL2)
    (hF : F ∈ jointPastL2 T) (hG : G ∈ jointPastL2 T)
    (hFX : (F,directionField h a) ∈ sourceDerivative.graph)
    (hFY : (swap gaussianProduct gaussianProduct F,
      -directionField h (swap gaussianProduct gaussianProduct b)) ∈ sourceDerivative.graph)
    (hGX : (G,directionField h b) ∈ sourceDerivative.graph)
    (hGY : (swap gaussianProduct gaussianProduct G,
      directionField h (swap gaussianProduct gaussianProduct a)) ∈ sourceDerivative.graph) :
    ∃ u : ComplexInput T, channel T false u=
      combine (gaussianProduct.prod gaussianProduct) (center F) (center G) := by
  let p := causalX T (directionField h a)
  let q := causalX T (directionField h b)
  have hyb : causalY T (-directionField h (swap gaussianProduct gaussianProduct b))= -q := by
    rw [map_neg,causal_rotation]
  have hya : causalY T (directionField h (swap gaussianProduct gaussianProduct a))=p :=
    causal_rotation T h a
  have he := malliavin_complex_joint_past T F G hF hG
    (directionField h a) (-directionField h (swap gaussianProduct gaussianProduct b))
    (directionField h b) (directionField h (swap gaussianProduct gaussianProduct a)) hFX hFY hGX hGY
  exact channel_CR_reconstruction T p q _ _ _ hyb hya he

/-- On the same genuine graph class, the centered observable has no anti
channel and is a fixed point of the actual normalized plus projection. -/
theorem analytic_graph_projections (T : ℝ≥0) (h : CoefficientSpace) (F G a b : JointL2)
    (hF : F ∈ jointPastL2 T) (hG : G ∈ jointPastL2 T)
    (hFX : (F,directionField h a) ∈ sourceDerivative.graph)
    (hFY : (swap gaussianProduct gaussianProduct F,
      -directionField h (swap gaussianProduct gaussianProduct b)) ∈ sourceDerivative.graph)
    (hGX : (G,directionField h b) ∈ sourceDerivative.graph)
    (hGY : (swap gaussianProduct gaussianProduct G,
      directionField h (swap gaussianProduct gaussianProduct a)) ∈ sourceDerivative.graph) :
    cauchyProjection T false (combine (gaussianProduct.prod gaussianProduct) (center F) (center G))=
        combine (gaussianProduct.prod gaussianProduct) (center F) (center G) ∧
      cauchyProjection T true (combine (gaussianProduct.prod gaussianProduct) (center F) (center G))=0 := by
  obtain ⟨u,hu⟩ := analytic_graph_reconstruction T h F G a b hF hG hFX hFY hGX hGY
  rw [← hu]
  exact ⟨cauchyProjection_channel T false u,cauchyProjection_other T true u⟩

end OperatorDerivativeRewrite.Foundation.StochasticCauchyCausalRotation
