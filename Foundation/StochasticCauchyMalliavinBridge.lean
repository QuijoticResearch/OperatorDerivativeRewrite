import Foundation.StochasticCauchyPastReconstruction
import Foundation.BochnerLiftAdjointInclusion
import Foundation.IBMNonlinearAverageGraph

/-! Actual closed Gaussian partial derivatives and synchronized causal projection.
The unbounded domain is retained; bounded stochastic adjoints are identified there. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyMalliavinBridge
open InfiniteGaussian GaussianTimeProcess GaussianComplexHorizonIto ProductL2Curry
open GaussianPredictableAdjoint GaussianFiniteHorizonAdjoint GaussianPredictableFull
open StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyPastReconstruction
attribute [local instance] StochasticCauchyParameterizedObstruction.predictableTime
  StochasticCauchyParameterizedObstruction.finiteL2Exponent
  StochasticCauchyJointPastIntegral.input_complete StochasticCauchyJointPastIntegral.swapped_complete
  GaussianProductDerivative.coefficientSpace_secondCountable
  GaussianComplexHorizonIto.realPredictableL2_secondCountable

private theorem swap_twice (F : JointL2) :
    swap gaussianProduct gaussianProduct (swap gaussianProduct gaussianProduct F)=F :=
  IBMNonlinearAverageGraph.swap_swap F

/-- Other source outside; differentiated source inside the actual Bochner fiber. -/
def sourceCurry : JointL2 ≃ₗᵢ[ℝ] Lp GaussianL2 2 gaussianProduct where
  toLinearEquiv := {
    toFun := fun F => curryEquiv gaussianProduct gaussianProduct (swap gaussianProduct gaussianProduct F)
    invFun := fun H => swap gaussianProduct gaussianProduct ((curryEquiv gaussianProduct gaussianProduct).symm H)
    left_inv := by
      intro F
      change swap gaussianProduct gaussianProduct
        ((curryEquiv gaussianProduct gaussianProduct).symm
          (curryEquiv gaussianProduct gaussianProduct (swap gaussianProduct gaussianProduct F)))=F
      rw [LinearIsometryEquiv.symm_apply_apply,swap_twice]
    right_inv := by
      intro H
      change curryEquiv gaussianProduct gaussianProduct
        (swap gaussianProduct gaussianProduct (swap gaussianProduct gaussianProduct
          ((curryEquiv gaussianProduct gaussianProduct).symm H)))=H
      rw [swap_twice,LinearIsometryEquiv.apply_symm_apply]
    map_add' := by intro F G; rw [map_add,map_add]
    map_smul' := by intro c F; simp only [map_smul,RingHom.id_apply] }
  norm_map' F := by
    change ‖curryEquiv gaussianProduct gaussianProduct (swap gaussianProduct gaussianProduct F)‖=‖F‖
    rw [(curryEquiv gaussianProduct gaussianProduct).norm_map,
    (swap gaussianProduct gaussianProduct).norm_map]

theorem sourceCurry_apply (F : JointL2) :
    sourceCurry F=curryEquiv gaussianProduct gaussianProduct (swap gaussianProduct gaussianProduct F) := rfl

private theorem uncurry_flip (F : Lp GaussianL2 2 gaussianProduct) :
    (curryEquiv gaussianProduct gaussianProduct).symm (ProductL2Curry.flip gaussianProduct gaussianProduct F)=
      swap gaussianProduct gaussianProduct ((curryEquiv gaussianProduct gaussianProduct).symm F) := by
  exact (curryEquiv gaussianProduct gaussianProduct).symm_apply_apply _

attribute [local irreducible] sourceCurry

abbrev DerivativeField := Lp GaussianVectorL2 2 gaussianProduct

/-- The ORIGINAL full closed derivative in each Gaussian fiber, with actual Bochner L2 values. -/
def sourceDerivative : JointL2 →ₗ.[ℝ] DerivativeField :=
  AdjointUnitaryTransport.pullback sourceCurry
    (BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative)

theorem sourceDerivative_graph (F : JointL2) (H : DerivativeField) :
    (F,H) ∈ sourceDerivative.graph ↔ ∀ᵐ w ∂gaussianProduct,
      (sourceCurry F w,H w) ∈ closedCylindricalDerivative.graph := by
  rw [sourceDerivative,AdjointUnitaryTransport.mem_pullback_graph,
    BochnerClosedOperator.mem_lift_graph_iff]

theorem sourceDerivative_closed : sourceDerivative.IsClosed :=
  AdjointUnitaryTransport.pullback_isClosed sourceCurry _
    (BochnerClosedOperator.lift_isClosed gaussianProduct _ closedCylindricalDerivative_isClosed)

theorem sourceDerivative_dense : Dense (sourceDerivative.domain : Set JointL2) :=
  AdjointUnitaryTransport.pullback_dense_domain sourceCurry _
    (BochnerClosedOperator.lift_dense_domain gaussianProduct _ closedCylindricalDerivative_dense_domain)

/-- Actual finite predictable field embedded in the original Gaussian derivative value space. -/
def finiteField (T : ℝ≥0) : Lp ℝ 2 (predictableMeasure T) →ₗᵢ[ℝ] GaussianVectorL2 :=
  predictableField.comp ((extendPredictable T).comp (trimEquiv T).symm.toLinearIsometry)

private theorem finiteField_graph (T : ℝ≥0) (a : Lp ℝ 2 (predictableMeasure T)) :
    (finiteField T a,realIto T a) ∈ hilbertDivergence.graph := by
  have h := predictableField_divergence_graph (extendPredictable T ((trimEquiv T).symm a))
  change (finiteField T a,GaussianPredictableFull.itoIntegral (extendPredictable T ((trimEquiv T).symm a))) ∈ _ at h
  rw [← finite_integral_eq_extended] at h
  exact h

private theorem finite_ibp (T : ℝ≥0) (f : GaussianL2) (h : GaussianVectorL2)
    (hf : (f,h) ∈ closedCylindricalDerivative.graph) (a : Lp ℝ 2 (predictableMeasure T)) :
    inner ℝ h (finiteField T a)=inner ℝ f (realIto T a) := by
  obtain ⟨u,hu,hv⟩ := closedCylindricalDerivative.mem_graph_iff.mp hf
  obtain ⟨v,hh,hi⟩ := hilbertDivergence.mem_graph_iff.mp (finiteField_graph T a)
  have hp := (closedCylindricalDerivative.adjoint_isFormalAdjoint
    closedCylindricalDerivative_dense_domain).symm u v
  change inner ℝ (closedCylindricalDerivative u) (v : GaussianVectorL2)=
    inner ℝ (u : GaussianL2) (hilbertDivergence v) at hp
  simpa only [hu,hv,hh,hi] using hp

/-- Actual native input in other-source-outside Bochner coordinates. -/
def nativeFiber (T : ℝ≥0) : Domain T →ₗᵢ[ℝ]
    Lp (Lp ℝ 2 (predictableMeasure T)) 2 gaussianProduct :=
  (ProductL2Curry.flip (predictableMeasure T) gaussianProduct).comp
    (curryEquiv (predictableMeasure T) gaussianProduct).toLinearIsometry

theorem nativeFiber_apply (T : ℝ≥0) (U : Domain T) :
    nativeFiber T U=ProductL2Curry.flip (predictableMeasure T) gaussianProduct
      (curryEquiv (predictableMeasure T) gaussianProduct U) := rfl

attribute [local irreducible] nativeFiber

/-- Existing source integral becomes the actual scalar Ito map in almost every fiber. -/
theorem firstIntegral_fiber (T : ℝ≥0) (U : Domain T) :
    sourceCurry (firstIntegral T U)=
      BochnerLinearIsometry.lift gaussianProduct (realIto T) (nativeFiber T U) := by
  rw [sourceCurry_apply]
  change curryEquiv gaussianProduct gaussianProduct
    (swap gaussianProduct gaussianProduct
      ((curryEquiv gaussianProduct gaussianProduct).symm
        (ProductL2Curry.flip gaussianProduct gaussianProduct
          (BochnerLinearIsometry.lift gaussianProduct (realIto T)
            (ProductL2Curry.flip (predictableMeasure T) gaussianProduct
              (curryEquiv (predictableMeasure T) gaussianProduct U)))))) = _
  rw [← nativeFiber_apply,uncurry_flip,swap_twice,LinearIsometryEquiv.apply_symm_apply]

/-- The actual native Gaussian derivative field corresponding to an integrand. -/
def nativeField (T : ℝ≥0) : Domain T →ₗᵢ[ℝ] DerivativeField :=
  (BochnerLinearIsometry.lift gaussianProduct (finiteField T)).comp (nativeFiber T)

/-- Full closed partial-domain integration by parts for EVERY native stochastic input. -/
theorem native_ibp (T : ℝ≥0) (F : JointL2) (H : DerivativeField)
    (hF : (F,H) ∈ sourceDerivative.graph) (U : Domain T) :
    inner ℝ H (nativeField T U)=inner ℝ F (firstIntegral T U) := by
  rw [← sourceCurry.inner_map_map F (firstIntegral T U),firstIntegral_fiber,
    L2_inner_eq_integral,L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [(sourceDerivative_graph F H).mp hF,
    BochnerLinearIsometry.lift_coeFn gaussianProduct (finiteField T) (nativeFiber T U),
    BochnerLinearIsometry.lift_coeFn gaussianProduct (realIto T) (nativeFiber T U)] with w hf hfield hito
  change nativeField T U w = _ at hfield
  rw [hfield,hito]
  exact finite_ibp T _ _ hf _

/-- The SAME completed synchronized input, embedded in the full partial derivative field. -/
def fieldX (T : ℝ≥0) : Input T →ₗᵢ[ℝ] DerivativeField :=
  (nativeField T).comp (Input T).subtypeₗᵢ

def fieldY (T : ℝ≥0) : Input T →ₗᵢ[ℝ] DerivativeField :=
  (nativeField T).comp ((SwappedInput T).subtypeₗᵢ.comp (swapInput T).toLinearIsometry)

/-- Genuine orthogonal causal projections, as adjoints of actual field embeddings. -/
def causalX (T : ℝ≥0) : DerivativeField →L[ℝ] Input T :=
  HilbertRepresentation.predictableAdjoint (fieldX T)
def causalY (T : ℝ≥0) : DerivativeField →L[ℝ] Input T :=
  HilbertRepresentation.predictableAdjoint (fieldY T)

/-- The manuscript's derivative-projection step, on the precise ORIGINAL closed domain. -/
theorem adjointX_derivative (T : ℝ≥0) (F : JointL2) (H : DerivativeField)
    (hF : (F,H) ∈ sourceDerivative.graph) : adjointX T F=causalX T H := by
  apply ext_inner_right ℝ
  intro u
  rw [show adjointX T = HilbertRepresentation.predictableAdjoint (integralX T) from rfl,
    HilbertRepresentation.predictableAdjoint_pairing,
    show causalX T = HilbertRepresentation.predictableAdjoint (fieldX T) from rfl,
    HilbertRepresentation.predictableAdjoint_pairing]
  exact (native_ibp T F H hF u).symm

theorem adjointY_derivative (T : ℝ≥0) (F : JointL2) (H : DerivativeField)
    (hF : (swap gaussianProduct gaussianProduct F,H) ∈ sourceDerivative.graph) :
    adjointY T F=causalY T H := by
  apply ext_inner_right ℝ
  intro u
  rw [show adjointY T = HilbertRepresentation.predictableAdjoint (integralY T) from rfl,
    HilbertRepresentation.predictableAdjoint_pairing,
    show causalY T = HilbertRepresentation.predictableAdjoint (fieldY T) from rfl,
    HilbertRepresentation.predictableAdjoint_pairing]
  have hp := native_ibp T (swap gaussianProduct gaussianProduct F) H hF (swapInput T u)
  have he := (swap gaussianProduct gaussianProduct).inner_map_map F
    (secondIntegral T (swapInput T u))
  change inner ℝ (swap gaussianProduct gaussianProduct F)
    (swap gaussianProduct gaussianProduct (swap gaussianProduct gaussianProduct (firstIntegral T (swapInput T u))))=_ at he
  rw [swap_twice] at he
  exact he.symm.trans hp.symm

theorem sourceCurry_tensor (F G : GaussianL2) :
    sourceCurry (productTensor gaussianProduct gaussianProduct F G)=BochnerClosedOperator.tensor gaussianProduct G F := by
  rw [sourceCurry_apply,swap_productTensor]
  exact curry_productTensor gaussianProduct gaussianProduct G F

/-- Actual closed partial graph on separated observables; the OTHER source need only be L2. -/
theorem sourceDerivative_tensor (F G : GaussianL2) (H : GaussianVectorL2)
    (hF : (F,H) ∈ closedCylindricalDerivative.graph) :
    (productTensor gaussianProduct gaussianProduct F G,BochnerClosedOperator.tensor gaussianProduct G H) ∈
      sourceDerivative.graph := by
  rw [sourceDerivative,AdjointUnitaryTransport.mem_pullback_graph,sourceCurry_tensor]
  exact BochnerClosedOperator.tensor_graph gaussianProduct closedCylindricalDerivative G F H hF

private theorem source_one : (jointOne,(0 : DerivativeField)) ∈ sourceDerivative.graph := by
  rw [sourceDerivative_graph]
  have he : sourceCurry jointOne=BochnerClosedOperator.tensor gaussianProduct gaussianOne gaussianOne :=
    sourceCurry_tensor gaussianOne gaussianOne
  rw [he]
  filter_upwards [BochnerClosedOperator.tensor_coeFn gaussianProduct gaussianOne gaussianOne,
    Lp.coeFn_zero GaussianVectorL2 2 gaussianProduct] with w hw hz
  rw [hw,hz]
  exact closedDerivative_constant_graph (gaussianOne w)

theorem adjoints_one (T : ℝ≥0) : adjointX T jointOne=0 ∧ adjointY T jointOne=0 := by
  constructor
  · rw [adjointX_derivative T jointOne 0 source_one,map_zero]
  · have he : swap gaussianProduct gaussianProduct jointOne=jointOne :=
      swap_productTensor gaussianProduct gaussianProduct gaussianOne gaussianOne
    rw [adjointY_derivative T jointOne 0 (by rw [he]; exact source_one),map_zero]

theorem adjoints_center (T : ℝ≥0) (F : JointL2) :
    adjointX T (center F)=adjointX T F ∧ adjointY T (center F)=adjointY T F := by
  rw [center_apply]
  simp only [map_sub,map_smul,(adjoints_one T).1,(adjoints_one T).2,smul_zero,sub_zero,and_self]

/-- Genuine joint-past Clark--Ocone on the full intersection of the two original partial domains. -/
theorem malliavin_joint_past (T : ℝ≥0) (F : JointL2) (hF : F ∈ jointPastL2 T)
    (HX HY : DerivativeField) (hX : (F,HX) ∈ sourceDerivative.graph)
    (hY : (swap gaussianProduct gaussianProduct F,HY) ∈ sourceDerivative.graph) :
    integralX T (causalX T HX)+integralY T (causalY T HY)=center F := by
  have he := joint_past_representation T F hF
  rw [(adjoints_center T F).1,(adjoints_center T F).2,
    adjointX_derivative T F HX hX,adjointY_derivative T F HY hY] at he
  exact he

open StochasticCauchyComplexChannels ComplexL2Isometry

/-- Complex Clark--Ocone with four explicit original closed partial graphs and correct noise rotation. -/
theorem malliavin_complex_joint_past (T : ℝ≥0) (F G : JointL2)
    (hF : F ∈ jointPastL2 T) (hG : G ∈ jointPastL2 T)
    (FX FY GX GY : DerivativeField)
    (hFX : (F,FX) ∈ sourceDerivative.graph)
    (hFY : (swap gaussianProduct gaussianProduct F,FY) ∈ sourceDerivative.graph)
    (hGX : (G,GX) ∈ sourceDerivative.graph)
    (hGY : (swap gaussianProduct gaussianProduct G,GY) ∈ sourceDerivative.graph) :
    channel T false (channelScale •
      (combineInput T (causalX T FX) (causalX T GX) -
        Complex.I • combineInput T (causalY T FY) (causalY T GY))) +
      channel T true (channelScale •
      (combineInput T (causalX T FX) (causalX T GX) +
        Complex.I • combineInput T (causalY T FY) (causalY T GY))) =
      combine (gaussianProduct.prod gaussianProduct) (center F) (center G) := by
  rw [channel_decomposition]
  unfold integralXComplex integralYComplex
  rw [liftInput_combine,liftInput_combine]
  calc
    _ = combine (gaussianProduct.prod gaussianProduct)
        (integralX T (causalX T FX) + integralY T (causalY T FY))
        (integralX T (causalX T GX) + integralY T (causalY T GY)) := by
      simp only [combine,map_add,smul_add]
      abel
    _ = _ := congrArg₂ (combine (gaussianProduct.prod gaussianProduct))
      (malliavin_joint_past T F hF FX FY hFX hFY)
      (malliavin_joint_past T G hG GX GY hGX hGY)

end OperatorDerivativeRewrite.Foundation.StochasticCauchyMalliavinBridge
