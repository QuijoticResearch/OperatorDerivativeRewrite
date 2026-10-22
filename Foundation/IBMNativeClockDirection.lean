import Foundation.IBMNativeUnboundedDirections
import Foundation.IBMClockInnovationObstruction

/-! Clock sign symmetry removes the drift-product restriction for actual native directions. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNativeClockDirection
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMFiniteAverageCore IBMIntrinsicChainRule IBMNativeDeterministicFields
open IBMNativeDirectionalMaps IBMNativeDirectionalDrift IBMNativeUnboundedDirections
open IBMClockConditionalCorrection IBMClockInnovationObstruction
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
set_option backward.isDefEq.respectTransparency false

theorem partial_value (k : CoefficientSpace) :
    partialDerivative.adjoint ⟨directionField k,direction_partial_mem k⟩ =
      BochnerClosedOperator.tensor gaussianProduct gaussianOne (firstChaosEmbedding k) := by
  have hg := BochnerClosedOperator.tensor_graph gaussianProduct hilbertDivergence
    gaussianOne _ _ (GaussianFirstChaosRecovery.firstChaos_divergence_graph k)
  exact ((partialDerivative.adjoint.image_iff (direction_partial_mem k)).mpr
    (LinearPMap.le_graph_of_le
      (BochnerLiftAdjointInclusion.lift_adjoint_le gaussianProduct closedCylindricalDerivative
        closedCylindricalDerivative_dense_domain) hg)).symm

theorem inverse_clock_tensor (v : GaussianL2) :
    clockUnitary.symm (BochnerClosedOperator.tensor gaussianProduct gaussianOne v) = clockLift v := by
  have he : clockLift v = ProductL2Curry.productTensor gaussianProduct gaussianProduct gaussianOne v := by
    apply Lp.ext
    have ho := (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
      gaussianOne_coeFn
    filter_upwards [clockLift_coeFn v,ProductL2Curry.productTensor_coeFn gaussianProduct gaussianProduct gaussianOne v,
      ho] with ω hc ht ho
    change gaussianOne ω.1 = 1 at ho
    rw [hc,ht,ho,one_smul]
  apply clockUnitary.injective
  rw [LinearIsometryEquiv.apply_symm_apply,he]
  exact (ProductL2Curry.curry_productTensor gaussianProduct gaussianProduct gaussianOne v).symm

theorem direction_zero : directionField 0 = 0 := by
  apply (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm.injective
  change uncurryField (directionField 0) = _
  rw [uncurry_direction,map_zero]
  apply Lp.ext
  exact (constantVector_ae 0).trans (Lp.coeFn_zero _ _ _).symm

theorem clock_projection_zero (k : CoefficientSpace) :
    IntrinsicSpace.orthogonalProjectionOnto (clockLift (firstChaosEmbedding k)) = 0 := by
  apply Subtype.ext
  change IntrinsicSpace.starProjection (clockLift (firstChaosEmbedding k)) = 0
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero IntrinsicSpace.zero_mem
  intro f hf
  rw [sub_zero]
  apply odd_inner_zero _ _ f hf
  rw [clockLift_reflection,GaussianSampleReflection.reflection_firstChaos,map_neg]

theorem nativeDrift_zero (k : CoefficientSpace) : nativeDrift 0 k = 0 := by
  have hc : directionField k ∈ clockDerivative.adjoint.domain := by
    rw [clock_adjoint_domain]
    exact direction_partial_mem k
  obtain ⟨hp,hv⟩ := ambient_pair_divergence 0 ⟨directionField k,hc⟩
  have he : nativeField 0 k = pairField 0 (directionField k) := by
    rw [nativeField,direction_zero]
  have hcval := (clock_adjoint_apply _ hc (direction_partial_mem k)).trans
    ((congrArg clockUnitary.symm (partial_value k)).trans (inverse_clock_tensor _))
  have hz : jointDivergence ⟨pairField 0 (directionField k),hp⟩ = 0 := by
    have hv' : jointDivergence ⟨pairField 0 (directionField k),hp⟩ =
        IntrinsicSpace.orthogonalProjectionOnto
          (sourceDerivative.adjoint 0 + clockDerivative.adjoint ⟨directionField k,hc⟩) := hv
    have hsval : sourceDerivative.adjoint (0 : sourceDerivative.adjoint.domain) = 0 :=
      sourceDerivative.adjoint.map_zero
    exact hv'.trans (by rw [hsval,zero_add,hcval,clock_projection_zero])
  have hg : (nativeField 0 k,(0 : IntrinsicSpace)) ∈ jointDivergence.graph :=
    jointDivergence.mem_graph_iff.mpr ⟨⟨_,hp⟩,he.symm,hz⟩
  have hval := ((jointDivergence.image_iff (native_mem 0 k)).mpr hg).symm
  exact congrArg (fun z : IntrinsicSpace => (z : JointL2)) hval

theorem clock_product_mem (k : CoefficientSpace) (f : jointDerivative.domain) :
    MemLp (fun ω => (((f : IntrinsicSpace) : JointL2) ω)*nativeDrift 0 k ω)
      2 IBMSourceLaws.jointMeasure := by
  have hz : (fun ω => (((f : IntrinsicSpace) : JointL2) ω)*nativeDrift 0 k ω)
      =ᵐ[IBMSourceLaws.jointMeasure] fun _ => (0 : ℝ) := by
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := IBMSourceLaws.jointMeasure)] with ω hω
    change (0 : JointL2) ω = 0 at hω
    rw [nativeDrift_zero,hω,mul_zero]
  exact (memLp_congr_ae hz).mpr (memLp_const (0 : ℝ))

theorem unbounded_clock_mem (k : CoefficientSpace) (f : jointDerivative.domain) :
    lift 0 k ((f : IntrinsicSpace) : JointL2) ∈ jointDivergence.domain :=
  unbounded_mem 0 k f (clock_product_mem k f)

theorem clock_output (k : CoefficientSpace) (f : jointDerivative.domain) :
    output 0 k f (clock_product_mem k f) =
      IntrinsicSpace.orthogonalProjectionOnto (-contract 0 k (jointDerivative f)) := by
  have he : drift ((f : IntrinsicSpace) : JointL2) (nativeDrift 0 k) (clock_product_mem k f) = 0 := by
    apply Lp.ext
    filter_upwards [drift_ae ((f : IntrinsicSpace) : JointL2) (nativeDrift 0 k) (clock_product_mem k f),
      Lp.coeFn_zero (E := ℝ) (p := 2) (μ := IBMSourceLaws.jointMeasure)] with ω hd hz
    change (0 : JointL2) ω = 0 at hz
    rw [hd,nativeDrift_zero,hz,mul_zero]
  change IntrinsicSpace.orthogonalProjectionOnto (_ - _) = _
  rw [he,zero_sub]

theorem unbounded_clock_value (k : CoefficientSpace) (f : jointDerivative.domain) :
    jointDivergence ⟨lift 0 k ((f : IntrinsicSpace) : JointL2),unbounded_clock_mem k f⟩ =
      IntrinsicSpace.orthogonalProjectionOnto (-contract 0 k (jointDerivative f)) :=
  (unbounded_value 0 k f (clock_product_mem k f)).trans (clock_output k f)

theorem clock_direction_ne_zero (k : CoefficientSpace) (hk : k ≠ 0) : nativeField 0 k ≠ 0 := by
  intro hz
  have hc := native_coordinates 0 k 1
  rw [hz] at hc
  simp only [PiLp.zero_apply,map_zero,show ¬(1 : Fin 2)=0 from by decide,ite_false] at hc
  have he : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, (0 : CoefficientSpace) = k :=
    (Lp.coeFn_zero (E := CoefficientSpace) (p := 2) (μ := IBMSourceLaws.jointMeasure)).symm.trans hc
  obtain ⟨ω,hω⟩ := he.exists
  exact hk hω.symm

end OperatorDerivativeRewrite.Foundation.IBMNativeClockDirection
