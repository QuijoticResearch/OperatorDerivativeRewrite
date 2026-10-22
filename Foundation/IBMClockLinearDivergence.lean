import Foundation.IBMObservableClockKernel
import Foundation.GaussianQuadraticSourceHodge
import Foundation.IBMEvenClockProjection

/-! Actual non-observable linear clock fields with quadratic intrinsic divergence. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockLinearDivergence
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMFiniteAverageCore IBMIntrinsicChainRule GaussianQuadraticSourceHodge
open IBMClockConditionalCorrection IBMNativeClockDirection
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
set_option backward.isDefEq.respectTransparency false

def linearFiber (a b : CoefficientSpace) : FieldSpace :=
  BochnerClosedOperator.tensor gaussianProduct gaussianOne (scalarTensor a (firstChaosEmbedding b))

def quadraticFiber (a b : CoefficientSpace) : ScalarFieldSpace :=
  BochnerClosedOperator.tensor gaussianProduct gaussianOne (mixedTarget a b)

theorem partial_graph (a b : CoefficientSpace) :
    (linearFiber a b,quadraticFiber a b) ∈ partialDerivative.adjoint.graph :=
  LinearPMap.le_graph_of_le
    (BochnerLiftAdjointInclusion.lift_adjoint_le gaussianProduct closedCylindricalDerivative
      closedCylindricalDerivative_dense_domain)
    (BochnerClosedOperator.tensor_graph gaussianProduct hilbertDivergence gaussianOne _ _
      (mixed_divergence_graph a b))

theorem partial_mem (a b : CoefficientSpace) : linearFiber a b ∈ partialDerivative.adjoint.domain :=
  LinearPMap.mem_domain_of_mem_graph (partial_graph a b)

theorem partial_value (a b : CoefficientSpace) :
    partialDerivative.adjoint ⟨linearFiber a b,partial_mem a b⟩ = quadraticFiber a b :=
  ((partialDerivative.adjoint.image_iff (partial_mem a b)).mpr (partial_graph a b)).symm

def nativeField (a b : CoefficientSpace) : JointFieldSpace := pairField 0 (linearFiber a b)

def output (a b : CoefficientSpace) : IntrinsicSpace :=
  IntrinsicSpace.orthogonalProjectionOnto (clockLift (mixedTarget a b))

theorem native_graph (a b : CoefficientSpace) :
    (nativeField a b,output a b) ∈ jointDivergence.graph := by
  have hc : linearFiber a b ∈ clockDerivative.adjoint.domain := by
    rw [clock_adjoint_domain]
    exact partial_mem a b
  obtain ⟨hp,hv⟩ := ambient_pair_divergence 0 ⟨linearFiber a b,hc⟩
  have he := (clock_adjoint_apply _ hc (partial_mem a b)).trans
    ((congrArg clockUnitary.symm (partial_value a b)).trans (inverse_clock_tensor _))
  have hs : sourceDerivative.adjoint (0 : sourceDerivative.adjoint.domain) = 0 :=
    sourceDerivative.adjoint.map_zero
  have hv' : jointDivergence ⟨nativeField a b,hp⟩ =
      IntrinsicSpace.orthogonalProjectionOnto
        (sourceDerivative.adjoint 0 + clockDerivative.adjoint ⟨linearFiber a b,hc⟩) := hv
  have ho : jointDivergence ⟨nativeField a b,hp⟩ = output a b :=
    hv'.trans (by rw [hs,zero_add,he]; rfl)
  exact jointDivergence.mem_graph_iff.mpr ⟨⟨_,hp⟩,rfl,ho⟩

theorem native_mem (a b : CoefficientSpace) : nativeField a b ∈ jointDivergence.domain :=
  LinearPMap.mem_domain_of_mem_graph (native_graph a b)

theorem native_value (a b : CoefficientSpace) :
    jointDivergence ⟨nativeField a b,native_mem a b⟩ = output a b :=
  ((jointDivergence.image_iff (native_mem a b)).mpr (native_graph a b)).symm

theorem field_ae (a b : CoefficientSpace) :
    uncurryField (nativeField a b 1) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => firstChaosEmbedding b ω.2 • a := by
  have he : uncurryField (linearFiber a b) =
      ProductL2Curry.productTensor gaussianProduct gaussianProduct gaussianOne
        (scalarTensor a (firstChaosEmbedding b)) := by
    apply (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct (E := CoefficientSpace)).injective
    rw [uncurryField,LinearIsometryEquiv.apply_symm_apply]
    exact (ProductL2Curry.curry_productTensor gaussianProduct gaussianProduct _ _).symm
  change uncurryField (linearFiber a b) =ᵐ[_] _
  rw [he]
  have ho := (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
    gaussianOne_coeFn
  have hs := (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
    (scalarTensor_coeFn a (firstChaosEmbedding b))
  filter_upwards [ProductL2Curry.productTensor_coeFn gaussianProduct gaussianProduct gaussianOne
    (scalarTensor a (firstChaosEmbedding b)),ho,hs] with ω ht ho hs
  change gaussianOne ω.1 = 1 at ho
  change scalarTensor a (firstChaosEmbedding b) ω.2 = firstChaosEmbedding b ω.2 • a at hs
  rw [ht,ho,one_smul,hs]

theorem diagonal_mixed_eq (h : CoefficientSpace) :
    mixedTarget h h = (GaussianTimeSpaceHermite.wick h 2 : GaussianL2) := by
  apply Lp.ext
  filter_upwards [mixedTarget_coeFn h h,GaussianTimeSpaceHermite.core_coeFn h (‖h‖^2) 2]
    with ω hm hw
  rw [hm,real_inner_self_eq_norm_sq]
  change _ = (GaussianTimeSpaceHermite.core h (‖h‖^2) 2 : GaussianL2) ω
  rw [hw,GaussianTimeSpaceHermite.value_two]
  ring

attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable

def timeDirection (t : ℝ≥0) : CoefficientSpace :=
  SeparableHilbertEmbedding.hilbertEmbedding GaussianTimeHilbert.TimeHilbert (GaussianTimeHilbert.timeVector t)

theorem time_output (t : ℝ≥0) : output (timeDirection t) (timeDirection t) =
    IntrinsicSpace.orthogonalProjectionOnto (IBMEvenClockProjection.clockQuadratic t) := by
  exact congrArg (fun q : GaussianL2 => IntrinsicSpace.orthogonalProjectionOnto (clockLift q))
    (diagonal_mixed_eq (timeDirection t))

theorem projected_quadratic_pairing (t : ℝ≥0) :
    inner ℝ (output (timeDirection t) (timeDirection t) : IntrinsicSpace)
      ⟨IBMActualQuarticMoment.fourthClass t,
        IBMPastCoreDensity.past_le_intrinsic t (IBMActualQuarticMoment.fourthClass_mem_past le_rfl)⟩ =
      6*(t : ℝ)^2 := by
  rw [time_output]
  exact (IntrinsicSpace.inner_orthogonalProjectionOnto_eq_of_mem_right
    ⟨_,IBMPastCoreDensity.past_le_intrinsic t (IBMActualQuarticMoment.fourthClass_mem_past le_rfl)⟩
    (IBMEvenClockProjection.clockQuadratic t)).trans (IBMEvenClockProjection.quadratic_fourth_pairing t)

theorem output_ne_zero (t : ℝ≥0) (ht : 0 < t) : output (timeDirection t) (timeDirection t) ≠ 0 := by
  intro hz
  have hp := projected_quadratic_pairing t
  rw [hz,inner_zero_left] at hp
  have hn : 0 < 6*(t : ℝ)^2 := mul_pos (by norm_num) (sq_pos_of_pos ht)
  linarith

theorem time_field_ae (t : ℝ≥0) :
    uncurryField (nativeField (timeDirection t) (timeDirection t) 1)
      =ᵐ[IBMSourceLaws.jointMeasure]
        fun ω => IBMConstructedSources.clockPath ω.2 t • timeDirection t := by
  have ht : (fun ω => IBMConstructedSources.clockPath ω.2 t) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => firstChaosEmbedding (timeDirection t) ω.2 :=
    (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
      (IBMConstructedSources.clockPath_coordinate_ae t)
  exact (field_ae _ _).trans ((ht.symm).mono fun ω hω => congrArg (fun z : ℝ => z • timeDirection t) hω)

theorem not_observable_weight (t : ℝ≥0) (ht : 0 < t) (k : CoefficientSpace) :
    ¬ ∃ F : IntrinsicSpace,
      nativeField (timeDirection t) (timeDirection t) = IBMNativeDirectionalMaps.lift 0 k (F : JointL2) := by
  rintro ⟨F,hF⟩
  have he : (⟨nativeField (timeDirection t) (timeDirection t),native_mem _ _⟩ : jointDivergence.domain) =
      ⟨IBMNativeDirectionalMaps.lift 0 k (F : JointL2),IBMObservableClockKernel.observable_clock_mem k F⟩ :=
    Subtype.ext hF
  have hz : output (timeDirection t) (timeDirection t) = 0 :=
    (native_value _ _).symm.trans ((congrArg jointDivergence he).trans
      (IBMObservableClockKernel.observable_clock_value k F))
  exact output_ne_zero t ht hz

end OperatorDerivativeRewrite.Foundation.IBMClockLinearDivergence
