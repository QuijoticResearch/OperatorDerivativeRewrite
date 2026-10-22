import Foundation.IBMNativeIntegrableDivergence
import Foundation.GaussianFirstChaosRecovery
import Foundation.BochnerLiftAdjointInclusion

/-! Concrete deterministic native fields in the actual IBM divergence domain. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNativeDeterministicFields
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMIntrinsicChainRule IBMIntrinsicChainEnergy
open IBMFiniteAverageCore
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
set_option backward.isDefEq.respectTransparency false

def directionField (h : CoefficientSpace) : FieldSpace :=
  BochnerClosedOperator.tensor gaussianProduct gaussianOne (scalarTensor h gaussianOne)

theorem direction_partial_mem (h : CoefficientSpace) :
    directionField h ∈ partialDerivative.adjoint.domain := by
  have hg := BochnerClosedOperator.tensor_graph gaussianProduct hilbertDivergence
    gaussianOne _ _ (GaussianFirstChaosRecovery.firstChaos_divergence_graph h)
  have hi := LinearPMap.le_graph_of_le
    (BochnerLiftAdjointInclusion.lift_adjoint_le gaussianProduct closedCylindricalDerivative
      closedCylindricalDerivative_dense_domain) hg
  exact LinearPMap.mem_domain_of_mem_graph hi

def constantVector (h : CoefficientSpace) : JointVectorL2 :=
  (memLp_const h : MemLp (fun _ : IBMSourceLaws.JointSample => h)
    2 IBMSourceLaws.jointMeasure).toLp _

theorem constantVector_ae (h : CoefficientSpace) :
    constantVector h =ᵐ[IBMSourceLaws.jointMeasure] fun _ => h := MemLp.coeFn_toLp _

theorem curry_constant (h : CoefficientSpace) :
    ProductL2Curry.curryEquiv gaussianProduct gaussianProduct (constantVector h) =
      directionField h := by
  have hi : scalarTensor h gaussianOne =ᵐ[gaussianProduct] fun _ => h := by
    filter_upwards [scalarTensor_coeFn h gaussianOne,gaussianOne_coeFn] with y hs ho
    rw [hs,ho,one_smul]
  apply Lp.ext
  filter_upwards [ProductL2Curry.curry_coeFn gaussianProduct gaussianProduct (constantVector h),
    ae_ae_of_ae_prod (constantVector_ae h),
    BochnerClosedOperator.tensor_coeFn gaussianProduct gaussianOne (scalarTensor h gaussianOne),
    gaussianOne_coeFn] with x hc hv ht ho
  have he : directionField h x = scalarTensor h gaussianOne := by
    change BochnerClosedOperator.tensor gaussianProduct gaussianOne (scalarTensor h gaussianOne) x = _
    rw [ht,ho,one_smul]
  rw [he]
  apply Lp.ext
  exact (hc.trans hv).trans hi.symm

theorem uncurry_direction (h : CoefficientSpace) :
    uncurryField (directionField h) = constantVector h := by
  rw [← curry_constant h]
  exact (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm_apply_apply _

theorem source_direction_ae (h : CoefficientSpace) :
    sourceField (directionField h) =ᵐ[IBMSourceLaws.jointMeasure] fun _ => h := by
  have ht := (measurePreserving_swap (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
    (constantVector_ae h)
  change vectorSwap (uncurryField (directionField h)) =ᵐ[_] _
  rw [uncurry_direction]
  exact (vectorSwap_ae _).trans ht

def nativeField (h k : CoefficientSpace) : JointFieldSpace :=
  pairField (directionField h) (directionField k)

theorem native_mem (h k : CoefficientSpace) : nativeField h k ∈ jointDivergence.domain := by
  have hs : directionField h ∈ sourceDerivative.adjoint.domain := by
    rw [source_adjoint_domain]
    exact direction_partial_mem h
  have hc : directionField k ∈ clockDerivative.adjoint.domain := by
    rw [clock_adjoint_domain]
    exact direction_partial_mem k
  exact (ambient_pair_divergence ⟨directionField h,hs⟩ ⟨directionField k,hc⟩).choose

theorem native_coordinates (h k : CoefficientSpace) (i : Fin 2) :
    IBMNativeFieldMultiplier.coordinate i (nativeField h k i)
      =ᵐ[IBMSourceLaws.jointMeasure] fun _ => if i = 0 then h else k := by
  fin_cases i
  · exact source_direction_ae h
  · change uncurryField (directionField k) =ᵐ[_] fun _ => k
    rw [uncurry_direction]
    exact constantVector_ae k

theorem native_bounded (h k : CoefficientSpace) (i : Fin 2) :
    MemLp (IBMNativeFieldMultiplier.coordinate i (nativeField h k i) :
      IBMSourceLaws.JointSample → CoefficientSpace) ∞ IBMSourceLaws.jointMeasure :=
  (memLp_congr_ae (native_coordinates h k i)).mpr (memLp_const _)

theorem native_source_ne_zero (h k : CoefficientSpace) (hh : h ≠ 0) :
    nativeField h k ≠ 0 := by
  intro hz
  have hc := native_coordinates h k 0
  rw [hz] at hc
  simp only [PiLp.zero_apply,map_zero,ite_true] at hc
  have he : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, (0 : CoefficientSpace) = h :=
    (Lp.coeFn_zero (E := CoefficientSpace) (p := 2) (μ := IBMSourceLaws.jointMeasure)).symm.trans hc
  obtain ⟨ω,hω⟩ := he.exists
  exact hh hω.symm

def directionElement (h k : CoefficientSpace) : jointDivergence.domain :=
  ⟨nativeField h k,native_mem h k⟩

theorem direction_correction_mem (f : jointDerivative.domain) (h k : CoefficientSpace) :
    MemLp (IBMNativeContractionDomain.pairingFunction (jointDerivative f) (nativeField h k))
      2 IBMSourceLaws.jointMeasure :=
  IBMNativeContractionDomain.bounded_field_domain _ _ (native_bounded h k)

theorem weighted_direction_mem (f : jointDerivative.domain) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((f : IntrinsicSpace) : JointL2) ω)| ≤ C)
    (h k : CoefficientSpace) :
    IBMNativeFieldMultiplier.multiply ((f : IntrinsicSpace) : JointL2)
      (IBMNativeProductOperators.bounded_memLp f C hf) (nativeField h k) ∈ jointDivergence.domain :=
  IBMNativeIntegrableDivergence.weighted_mem f C hC hf (directionElement h k)
    (direction_correction_mem f h k)

theorem weighted_direction_value (f : jointDerivative.domain) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((f : IntrinsicSpace) : JointL2) ω)| ≤ C)
    (h k : CoefficientSpace) :
    jointDivergence ⟨IBMNativeFieldMultiplier.multiply ((f : IntrinsicSpace) : JointL2)
      (IBMNativeProductOperators.bounded_memLp f C hf) (nativeField h k),
      weighted_direction_mem f C hC hf h k⟩ =
        IBMNativeIntegrableDivergence.output f (IBMNativeProductOperators.bounded_memLp f C hf)
          (directionElement h k) (direction_correction_mem f h k) :=
  IBMNativeIntegrableDivergence.weighted_value f C hC hf (directionElement h k)
    (direction_correction_mem f h k)

end OperatorDerivativeRewrite.Foundation.IBMNativeDeterministicFields
