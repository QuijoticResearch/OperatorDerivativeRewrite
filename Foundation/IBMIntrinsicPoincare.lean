import Foundation.IBMNativeRecoveryContraction
import Foundation.IBMCenteredSourceRepresentation

/-! Constant-one Poincare control and the exact kernel of the ORIGINAL intrinsic derivative. -/
noncomputable section
open MeasureTheory Set
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicPoincare
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative IBMPredictableIntegralObservable
open IBMStochasticNativeDivergence IBMNativeRecoveryContraction
open IBMCenteredSourceRepresentation (intrinsicOne joint_one_graph)
set_option backward.isDefEq.respectTransparency false
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

theorem jointOne_eq_old_one : jointOne = IBMGlobalVacuum.one :=
  Lp.ext (jointOne_ae.trans IBMGlobalVacuum.one_coeFn.symm)

theorem one_pairing : inner ℝ jointOne (intrinsicOne : JointL2) = 1 := by
  rw [jointOne_eq_old_one]
  change inner ℝ IBMGlobalVacuum.one IBMGlobalVacuum.one = 1
  rw [IBMGlobalVacuum.one_inner_mean, integral_congr_ae IBMGlobalVacuum.one_coeFn]
  simp

def oneElement : jointDerivative.domain :=
  ⟨intrinsicOne, LinearPMap.mem_domain_of_mem_graph joint_one_graph⟩

theorem one_derivative : jointDerivative oneElement = 0 :=
  ((jointDerivative.image_iff oneElement.property).mpr joint_one_graph).symm

theorem centered_recovery_duality (f : IntrinsicSpace)
    (hf : inner ℝ jointOne (f : JointL2) = 0) (g : jointDerivative.domain) :
    inner ℝ f (g : IntrinsicSpace) =
      inner ℝ (IBMNativeGaussianRecovery.recoveryPair (f : JointL2)) (jointDerivative g) := by
  have h := centered_observable_recovery f hf
  let u : jointDivergence.domain := ⟨IBMNativeGaussianRecovery.recoveryPair (f : JointL2), h.choose⟩
  have hv : jointDivergence u = f := h.choose_spec
  calc
    inner ℝ f (g : IntrinsicSpace) = inner ℝ (jointDivergence u) (g : IntrinsicSpace) :=
      congrArg (fun v : IntrinsicSpace => inner ℝ v (g : IntrinsicSpace)) hv.symm
    _ = _ := jointDerivative.adjoint_isFormalAdjoint jointDerivative_dense u g

theorem centered_poincare (f : jointDerivative.domain)
    (hf : inner ℝ jointOne ((f : IntrinsicSpace) : JointL2) = 0) :
    ‖(f : IntrinsicSpace)‖ ≤ ‖jointDerivative f‖ := by
  have hi := centered_recovery_duality (f : IntrinsicSpace) hf f
  rw [real_inner_self_eq_norm_sq] at hi
  have hb := real_inner_le_norm (IBMNativeGaussianRecovery.recoveryPair ((f : IntrinsicSpace) : JointL2))
    (jointDerivative f)
  have hr := recovery_contraction ((f : IntrinsicSpace) : JointL2)
  have hn : ‖(f : IntrinsicSpace)‖ ^ 2 ≤ ‖(f : IntrinsicSpace)‖ * ‖jointDerivative f‖ := by
    rw [hi]
    exact hb.trans (mul_le_mul_of_nonneg_right hr (norm_nonneg _))
  by_cases hz : ‖(f : IntrinsicSpace)‖ = 0
  · rw [hz]
    exact norm_nonneg _
  · have hp := lt_of_le_of_ne (norm_nonneg (f : IntrinsicSpace)) (Ne.symm hz)
    nlinarith

def mean (f : IntrinsicSpace) : ℝ := inner ℝ jointOne (f : JointL2)

theorem full_poincare (f : jointDerivative.domain) :
    ‖(f : IntrinsicSpace) - mean (f : IntrinsicSpace) • intrinsicOne‖ ≤ ‖jointDerivative f‖ := by
  let c := mean (f : IntrinsicSpace)
  let g : jointDerivative.domain := f - c • oneElement
  have hg : inner ℝ jointOne ((g : IntrinsicSpace) : JointL2) = 0 := by
    change inner ℝ jointOne
      (((f : IntrinsicSpace) : JointL2) - c • (intrinsicOne : JointL2)) = 0
    rw [inner_sub_right, real_inner_smul_right, one_pairing, mul_one]
    exact sub_self _
  have hd : jointDerivative g = jointDerivative f := by
    change jointDerivative (f-c • oneElement) = _
    rw [jointDerivative.map_sub, jointDerivative.map_smul, one_derivative, smul_zero, sub_zero]
  have h := centered_poincare g hg
  rw [hd] at h
  exact h

theorem kernel_iff_constant (f : jointDerivative.domain) :
    jointDerivative f = 0 ↔ (f : IntrinsicSpace) = mean (f : IntrinsicSpace) • intrinsicOne := by
  constructor
  · intro hzero
    have h := full_poincare f
    rw [hzero, norm_zero] at h
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
  · intro hf
    have he : f = mean (f : IntrinsicSpace) • oneElement := Subtype.ext hf
    rw [he, jointDerivative.map_smul, one_derivative, smul_zero]

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicPoincare
