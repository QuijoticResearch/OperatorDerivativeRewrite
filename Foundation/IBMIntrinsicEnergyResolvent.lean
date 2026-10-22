import Foundation.IBMIntrinsicPoincare
import Foundation.ClosedOperatorEnergyResolvent

/-! The actual intrinsic energy resolvent preserves mean and halves centered norms. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicEnergyResolvent
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative IBMIntrinsicPoincare
open IBMCenteredSourceRepresentation (intrinsicOne)
set_option backward.isDefEq.respectTransparency false
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

def resolvent : IntrinsicSpace →L[ℝ] IntrinsicSpace :=
  ClosedOperatorEnergyResolvent.resolvent jointDerivative jointDerivative_closed

def gradient : IntrinsicSpace →L[ℝ] JointFieldSpace :=
  ClosedOperatorEnergyResolvent.gradient jointDerivative jointDerivative_closed

theorem resolvent_mem (x : IntrinsicSpace) : resolvent x ∈ jointDerivative.domain :=
  ClosedOperatorEnergyResolvent.resolvent_mem_domain _ _ x

theorem derivative_resolvent (x : IntrinsicSpace) :
    jointDerivative ⟨resolvent x, resolvent_mem x⟩ = gradient x :=
  ClosedOperatorEnergyResolvent.derivative_resolvent _ _ x

theorem gradient_mem (x : IntrinsicSpace) : gradient x ∈ jointDivergence.domain :=
  ClosedOperatorEnergyResolvent.gradient_mem_adjoint _ _ x

theorem divergence_gradient (x : IntrinsicSpace) :
    jointDivergence ⟨gradient x, gradient_mem x⟩ = x-resolvent x :=
  ClosedOperatorEnergyResolvent.adjoint_gradient _ _ jointDerivative_dense x

theorem mean_pairing (x : IntrinsicSpace) : mean x = inner ℝ intrinsicOne x := by
  rw [mean, jointOne_eq_old_one]
  rfl

theorem resolvent_mean (x : IntrinsicSpace) : mean (resolvent x) = mean x := by
  have h := ClosedOperatorEnergyResolvent.weak_identity jointDerivative jointDerivative_closed x oneElement
  rw [one_derivative, inner_zero_right, add_zero] at h
  change inner ℝ (resolvent x) intrinsicOne = inner ℝ x intrinsicOne at h
  rw [mean_pairing, mean_pairing]
  exact (real_inner_comm (resolvent x) intrinsicOne).trans
    (h.trans (real_inner_comm intrinsicOne x))

theorem centered_half_contraction (x : IntrinsicSpace) (hx : mean x = 0) :
    ‖resolvent x‖ ≤ ‖x‖ / 2 := by
  have hm : mean (resolvent x) = 0 := (resolvent_mean x).trans hx
  have hp := centered_poincare ⟨resolvent x, resolvent_mem x⟩ hm
  rw [derivative_resolvent] at hp
  have he := ClosedOperatorEnergyResolvent.energy_identity jointDerivative jointDerivative_closed x
  change ‖resolvent x‖ ^ 2 + ‖gradient x‖ ^ 2 = inner ℝ x (resolvent x) at he
  have hb := real_inner_le_norm x (resolvent x)
  by_cases hz : ‖resolvent x‖ = 0
  · rw [hz]
    exact div_nonneg (norm_nonneg _) (by norm_num)
  · have hpos := lt_of_le_of_ne (norm_nonneg (resolvent x)) (Ne.symm hz)
    nlinarith [norm_nonneg (gradient x)]

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicEnergyResolvent
