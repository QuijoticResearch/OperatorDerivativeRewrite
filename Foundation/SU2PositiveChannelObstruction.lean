import Foundation.SU2CoupledLoopResponse
/-! Positive one-loop character response with zero connected two-loop covariance. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open OperatorDerivativeRewrite.Foundation.QuaternionSU2Representation
open OperatorDerivativeRewrite.Foundation.BoundedExponentialTiltResponse
open OperatorDerivativeRewrite.Foundation.SU2OneWordTransfer
open OperatorDerivativeRewrite.Foundation.SU2TwoLoopJointLaw
namespace OperatorDerivativeRewrite.Foundation.SU2PositiveChannelObstruction

def loopLaw (A : SU2) (β : ℝ) : Measure (SU2 × SU2) :=
  (transition law β A ⊗ₘ transition law β).map
    (fun p : SU2 × SU2 => (A * p.1, p.1 * p.2))

def marginalMean (β : ℝ) : ℝ :=
  ∫ C, halfTrace C ∂tiltedMeasure law halfTrace β

theorem marginalMean_pos_near_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ β, 0 < β ∧ β < ε ∧ 0 < marginalMean β := by
  obtain ⟨β, hβ, hβε, hm⟩ := positive_identity_mean_near_zero law ε hε
  refine ⟨β, hβ, hβε, ?_⟩
  rw [transition_identity_law] at hm
  exact hm

theorem pair_moment_factor (A : SU2) (β : ℝ) :
    (∫ p, halfTrace p.1 * halfTrace p.2 ∂loopLaw A β) =
      marginalMean β * marginalMean β := by
  letI : IsProbabilityMeasure (tiltedMeasure law halfTrace β) :=
    tiltedMeasure_probability law halfTrace halfTrace_measurable halfTrace_bound β
  rw [loopLaw, two_loop_joint_law]
  exact integral_prod_mul halfTrace halfTrace

theorem first_mean_eq (A : SU2) (β : ℝ) :
    (∫ p, halfTrace p.1 ∂loopLaw A β) = marginalMean β := by
  letI : IsProbabilityMeasure (tiltedMeasure law halfTrace β) :=
    tiltedMeasure_probability law halfTrace halfTrace_measurable halfTrace_bound β
  rw [loopLaw, two_loop_joint_law]
  have h := integral_prod_mul (μ := tiltedMeasure law halfTrace β)
    (ν := tiltedMeasure law halfTrace β) halfTrace (fun _ : SU2 => (1 : ℝ))
  simpa [marginalMean] using h

theorem second_mean_eq (A : SU2) (β : ℝ) :
    (∫ p, halfTrace p.2 ∂loopLaw A β) = marginalMean β := by
  letI : IsProbabilityMeasure (tiltedMeasure law halfTrace β) :=
    tiltedMeasure_probability law halfTrace halfTrace_measurable halfTrace_bound β
  rw [loopLaw, two_loop_joint_law]
  have h := integral_prod_mul (μ := tiltedMeasure law halfTrace β)
    (ν := tiltedMeasure law halfTrace β) (fun _ : SU2 => (1 : ℝ)) halfTrace
  simpa [marginalMean] using h
theorem connected_zero (A : SU2) (β : ℝ) :
    (∫ p, halfTrace p.1 * halfTrace p.2 ∂loopLaw A β) -
      (∫ p, halfTrace p.1 ∂loopLaw A β) *
      (∫ p, halfTrace p.2 ∂loopLaw A β) = 0 := by
  rw [pair_moment_factor, first_mean_eq, second_mean_eq]
  ring
theorem positive_channel_zero_connected (A : SU2) (ε : ℝ) (hε : 0 < ε) :
    ∃ β, 0 < β ∧ β < ε ∧ 0 < marginalMean β ∧
      (∫ p, halfTrace p.1 * halfTrace p.2 ∂loopLaw A β) -
        (∫ p, halfTrace p.1 ∂loopLaw A β) *
        (∫ p, halfTrace p.2 ∂loopLaw A β) = 0 := by
  obtain ⟨β, hβ, hβε, hm⟩ := marginalMean_pos_near_zero ε hε
  exact ⟨β, hβ, hβε, hm, connected_zero A β⟩
end OperatorDerivativeRewrite.Foundation.SU2PositiveChannelObstruction
