import Foundation.SU2GaugeCovariantTransfer
/-! Exact two-step closed-product event factorization for the actual one-word SU(2) kernel. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open OperatorDerivativeRewrite.Foundation.QuaternionSU2Representation
open OperatorDerivativeRewrite.Foundation.SU2ClosedLoopTransfer
namespace OperatorDerivativeRewrite.Foundation.SU2TwoLoopChain

private theorem section_eq (B : SU2) (β : ℝ) (t : Set SU2) (ht : MeasurableSet t) :
    (SU2OneWordTransfer.transition law β B) {D | B * D ∈ t} =
      (BoundedExponentialTiltResponse.tiltedMeasure law halfTrace β) t := by
  have h := congrArg (fun m : Measure SU2 => m t) (closedLoop_law B β)
  rw [Measure.map_apply (measurable_const_mul B) ht] at h
  exact h

private theorem first_eq (A : SU2) (β : ℝ) (s : Set SU2) (hs : MeasurableSet s) :
    (SU2OneWordTransfer.transition law β A) {B | A * B ∈ s} =
      (BoundedExponentialTiltResponse.tiltedMeasure law halfTrace β) s :=
  section_eq A β s hs

/-- Consecutive closed-product events factor under two actual one-word updates. -/
theorem two_loop_rectangle (A : SU2) (β : ℝ) (s t : Set SU2)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (∫⁻ B in {B | A * B ∈ s},
      (SU2OneWordTransfer.transition law β B) {D | B * D ∈ t}
      ∂SU2OneWordTransfer.transition law β A) =
      (BoundedExponentialTiltResponse.tiltedMeasure law halfTrace β) s *
      (BoundedExponentialTiltResponse.tiltedMeasure law halfTrace β) t := by
  simp_rw [show ∀ B : SU2, (SU2OneWordTransfer.transition law β B) {D | B * D ∈ t} =
    (BoundedExponentialTiltResponse.tiltedMeasure law halfTrace β) t from
    fun B => section_eq B β t ht]
  rw [lintegral_const]
  rw [Measure.restrict_apply_univ, first_eq A β s hs]
  ring
end OperatorDerivativeRewrite.Foundation.SU2TwoLoopChain
