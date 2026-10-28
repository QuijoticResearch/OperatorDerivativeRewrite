import Foundation.SU2OpenLinkGaugeObstruction
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.SU2ClosedLoopTransfer
open QuaternionSU2Representation SU2TraceHessianModel SU2StaplePolar SU2StapleTiltLaw

private theorem singleton_radius (A : SU2) :
    ‖quaternionSum (Finset.univ : Finset Unit) (SU2OneWordTransfer.word A)‖ = 1 := by
  simp [quaternionSum, SU2OneWordTransfer.word,
    CStarRing.norm_of_mem_unitary, recover_mem]

private theorem singleton_orientation (A : SU2) :
    orientation (quaternionSum (Finset.univ : Finset Unit) (SU2OneWordTransfer.word A)) = A := by
  have hp := staple_polar (Finset.univ : Finset Unit) (SU2OneWordTransfer.word A)
  rw [singleton_radius A] at hp
  apply Subtype.ext
  simpa [staple, SU2OneWordTransfer.word] using hp.symm

end OperatorDerivativeRewrite.Foundation.SU2ClosedLoopTransfer

namespace OperatorDerivativeRewrite.Foundation.SU2ClosedLoopTransfer
open MeasureTheory ProbabilityTheory
open QuaternionSU2Representation SU2TraceHessianModel SU2StaplePolar SU2StapleTiltLaw SU2OpenLinkGaugeObstruction

theorem closedLoop_law (A : SU2) (β : ℝ) :
    (SU2OneWordTransfer.transition law β A).map (fun B => A * B) =
      BoundedExponentialTiltResponse.tiltedMeasure law halfTrace β := by
  have h := stapleLaw_map law (Finset.univ : Finset Unit) (SU2OneWordTransfer.word A) β
  rw [singleton_orientation A, concentration, singleton_radius A, mul_one] at h
  rw [SU2OneWordTransfer.transition_section]
  exact h

end OperatorDerivativeRewrite.Foundation.SU2ClosedLoopTransfer

namespace OperatorDerivativeRewrite.Foundation.SU2ClosedLoopTransfer
open MeasureTheory ProbabilityTheory
open QuaternionSU2Representation SU2OpenLinkGaugeObstruction

theorem closedLoop_mean (A : SU2) (β : ℝ) :
    (∫ B, closedPairTrace A B ∂SU2OneWordTransfer.transition law β A) =
      BoundedExponentialTiltResponse.expectation law halfTrace halfTrace β := by
  rw [← BoundedExponentialTiltResponse.tilted_integral law halfTrace halfTrace
    halfTrace_measurable halfTrace_bound β]
  rw [← closedLoop_law A β]
  rw [integral_map (measurable_const_mul A).aemeasurable halfTrace_measurable.aestronglyMeasurable]
  rfl

end OperatorDerivativeRewrite.Foundation.SU2ClosedLoopTransfer

namespace OperatorDerivativeRewrite.Foundation.SU2ClosedLoopTransfer
open MeasureTheory ProbabilityTheory
open QuaternionSU2Representation SU2OpenLinkGaugeObstruction

theorem closedLoop_mean_hasDerivAt_zero (A : SU2) :
    HasDerivAt (fun β : ℝ => ∫ B, closedPairTrace A B ∂SU2OneWordTransfer.transition law β A)
      (1/4) 0 := by
  have hi (β : ℝ) :
      (∫ B, halfTrace B ∂SU2OneWordTransfer.transition law β (1 : SU2)) =
        BoundedExponentialTiltResponse.expectation law halfTrace halfTrace β := by
    rw [SU2OneWordTransfer.transition_identity_law]
    exact BoundedExponentialTiltResponse.tilted_integral law halfTrace halfTrace
      halfTrace_measurable halfTrace_bound β
  have he : (fun β : ℝ => ∫ B, closedPairTrace A B ∂SU2OneWordTransfer.transition law β A) =
      (fun β : ℝ => ∫ B, halfTrace B ∂SU2OneWordTransfer.transition law β (1 : SU2)) := by
    funext β
    rw [closedLoop_mean, hi]
  rw [he]
  exact SU2OneWordTransfer.identity_mean_hasDerivAt_zero law

theorem closedLoop_mean_tendsto_one (A : SU2) :
    Filter.Tendsto (fun β : ℝ => ∫ B, closedPairTrace A B ∂SU2OneWordTransfer.transition law β A)
      Filter.atTop (nhds 1) := by
  have he : (fun β : ℝ => ∫ B, closedPairTrace A B ∂SU2OneWordTransfer.transition law β A) =
    (fun β : ℝ => ∫ B, halfTrace B ∂BoundedExponentialTiltResponse.tiltedMeasure law halfTrace β) := by
    funext β
    rw [closedLoop_mean]
    exact (BoundedExponentialTiltResponse.tilted_integral law halfTrace halfTrace
      halfTrace_measurable halfTrace_bound β).symm
  rw [he]
  exact SU2OneWordLargeCoupling.positive_mean_tendsto_one

end OperatorDerivativeRewrite.Foundation.SU2ClosedLoopTransfer
