import Foundation.SU2OneWordTransfer

/-! Exact opposite central-input response for the actual one-word SU(2) transfer. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.SU2OneWordBoundaryInfluence
open QuaternionSU2Representation SU2TraceHessianModel
theorem minus_exponent (β : ℝ) (B : SU2) :
    SU2StapleKernel.exponent (Finset.univ : Finset Unit) β
      (SU2OneWordTransfer.word SU2StapleExtremes.minusOne) B =
      -β * halfTrace B := by
  simp [SU2StapleKernel.exponent, SU2StaplePolar.staple,
    SU2OneWordTransfer.word, SU2StapleExtremes.minusOne,
    QuaternionSU2Representation.hom, QuaternionSU2Representation.repr,
    halfTrace]
  simp [traceReal, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem minus_law (β : ℝ) :
    SU2OneWordTransfer.transition law β SU2StapleExtremes.minusOne =
      BoundedExponentialTiltResponse.tiltedMeasure law halfTrace (-β) := by
  change SU2StapleKernel.kernel law (Finset.univ : Finset Unit) β
    (SU2OneWordTransfer.word SU2StapleExtremes.minusOne) = _
  rw [SU2StapleKernel.kernel,
    MeasurableExponentialKernel.kernel_apply law _
      (SU2StapleKernel.exponent_measurable (Finset.univ : Finset Unit) β)]
  unfold BoundedExponentialTiltResponse.tiltedMeasure
  congr 1
  funext B
  simp only [MeasurableExponentialKernel.density,
    BoundedExponentialTiltResponse.density,
    MeasurableExponentialKernel.partition,
    BoundedExponentialTiltResponse.partition,
    BoundedExponentialTiltResponse.weighted, one_mul]
  simp_rw [minus_exponent]

theorem minus_mean_hasDerivAt_zero : HasDerivAt
    (fun β : ℝ => ∫ B, halfTrace B ∂(SU2OneWordTransfer.transition law β
      SU2StapleExtremes.minusOne)) (-1/4) 0 := by
  have hEq (β : ℝ) :
      (∫ B, halfTrace B ∂(SU2OneWordTransfer.transition law β
        SU2StapleExtremes.minusOne)) =
      BoundedExponentialTiltResponse.expectation law halfTrace halfTrace (-β) := by
    rw [minus_law]
    exact BoundedExponentialTiltResponse.tilted_integral law halfTrace halfTrace
      halfTrace_measurable halfTrace_bound (-β)
  have hd := BoundedExponentialTiltResponse.expectation_hasDerivAt_zero law
    halfTrace halfTrace halfTrace_measurable halfTrace_measurable halfTrace_bound
    1 (by norm_num) halfTrace_bound
  obtain ⟨h1, h2, _, _, _⟩ := SU2TiltEnergyResponse.moment_values law
  have hmul : (∫ B, halfTrace B * halfTrace B ∂law) = (1/4 : ℝ) := by
    convert h2 using 1
    apply integral_congr_ae
    filter_upwards with B
    ring
  rw [hmul, h1] at hd
  norm_num at hd
  have hd' : HasDerivAt (BoundedExponentialTiltResponse.expectation law halfTrace halfTrace) (1/4) (-(0:ℝ)) := by simpa using hd
  have hc := hd'.comp 0 (hasDerivAt_neg (0 : ℝ))
  simp_rw [hEq]
  change HasDerivAt (BoundedExponentialTiltResponse.expectation law halfTrace halfTrace ∘ Neg.neg) (-1/4) 0
  convert hc using 1
  norm_num

theorem boundary_mean_separation_near_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ β, 0 < β ∧ β < ε ∧
      (∫ B, halfTrace B ∂(SU2OneWordTransfer.transition law β
        SU2StapleExtremes.minusOne)) <
      (∫ B, halfTrace B ∂(SU2OneWordTransfer.transition law β (1 : SU2))) := by
  let plusMean : ℝ → ℝ := fun β =>
    ∫ B, halfTrace B ∂(SU2OneWordTransfer.transition law β (1 : SU2))
  let minusMean : ℝ → ℝ := fun β =>
    ∫ B, halfTrace B ∂(SU2OneWordTransfer.transition law β SU2StapleExtremes.minusOne)
  have hd : HasDerivAt (fun β => plusMean β - minusMean β) (1/2) 0 := by
    convert (SU2OneWordTransfer.identity_mean_hasDerivAt_zero law).sub minus_mean_hasDerivAt_zero
      using 1
    norm_num
  have hz1 : plusMean 0 = 0 := by
    change (∫ B, halfTrace B ∂(SU2OneWordTransfer.transition law 0 (1 : SU2))) = 0
    rw [SU2OneWordTransfer.transition_zero]
    exact (SU2TiltEnergyResponse.moment_values law).1
  have hz2 : minusMean 0 = 0 := by
    change (∫ B, halfTrace B ∂(SU2OneWordTransfer.transition law 0
      SU2StapleExtremes.minusOne)) = 0
    rw [SU2OneWordTransfer.transition_zero]
    exact (SU2TiltEnergyResponse.moment_values law).1
  obtain ⟨β, hβ, hβε, hinc⟩ :=
    BoundedExponentialTiltResponse.positive_derivative_arbitrarily_small_increase
      (fun β => plusMean β - minusMean β) (1/2) hd (by norm_num) ε hε
  rw [hz1, hz2] at hinc
  refine ⟨β, hβ, hβε, ?_⟩
  change minusMean β < plusMean β
  linarith
end OperatorDerivativeRewrite.Foundation.SU2OneWordBoundaryInfluence
