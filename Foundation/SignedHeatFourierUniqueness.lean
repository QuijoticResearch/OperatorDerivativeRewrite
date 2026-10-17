import Foundation.SignedDensityIntegral
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! Fourier characters determine actual finite signed measures on the real line. -/
noncomputable section
open MeasureTheory
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.SignedHeatFourierUniqueness
open HigherHeatCylinderFourier SignedDensityIntegral

theorem positive_ext (P Q : Measure ℝ) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (h : ∀ ξ, (∫ x, phase ξ x ∂P) = ∫ x, phase ξ x ∂Q) : P = Q := by
  have hs : ∀ x : ℝ, x ≠ 0 → (LinearMap.mul ℝ ℝ) x ≠ 0 := by
    intro x hx he
    have hh := congrArg (fun L : ℝ →ₗ[ℝ] ℝ => L 1) he
    exact hx (by simpa using hh)
  have hc : Continuous (fun p : ℝ × ℝ => ((LinearMap.mul ℝ ℝ) p.1) p.2) :=
    continuous_fst.mul continuous_snd
  apply ext_of_integral_char_eq Real.continuous_fourierChar Real.fourierChar_ne_one hs hc
  intro ξ
  change (∫ x, (Real.fourierChar (x * ξ) : ℂ) ∂P) =
    ∫ x, (Real.fourierChar (x * ξ) : ℂ) ∂Q
  simpa only [phase, mul_neg, neg_neg] using h (-ξ)

theorem jordan_integral (μ : SignedMeasure ℝ) (ξ : ℝ) :
    (∫ᵛ x, phase ξ x ∂<•μ) =
      (∫ x, phase ξ x ∂μ.toJordanDecomposition.posPart) -
        ∫ x, phase ξ x ∂μ.toJordanDecomposition.negPart := by
  conv_lhs => rw [← μ.toSignedMeasure_toJordanDecomposition]
  rw [JordanDecomposition.toSignedMeasure]
  rw [VectorMeasure.integral_sub_vectorMeasure
    (bounded_signed_integrable _ _ (phase_continuous ξ).measurable 1 (fun x => (phase_norm ξ x).le))
    (bounded_signed_integrable _ _ (phase_continuous ξ).measurable 1 (fun x => (phase_norm ξ x).le))]
  simp only [VectorMeasure.integral_toSignedMeasure]

theorem eq_zero (μ : SignedMeasure ℝ) (h : ∀ ξ, (∫ᵛ x, phase ξ x ∂<•μ) = 0) : μ = 0 := by
  have hp : μ.toJordanDecomposition.posPart = μ.toJordanDecomposition.negPart := by
    apply positive_ext
    intro ξ
    have hh := h ξ
    rw [jordan_integral, sub_eq_zero] at hh
    exact hh
  rw [← μ.toSignedMeasure_toJordanDecomposition, JordanDecomposition.toSignedMeasure]
  simp only [hp, sub_self]

theorem ext (μ ν : SignedMeasure ℝ)
    (h : ∀ ξ, (∫ᵛ x, phase ξ x ∂<•μ) = ∫ᵛ x, phase ξ x ∂<•ν) : μ = ν := by
  have hz : μ - ν = 0 := by
    apply eq_zero
    intro ξ
    rw [VectorMeasure.integral_sub_vectorMeasure
      (bounded_signed_integrable _ _ (phase_continuous ξ).measurable 1 (fun x => (phase_norm ξ x).le))
      (bounded_signed_integrable _ _ (phase_continuous ξ).measurable 1 (fun x => (phase_norm ξ x).le)),
      h ξ, sub_self]
  exact sub_eq_zero.mp hz

end OperatorDerivativeRewrite.Foundation.SignedHeatFourierUniqueness
