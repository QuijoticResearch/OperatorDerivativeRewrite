import Foundation.HigherHeatStepIntegralRealization
import Foundation.HigherHeatSignedPolynomialCalculus

/-! Nontrivial actual deterministic integral laws with vanishing signed second moment. -/
noncomputable section
open MeasureTheory
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatIntegralSecondMoment
open HigherHeatSignedLaws HigherHeatCylinderFourier HigherHeatStepIntegralLaws
open HigherHeatStepIntegralRealization HigherHeatSignedPolynomialCalculus

theorem heat_second_integrable (m : ℕ) (hm : 0 < m) (T : ℝ≥0) :
    (heatLaw m hm T).Integrable (fun y : ℝ => (y : ℂ)^2) := by
  by_cases hT : 0 < T
  · rw [heatLaw, dif_pos hT]
    have hh := polynomial_signed_integrable m hm T hT ((Polynomial.X : Polynomial ℝ)^2)
    simpa only [Polynomial.eval_pow, Polynomial.eval_X, Complex.ofReal_pow] using hh
  · rw [heatLaw, dif_neg hT, zeroLaw]
    change Integrable (fun y : ℝ => (y : ℂ)^2)
      ((Measure.dirac (0 : ℝ)).toSignedMeasure.variation)
    rw [Measure.variation_toSignedMeasure]
    exact integrable_dirac (a := (0 : ℝ)) (f := fun y : ℝ => (y : ℂ)^2) (by simp)

theorem heat_second_zero (m : ℕ) (hm : 2 ≤ m) (T : ℝ≥0) :
    (∫ᵛ y : ℝ, (y : ℂ)^2 ∂<•heatLaw m (by omega) T) = 0 := by
  by_cases hT : 0 < T
  · rw [heatLaw, dif_pos hT, signed_moment]
    have hz : (1 : ℕ).descFactorial (2*m-1) = 0 := Nat.descFactorial_of_lt (by omega)
    simp only [PseudoPolynomialStein.moment_succ, hz, Nat.cast_zero, mul_zero, zero_mul,
      Complex.ofReal_zero]
  · rw [heatLaw, dif_neg hT, zeroLaw, VectorMeasure.integral_toSignedMeasure, integral_dirac]
    simp

theorem heat_not_dirac (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    heatLaw m hm T ≠ zeroLaw := by
  intro he
  have hh := congrArg (fun μ : SignedMeasure ℝ => ∫ᵛ y, phase 1 y ∂<•μ) he
  rw [heatLaw_fourier, zeroLaw_fourier] at hh
  have hr := congrArg Complex.re hh
  change Real.exp (-(T : ℝ) * (2 * Real.pi * 1) ^ (2*m)) = 1 at hr
  have hn : -(T : ℝ) * (2 * Real.pi * 1) ^ (2*m) < 0 :=
    mul_neg_of_neg_of_pos (neg_neg_of_pos hT) (pow_pos (by positivity) _)
  have hs := Real.exp_lt_one_iff.mpr hn
  linarith

theorem integral_second_degeneracy {ι : Type*} [Fintype ι] (m : ℕ) (hm : 2 ≤ m)
    (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i) (u : ι → ℝ) (hA : 0 < effectiveTime m t u) :
    (integralLaw m (by omega) t ht u).Integrable (fun y : ℝ => (y : ℂ)^2) ∧
    (∫ᵛ y : ℝ, (y : ℂ)^2 ∂<•integralLaw m (by omega) t ht u) = 0 ∧
    integralLaw m (by omega) t ht u ≠ zeroLaw := by
  rw [integralLaw_eq_heatLaw]
  exact ⟨heat_second_integrable m (by omega) _, heat_second_zero m hm _,
    heat_not_dirac m (by omega) _ hA⟩

theorem biharmonic_integral_fourth {ι : Type*} [Fintype ι] (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (u : ι → ℝ) :
    (∫ᵛ y : ℝ, (y : ℂ)^4 ∂<•integralLaw 2 (by norm_num) t ht u) =
      -24 * (effectiveTime 2 t u : ℝ) := by
  rw [integralLaw_eq_heatLaw]
  by_cases hA : 0 < effectiveTime 2 t u
  · rw [heatLaw, dif_pos hA, biharmonic_signed_fourth]
  · have h0 : effectiveTime 2 t u = 0 := le_antisymm (le_of_not_gt hA) bot_le
    rw [heatLaw, dif_neg hA, zeroLaw, VectorMeasure.integral_toSignedMeasure, integral_dirac, h0]
    simp

end OperatorDerivativeRewrite.Foundation.HigherHeatIntegralSecondMoment
