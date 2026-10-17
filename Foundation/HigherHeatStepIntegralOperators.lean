import Foundation.HigherHeatStepIntegralRealization
import Foundation.FourierPathTerminalKernels

/-! Actual deterministic step integrals instantiate the complete Fourier heat operator calculus. -/
noncomputable section
open MeasureTheory
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.HigherHeatStepIntegralOperators
open HigherHeatSignedLaws HigherHeatStepIntegralLaws HigherHeatStepIntegralRealization
open HigherHeatFourierBanach HigherHeatFourierPathSemigroup FourierPathStopping
open FourierPathTerminalKernels FourierPathKernelFunctionals SignedDensityIntegral

theorem heatLaw_operator (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m) (T : ℝ≥0)
    (q : TestSpace terminalLevels (frequency a)) (x : ℝ) :
    realize terminalLevels (frequency a) (evolution terminalLevels (frequency a) m hm T q)
      (line x) = ∫ᵛ y, realize terminalLevels (frequency a) q (shiftedLine x y)
        ∂<•heatLaw m hm T := by
  by_cases hT : 0 < T
  · rw [heatLaw, dif_pos hT]
    exact heat_signed_representation a m hm T hT x q
  · have h0 : T = 0 := le_antisymm (le_of_not_gt hT) bot_le
    rw [h0, evolution_zero, heatLaw, dif_neg (by simp), zeroLaw,
      VectorMeasure.integral_toSignedMeasure, integral_dirac]
    simp only [shiftedLine, add_zero]

theorem integral_operator {ι : Type*} [Fintype ι] (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m)
    (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i) (u : ι → ℝ)
    (q : TestSpace terminalLevels (frequency a)) (x : ℝ) :
    realize terminalLevels (frequency a)
      (evolution terminalLevels (frequency a) m hm (effectiveTime m t u) q) (line x) =
      ∫ᵛ y, realize terminalLevels (frequency a) q (shiftedLine x y)
        ∂<•integralLaw m hm t ht u := by
  rw [integralLaw_eq_heatLaw]
  exact heatLaw_operator a m hm _ q x

theorem increment_operator {ι : Type*} [Fintype ι] (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m)
    (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i) (u : ι → ℝ)
    (q : TestSpace terminalLevels (frequency a)) (x : ℝ) :
    realize terminalLevels (frequency a)
      (evolution terminalLevels (frequency a) m hm (effectiveTime m t u) q) (line x) =
      ∫ᵛ v, realize terminalLevels (frequency a) q (shiftedLine x (integralMap u v))
        ∂<•incrementLaw m hm t ht := by
  have hfm : Measurable (fun y => realize terminalLevels (frequency a) q (shiftedLine x y)) :=
    ((realize terminalLevels (frequency a) q).continuous.comp (shiftedLine_continuous x)).measurable
  have hgm : Measurable (fun v => realize terminalLevels (frequency a) q
      (shiftedLine x (integralMap u v))) := hfm.comp (integralMap_measurable u)
  have hi := bounded_signed_integrable (incrementLaw m hm t ht) _ hgm ‖q‖
    (fun v => test_bound terminalLevels (frequency a) q _)
  rw [integral_operator a m hm t ht u q x, integralLaw,
    VectorMeasure.integral_map (integralMap_measurable u)
    hfm.aestronglyMeasurable hi]

theorem integral_expectation_bound {ι : Type*} [Fintype ι] (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m)
    (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i) (u : ι → ℝ)
    (q : TestSpace terminalLevels (frequency a)) (x : ℝ) :
    ‖∫ᵛ v, realize terminalLevels (frequency a) q (shiftedLine x (integralMap u v))
      ∂<•incrementLaw m hm t ht‖ ≤ ‖q‖ := by
  rw [← increment_operator a m hm t ht u q x]
  exact (test_bound terminalLevels (frequency a) _ (line x)).trans
    (evolution_bound terminalLevels (frequency a) m hm _ q)

end OperatorDerivativeRewrite.Foundation.HigherHeatStepIntegralOperators
