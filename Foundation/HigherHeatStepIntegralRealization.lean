import Foundation.HigherHeatStepIntegralLaws
import Foundation.SignedHeatFourierUniqueness
import Foundation.FourierPathFutureIntegral

/-! Exact realization of every deterministic step-integral law, including its zero-clock case. -/
noncomputable section
open MeasureTheory
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatStepIntegralRealization
open HigherHeatSignedLaws HigherHeatCylinderFourier HigherHeatStepIntegralLaws

def zeroLaw : SignedMeasure ℝ := (Measure.dirac (0 : ℝ)).toSignedMeasure

theorem zeroLaw_fourier (ξ : ℝ) : (∫ᵛ y, phase ξ y ∂<•zeroLaw) = 1 := by
  rw [zeroLaw, VectorMeasure.integral_toSignedMeasure, integral_dirac]
  simp [phase]

def heatLaw (m : ℕ) (hm : 0 < m) (T : ℝ≥0) : SignedMeasure ℝ :=
  if hT : 0 < T then law m hm T hT else zeroLaw

theorem heatLaw_fourier (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (ξ : ℝ) :
    (∫ᵛ y, phase ξ y ∂<•heatLaw m hm T) = HigherHeatL2.symbol m T ξ := by
  by_cases hT : 0 < T
  · rw [heatLaw, dif_pos hT]
    have hh := FourierPathFutureIntegral.shifted_signed_integral m hm T hT 0 ξ
    simpa [phase] using hh
  · have h0 : T = 0 := le_antisymm (le_of_not_gt hT) bot_le
    rw [heatLaw, dif_neg hT, zeroLaw_fourier, h0, HigherHeatL2.symbol_zero]

theorem heatLaw_mass (m : ℕ) (hm : 0 < m) (T : ℝ≥0) : heatLaw m hm T Set.univ = 1 := by
  by_cases hT : 0 < T
  · rw [heatLaw, dif_pos hT, law_mass]
  · rw [heatLaw, dif_neg hT]
    simp [zeroLaw]

theorem integralLaw_eq_heatLaw {ι : Type*} [Fintype ι] (m : ℕ) (hm : 0 < m)
    (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i) (u : ι → ℝ) :
    integralLaw m hm t ht u = heatLaw m hm (effectiveTime m t u) := by
  apply SignedHeatFourierUniqueness.ext
  intro ξ
  rw [integralLaw_clock, heatLaw_fourier]

theorem law_eq_of_clock {ι κ : Type*} [Fintype ι] [Fintype κ] (m : ℕ) (hm : 0 < m)
    (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i) (u : ι → ℝ)
    (s : κ → ℝ≥0) (hs : ∀ i, 0 < s i) (v : κ → ℝ)
    (h : effectiveTime m t u = effectiveTime m s v) :
    integralLaw m hm t ht u = integralLaw m hm s hs v := by
  rw [integralLaw_eq_heatLaw, integralLaw_eq_heatLaw, h]

theorem zero_control_law {ι : Type*} [Fintype ι] (m : ℕ) (hm : 0 < m)
    (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i) : integralLaw m hm t ht (fun _ => 0) = zeroLaw := by
  have hp : 2*m ≠ 0 := Nat.ne_of_gt (Nat.mul_pos (by norm_num) hm)
  rw [integralLaw_eq_heatLaw]
  have he : effectiveTime m t (fun _ : ι => (0 : ℝ)) = 0 := by simp [effectiveTime, hp]
  rw [he, heatLaw, dif_neg (by simp)]

end OperatorDerivativeRewrite.Foundation.HigherHeatStepIntegralRealization
