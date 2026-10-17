import Foundation.ComplexRootWalkFourthMoment
import Foundation.ComplexRootScaledMoments
import Foundation.FiniteProbabilityTailBound

/-! Uniform positive lower tail mass under the genuine biharmonic-scaled complex walk laws. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.ComplexRootScaledTail
open ComplexFourthRootWalk ComplexRootHeatTransformLimit ComplexRootScaledMoments
open ComplexRootWalkFourthMoment

theorem scaled_absolute_fourth (T : ℝ≥0) (n : ℕ) (hn : n ≠ 0) :
    (∫ ω, ‖terminal n (amplitude T n) ω‖^4 ∂probability n) =
      48*(T : ℝ)*n - 24*(T : ℝ) := by
  rw [terminal_absolute_fourth, amplitude_fourth]
  have hnr : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp [hnr]
  ring

theorem scaled_fourth_bound (T : ℝ≥0) (n : ℕ) :
    (∫ ω, ‖terminal n (amplitude T n) ω‖^4 ∂probability n) ≤
      2*(∫ ω, ‖terminal n (amplitude T n) ω‖^2 ∂probability n)^2 := by
  by_cases hn : n = 0
  · subst n
    simp [terminal]
  · rw [scaled_absolute_fourth T n hn, absolute_second_square]
    have hT := T.coe_nonneg
    nlinarith

theorem tail_mass_lower (T : ℝ≥0) (hT : 0 < T) (n : ℕ) (hn : n ≠ 0)
    (b : ℝ) (hb : 0 ≤ b)
    (hbm : 2*b ≤ ∫ ω, ‖terminal n (amplitude T n) ω‖^2 ∂probability n) :
    1/8 ≤ (probability n).real {ω | b < ‖terminal n (amplitude T n) ω‖^2} := by
  let m : ℝ := ∫ ω, ‖terminal n (amplitude T n) ω‖^2 ∂probability n
  let p : ℝ := (probability n).real {ω | b < ‖terminal n (amplitude T n) ω‖^2}
  have hm : 0 ≤ m := integral_nonneg (fun _ => sq_nonneg _)
  have hp : 0 ≤ p := ENNReal.toReal_nonneg
  have hms : 0 < m^2 := by
    change 0 < (∫ ω, ‖terminal n (amplitude T n) ω‖^2 ∂probability n)^2
    rw [absolute_second_square]
    have hn' : 0 < n := Nat.pos_of_ne_zero hn
    positivity
  have hs := FiniteProbabilityTailBound.mean_tail_square (probability n)
    (fun ω => ‖terminal n (amplitude T n) ω‖^2) (fun _ => sq_nonneg _) b hb
    (by change b ≤ m; change 2*b ≤ m at hbm; linarith)
  simp only [← pow_mul, show 2*2=4 from rfl] at hs
  change (m-b)^2 ≤ (∫ ω, ‖terminal n (amplitude T n) ω‖^4 ∂probability n)*p at hs
  have hl : (m/2)^2 ≤ (m-b)^2 :=
    pow_le_pow_left₀ (by positivity) (by change 2*b ≤ m at hbm; linarith) 2
  have hu := mul_le_mul_of_nonneg_right (scaled_fourth_bound T n) hp
  change (∫ ω, ‖terminal n (amplitude T n) ω‖^4 ∂probability n)*p ≤ 2*m^2*p at hu
  have he : m^2*(1/8) ≤ m^2*p := by nlinarith
  exact le_of_mul_le_mul_left he hms

end OperatorDerivativeRewrite.Foundation.ComplexRootScaledTail
