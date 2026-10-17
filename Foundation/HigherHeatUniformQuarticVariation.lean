import Foundation.HigherHeatQuarticVariation

/-! Exact decay of the actual uniform-grid centered quartic signed second moment. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatUniformQuarticVariation
open HigherHeatSignedLaws HigherHeatPowerVariation HigherHeatQuarticVariation

def duration (T : ℝ≥0) (n : ℕ) : ℝ≥0 := T / (n+1 : ℕ)

theorem duration_pos (T : ℝ≥0) (hT : 0 < T) (n : ℕ) : 0 < duration T n := by
  unfold duration
  positivity

theorem duration_coe (T : ℝ≥0) (n : ℕ) :
    (duration T n : ℝ) = (T : ℝ)/(n+1 : ℕ) := by simp [duration]

def law (T : ℝ≥0) (hT : 0 < T) (n : ℕ) : SignedMeasure (Fin (n+1) → ℝ) :=
  incrementLaw 2 (by norm_num) (fun _ => duration T n) (fun _ => duration_pos T hT n)

theorem durations_sum (T : ℝ≥0) (n : ℕ) :
    (∑ _ : Fin (n+1), ((duration T n : ℝ) : ℂ)) = ((T : ℝ) : ℂ) := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, duration_coe]
  push_cast
  field_simp

theorem durations_square_sum (T : ℝ≥0) (n : ℕ) :
    (∑ _ : Fin (n+1), ((duration T n : ℝ) : ℂ)^2) =
      ((T : ℝ) : ℂ)^2 / (n+1 : ℕ) := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, duration_coe]
  push_cast
  field_simp

theorem quadratic_second_moment (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    (∫ᵛ x, (powerSum 2 x)^2 ∂<•law T hT n) = -24*((T : ℝ) : ℂ) := by
  have he := quadratic_sum_second_moment (fun _ : Fin (n+1) => duration T n)
    (fun _ => duration_pos T hT n)
  rw [Complex.ofReal_sum, durations_sum] at he
  exact he

theorem quartic_mean (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    (∫ᵛ x, powerSum 4 x ∂<•law T hT n) = -24*((T : ℝ) : ℂ) := by
  have he := quartic_sum_mean (fun _ : Fin (n+1) => duration T n)
    (fun _ => duration_pos T hT n)
  rw [Complex.ofReal_sum, durations_sum] at he
  exact he

theorem centered_quartic_second_moment (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    (∫ᵛ x, (powerSum 4 x + 24*((T : ℝ) : ℂ))^2 ∂<•law T hT n) =
      19584*((T : ℝ) : ℂ)^2 / (n+1 : ℕ) := by
  have he := HigherHeatQuarticVariation.centered_quartic_second_moment
    (fun _ : Fin (n+1) => duration T n) (fun _ => duration_pos T hT n)
  rw [durations_sum, durations_square_sum] at he
  simpa only [law, mul_div_assoc] using he

theorem centered_quartic_second_moment_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => ∫ᵛ x, (powerSum 4 x + 24*((T : ℝ) : ℂ))^2 ∂<•law T hT n)
      atTop (𝓝 0) := by
  simp_rw [centered_quartic_second_moment]
  have he := (tendsto_const_div_atTop_nhds_zero_nat (19584*(T : ℝ)^2)).comp
    (tendsto_add_atTop_nat 1)
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp he
  simpa only [Function.comp_def, Complex.ofReal_zero, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_natCast] using hc

end OperatorDerivativeRewrite.Foundation.HigherHeatUniformQuarticVariation
