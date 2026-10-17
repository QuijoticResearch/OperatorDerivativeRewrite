import Foundation.FourierPathRoughDirection
import Foundation.FourierPathTransferSymbols
import Mathlib.Analysis.SpecificLimits.Basic

/-! Actual unbounded expectation-transfer along a continuous rough path direction. -/
noncomputable section
open Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathRoughTransferObstruction
open HigherHeatFourierBanach HigherHeatFourierPathSemigroup HigherHeatFourierPathDerivative
open FourierPathDirectionalCharacters FourierPathDirectionalOperator FourierPathTransferSymbols
open FourierPathRoughDirection

theorem multiplier_value (T : ℝ≥0) (n : ℕ) :
    multiplier levels frequencies 2 T (n+1)=(Real.exp (-(T:ℝ)):ℝ) := by
  rw [multiplier_exp, quartic_rate, mul_one]

theorem expected_derivative (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    expectation levels frequencies 2 (by norm_num) T hT
      (derivativeTest levels frequencies direction (n+1))=
      eigenvalue (-(2:ℝ)^n)*(Real.exp (-(T:ℝ)):ℝ) := by
  rw [expectation_derivativeTest, directional_frequency, multiplier_value]

theorem expected_derivative_norm (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    ‖expectation levels frequencies 2 (by norm_num) T hT
      (derivativeTest levels frequencies direction (n+1))‖=(2:ℝ)^n*Real.exp (-(T:ℝ)) := by
  rw [expected_derivative, norm_mul, eigenvalue_norm, norm_neg, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem derivative_norm_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => ‖expectation levels frequencies 2 (by norm_num) T hT
      (derivativeTest levels frequencies direction (n+1))‖) atTop atTop := by
  have hp : Tendsto (fun n : ℕ => (2:ℝ)^n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  simpa only [expected_derivative_norm] using hp.atTop_mul_const (Real.exp_pos (-(T:ℝ)))

theorem no_bound (T : ℝ≥0) (hT : 0 < T) :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ graph levels frequencies direction,
      ‖expectation levels frequencies 2 (by norm_num) T hT z.2‖ ≤ C*‖z.1‖ := by
  rintro ⟨C,hC,hb⟩
  obtain ⟨n,hn⟩ := ((derivative_norm_tendsto T hT).eventually (eventually_gt_atTop C)).exists
  have hh := bound_symbols levels frequencies direction 2 (by norm_num) T hT C hC hb (n+1)
  rw [← expectation_derivativeTest levels frequencies direction 2 (by norm_num) T hT (n+1)] at hh
  exact not_lt_of_ge hh hn

theorem no_continuous_transfer (T : ℝ≥0) (hT : 0 < T) :
    ¬ ∃ L : TestSpace levels frequencies →L[ℝ] ℂ,
      ∀ z ∈ graph levels frequencies direction,
        expectation levels frequencies 2 (by norm_num) T hT z.2=L z.1 := by
  rintro ⟨L,hL⟩
  exact no_bound T hT (continuous_transfer_bound levels frequencies direction 2
    (by norm_num) T hT L hL)

theorem expected_derivative_imag (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    (expectation levels frequencies 2 (by norm_num) T hT
      (derivativeTest levels frequencies direction (n+1))).im=
      -(2:ℝ)^n*Real.exp (-(T:ℝ)) := by
  rw [expected_derivative]
  change ((Complex.I * (Complex.ofReal (-(2:ℝ)^n))) * (Complex.ofReal (Real.exp (-(T:ℝ))))).im=_
  simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, zero_add, add_zero, one_mul, sub_zero]

theorem no_real_dual_transfer (T : ℝ≥0) (hT : 0 < T) :
    ¬ ∃ L : StrongDual ℝ (TestSpace levels frequencies),
      ∀ z ∈ graph levels frequencies direction,
        (expectation levels frequencies 2 (by norm_num) T hT z.2).im=L z.1 := by
  rintro ⟨L,hL⟩
  have hp : Tendsto (fun n : ℕ => (2:ℝ)^n*Real.exp (-(T:ℝ))) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2)).atTop_mul_const
      (Real.exp_pos (-(T:ℝ)))
  obtain ⟨n,hn⟩ := (hp.eventually (eventually_gt_atTop ‖L‖)).exists
  have he := hL (generator levels frequencies (n+1),derivativeTest levels frequencies direction (n+1))
    (derivativeTest_graph levels frequencies direction (n+1))
  change (expectation levels frequencies 2 (by norm_num) T hT
    (derivativeTest levels frequencies direction (n+1))).im=L (generator levels frequencies (n+1)) at he
  have hb : ‖L (generator levels frequencies (n+1))‖ ≤ ‖L‖ :=
    (L.le_opNorm _).trans ((mul_le_mul_of_nonneg_left
      (generator_bound levels frequencies (n+1)) (norm_nonneg L)).trans_eq (mul_one _))
  rw [← he, expected_derivative_imag, Real.norm_eq_abs, abs_mul, abs_neg,
    abs_of_nonneg (by positivity), abs_of_pos (Real.exp_pos _)] at hb
  exact not_lt_of_ge hb hn

end OperatorDerivativeRewrite.Foundation.FourierPathRoughTransferObstruction
