import Foundation.ComplexRootPoissonQuarticDrift
import Foundation.ComplexRootWalkFourthMoment
import Foundation.ComplexRootScaledMoments

/-! Exact positive moments of genuine compound-root probability laws and their heat scaling. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.ComplexRootPoissonPositiveMoments
open ComplexFourthRootWalk ComplexRootPoissonPolynomialDomain PoissonCountMoments
open ComplexRootWalkSecondMoment ComplexRootWalkFourthMoment
open ComplexRootHeatTransformLimit ComplexRootScaledMoments

theorem absolute_second (r : ℝ≥0) (a : ℝ) :
    (∫ z : ℂ, ‖z‖^2 ∂ComplexRootPoissonLaw.law r a) = 2*(r : ℝ)*a^2 := by
  rw [norm_power_mixture]
  simp_rw [terminal_absolute_second]
  rw [integral_mul_const, integral_const_mul, count_integral]

theorem absolute_fourth (r : ℝ≥0) (a : ℝ) :
    (∫ z : ℂ, ‖z‖^4 ∂ComplexRootPoissonLaw.law r a) =
      (8*(r : ℝ)^2+4*(r : ℝ))*a^4 := by
  rw [norm_power_mixture]
  simp_rw [terminal_absolute_fourth]
  rw [integral_mul_const,
    integral_sub ((count_power_integrable r 2).const_mul 8) ((count_integrable r).const_mul 4),
    integral_const_mul, integral_const_mul, square_integral, count_integral]
  ring

theorem scaled_second_square (T : ℝ≥0) (n : ℕ) :
    (∫ z : ℂ, ‖z‖^2 ∂ComplexRootPoissonLaw.law (n : ℝ≥0) (amplitude T n))^2 =
      24*(T : ℝ)*n := by
  rw [absolute_second]
  calc
    _ = 4*(n : ℝ)^2*(amplitude T n)^4 := by push_cast; ring
    _ = _ := by
      rw [amplitude_fourth]
      by_cases hn : n = 0
      · simp [hn]
      · have hnr : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
        field_simp [hnr]
        ring

theorem scaled_fourth (T : ℝ≥0) (n : ℕ) (hn : n ≠ 0) :
    (∫ z : ℂ, ‖z‖^4 ∂ComplexRootPoissonLaw.law (n : ℝ≥0) (amplitude T n)) =
      48*(T : ℝ)*n+24*(T : ℝ) := by
  rw [absolute_fourth, amplitude_fourth]
  push_cast
  have hnr : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp [hnr]
  ring

theorem scaled_fourth_bound (T : ℝ≥0) (n : ℕ) (hn : n ≠ 0) :
    (∫ z : ℂ, ‖z‖^4 ∂ComplexRootPoissonLaw.law (n : ℝ≥0) (amplitude T n)) ≤
      3*(∫ z : ℂ, ‖z‖^2 ∂ComplexRootPoissonLaw.law (n : ℝ≥0) (amplitude T n))^2 := by
  rw [scaled_fourth T n hn, scaled_second_square]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hT := T.coe_nonneg
  nlinarith

end OperatorDerivativeRewrite.Foundation.ComplexRootPoissonPositiveMoments
