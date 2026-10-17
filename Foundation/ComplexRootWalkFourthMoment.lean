import Foundation.ComplexRootPoissonSemigroup
import Foundation.ComplexRootWalkSecondMoment

/-! Exact positive fourth moments of the actual finite complex-root walks. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.ComplexRootWalkFourthMoment
open ComplexFourthRootNoise ComplexFourthRootWalk ComplexRootOneStepCalculus
open ComplexRootWalkSecondMoment ComplexRootPoissonSemigroup

theorem walk_successor_real (n : ℕ) (a : ℝ) (F : ℂ → ℝ) :
    (∫ ω, F (terminal (n+1) a ω) ∂ComplexFourthRootWalk.probability (n+1)) =
      ∫ ω, (∫ k : Fin 4, F (terminal n a ω + noise a k)
        ∂ComplexFourthRootNoise.probability) ∂ComplexFourthRootWalk.probability n := by
  have he := walk_successor_integral n a (fun z => ((F z : ℝ) : ℂ)) 0
  simp only [zero_add, integral_complex_ofReal] at he
  have hr := Complex.ofReal_injective he
  rw [hr, integral_integral_swap Integrable.of_finite]
  congr 1
  funext ω
  congr 1
  funext k
  rw [add_comm]

theorem absolute_fourth_successor (n : ℕ) (a : ℝ) :
    (∫ ω, ‖terminal (n+1) a ω‖^4 ∂ComplexFourthRootWalk.probability (n+1)) =
      (∫ ω, ‖terminal n a ω‖^4 ∂ComplexFourthRootWalk.probability n) +
        8*a^2*(2*(n : ℝ)*a^2) + 4*a^4 := by
  rw [walk_successor_real n a (fun z => ‖z‖^4)]
  simp_rw [shifted_norm_fourth]
  rw [integral_add (Integrable.of_finite) (integrable_const _),
    integral_add (Integrable.of_finite) (Integrable.of_finite), integral_const_mul,
    terminal_absolute_second]
  simp

theorem terminal_absolute_fourth (n : ℕ) (a : ℝ) :
    (∫ ω, ‖terminal n a ω‖^4 ∂ComplexFourthRootWalk.probability n) =
      (8*(n : ℝ)^2 - 4*(n : ℝ))*a^4 := by
  induction n with
  | zero => simp [terminal]
  | succ n ih =>
    rw [absolute_fourth_successor, ih]
    push_cast
    ring

end OperatorDerivativeRewrite.Foundation.ComplexRootWalkFourthMoment
