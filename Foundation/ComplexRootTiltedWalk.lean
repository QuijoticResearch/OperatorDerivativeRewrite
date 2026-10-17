import Foundation.ComplexRootTiltedStep
import Foundation.ComplexRootPoissonSemigroup

/-! Iterated weighted operators are actual weighted expectations of independent complex walks. -/
noncomputable section
open MeasureTheory Filter
namespace OperatorDerivativeRewrite.Foundation.ComplexRootTiltedWalk
open ComplexFourthRootWalk ComplexRootTransitionOperator ComplexRootTiltedStep

theorem weighted_successor (n : ℕ) (a ξ : ℝ) (f : Test) (z : ℂ) :
    (∫ ω, Complex.exp (Complex.I*(ξ : ℂ)*terminal (n+1) a ω) *
      f (z+terminal (n+1) a ω) ∂ComplexFourthRootWalk.probability (n+1)) =
      ∫ k : Fin 4, weight a ξ k * (∫ ω,
        Complex.exp (Complex.I*(ξ : ℂ)*terminal n a ω) *
          f (z+ComplexFourthRootNoise.noise a k+terminal n a ω)
        ∂ComplexFourthRootWalk.probability n) ∂ComplexFourthRootNoise.probability := by
  have he := ComplexRootPoissonSemigroup.walk_successor_integral n a
    (fun y => Complex.exp (Complex.I*(ξ : ℂ)*y) * f (z+y)) 0
  simp only [zero_add] at he
  rw [he]
  apply integral_congr_ae
  filter_upwards with k
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ω
  simp only [mul_add, Complex.exp_add, weight, add_assoc, mul_assoc]

theorem weightedStep_pow_apply (a ξ : ℝ) (n : ℕ) (f : Test) (z : ℂ) :
    ((weightedStep a ξ)^n) f z = ∫ ω,
      Complex.exp (Complex.I*(ξ : ℂ)*terminal n a ω) * f (z+terminal n a ω)
        ∂ComplexFourthRootWalk.probability n := by
  induction n generalizing z with
  | zero => simp [terminal]
  | succ n ih =>
    rw [pow_succ']
    change weightedStep a ξ (((weightedStep a ξ)^n) f) z = _
    rw [weightedStep_integral, weighted_successor]
    apply integral_congr_ae
    exact Eventually.of_forall fun k => congrArg (weight a ξ k * ·)
      (ih (z+ComplexFourthRootNoise.noise a k))

end OperatorDerivativeRewrite.Foundation.ComplexRootTiltedWalk
