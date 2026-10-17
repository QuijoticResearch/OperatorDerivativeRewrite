import Foundation.ComplexRootMarkRepresentation
import Foundation.ComplexRootTransitionOperator

/-! Bounded derivative channels reconstruct every actual four-point jump kernel. -/
noncomputable section
open MeasureTheory
open scoped BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.ComplexRootChannelOperator
open ComplexFourthRootNoise ComplexRootTransitionOperator ComplexRootMarkRepresentation

def channel (a : ℝ) (r : Fin 3) : Test →L[ℂ] Test :=
  (fourthMoment a)⁻¹ • ((1/4 : ℂ) • ∑ k : Fin 4,
    (noise a k)^(3-r.val) • shift (noise a k))

theorem channel_apply (a : ℝ) (r : Fin 3) (f : Test) (z : ℂ) :
    channel a r f z = coefficient a (fun k => f (z+noise a k)) r := by
  norm_num [channel, coefficient, shift, integral_formula, Fin.sum_univ_succ, smul_eq_mul]
  ring

theorem channel_constant (a : ℝ) (r : Fin 3) (c : ℂ) :
    channel a r (BoundedContinuousFunction.const ℂ c) = 0 := by
  ext z
  rw [channel_apply]
  fin_cases r <;> simp [coefficient, integral_const_mul, mean, second, third]

theorem jump_kernel_decomposition (a : ℝ) (ha : a ≠ 0) (f : Test) (z : ℂ) (k : Fin 4) :
    f (z+noise a k)-f z = generator 1 a f z +
      channel a 0 f z*noise a k + channel a 1 f z*(noise a k)^2 +
      channel a 2 f z*(noise a k)^3 := by
  have he := centered_representation a ha (fun j => f (z+noise a j)) k
  rw [← channel_apply a 0 f z, ← channel_apply a 1 f z, ← channel_apply a 2 f z] at he
  rw [generator_apply]
  norm_num only [Complex.ofReal_one, one_mul]
  rw [step_integral]
  linear_combination he

end OperatorDerivativeRewrite.Foundation.ComplexRootChannelOperator
