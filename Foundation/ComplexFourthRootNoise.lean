import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.Complex.Trigonometric

/-! A genuine four-point probability noise with vanishing lower holomorphic moments. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.ComplexFourthRootNoise

def probability : Measure (Fin 4) := (PMF.uniformOfFintype (Fin 4)).toMeasure

instance probability_isProbability : IsProbabilityMeasure probability := by
  unfold probability
  infer_instance

def root (k : Fin 4) : ℂ := ![1+Complex.I, -1+Complex.I, -1-Complex.I, 1-Complex.I] k

def noise (a : ℝ) (k : Fin 4) : ℂ := (a : ℂ) * root k

theorem noise_measurable (a : ℝ) : Measurable (noise a) := measurable_of_countable _

theorem noise_integrable (a : ℝ) : Integrable (noise a) probability := Integrable.of_finite

theorem integral_formula (f : Fin 4 → ℂ) :
    (∫ k, f k ∂probability) = (f 0 + f 1 + f 2 + f 3)/4 := by
  rw [probability, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
  norm_num [Fin.sum_univ_succ, Complex.real_smul]
  ring

theorem root_fourth (k : Fin 4) : (root k)^4 = -4 := by
  fin_cases k <;> norm_num [root, Complex.I_sq] <;> ring_nf <;> norm_num [Complex.I_sq] <;> ring

theorem mean (a : ℝ) : (∫ k, noise a k ∂probability) = 0 := by
  rw [integral_formula]
  norm_num [noise, root]
  ring

theorem second (a : ℝ) : (∫ k, (noise a k)^2 ∂probability) = 0 := by
  rw [integral_formula]
  norm_num [noise, root]
  ring_nf
  norm_num [Complex.I_sq]

theorem third (a : ℝ) : (∫ k, (noise a k)^3 ∂probability) = 0 := by
  rw [integral_formula]
  norm_num [noise, root]
  ring

theorem fourth (a : ℝ) : (∫ k, (noise a k)^4 ∂probability) = -4*(a : ℂ)^4 := by
  simp_rw [noise, mul_pow, root_fourth]
  simp [mul_comm]

theorem norm_square (a : ℝ) (k : Fin 4) : ‖noise a k‖^2 = 2*a^2 := by
  rw [noise, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hr : ‖root k‖^2 = 2 := by
    rw [Complex.sq_norm]
    fin_cases k <;> norm_num [root, Complex.normSq_apply]
  rw [hr]
  ring

theorem absolute_second (a : ℝ) : (∫ k, ‖noise a k‖^2 ∂probability) = 2*a^2 := by
  simp_rw [norm_square]
  simp

end OperatorDerivativeRewrite.Foundation.ComplexFourthRootNoise
