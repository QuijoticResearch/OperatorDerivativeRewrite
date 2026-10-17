import Foundation.ComplexFourthRootWalk

/-! Exact holomorphic and positive-norm one-step calculus for an actual complex probability noise. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.ComplexRootOneStepCalculus
open ComplexFourthRootNoise ComplexFourthRootWalk

theorem integral_real_formula (f : Fin 4 → ℝ) :
    (∫ k, f k ∂ComplexFourthRootNoise.probability) = (f 0 + f 1 + f 2 + f 3)/4 := by
  rw [ComplexFourthRootNoise.probability, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
  norm_num [Fin.sum_univ_succ]
  ring

theorem shifted_fourth (a : ℝ) (z : ℂ) :
    (∫ k, (z + noise a k)^4 ∂ComplexFourthRootNoise.probability) = z^4 - 4*(a : ℂ)^4 := by
  rw [integral_formula]
  norm_num [noise, root]
  ring_nf
  norm_num [Complex.I_sq]
  ring

theorem shifted_norm_square (a : ℝ) (z : ℂ) :
    (∫ k, ‖z + noise a k‖^2 ∂ComplexFourthRootNoise.probability) = ‖z‖^2 + 2*a^2 := by
  simp_rw [Complex.sq_norm, Complex.normSq_apply]
  rw [integral_real_formula]
  norm_num [noise, root, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  ring

theorem shifted_norm_fourth (a : ℝ) (z : ℂ) :
    (∫ k, ‖z + noise a k‖^4 ∂ComplexFourthRootNoise.probability) =
      ‖z‖^4 + 8*a^2*‖z‖^2 + 4*a^4 := by
  simp_rw [show (4 : ℕ) = 2*2 from rfl, pow_mul, Complex.sq_norm, Complex.normSq_apply]
  rw [integral_real_formula]
  norm_num [noise, root, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  ring

theorem stepTransform_formula (a ξ : ℝ) :
    stepTransform a ξ = Complex.cos (((a*ξ : ℝ) : ℂ)) * Complex.cosh (((a*ξ : ℝ) : ℂ)) := by
  let z : ℂ := ((a*ξ : ℝ) : ℂ)
  unfold stepTransform
  rw [integral_formula]
  have h₀ : Complex.I * (ξ : ℂ) * noise a 0 = z*Complex.I + (-z) := by
    norm_num [noise, root, z]
    ring_nf
    norm_num [Complex.I_sq]
    ring
  have h₁ : Complex.I * (ξ : ℂ) * noise a 1 = -z*Complex.I + (-z) := by
    norm_num [noise, root, z]
    ring_nf
    norm_num [Complex.I_sq]
    ring
  have h₂ : Complex.I * (ξ : ℂ) * noise a 2 = -z*Complex.I + z := by
    norm_num [noise, root, z]
    ring_nf
    norm_num [Complex.I_sq]
  have h₃ : Complex.I * (ξ : ℂ) * noise a 3 = z*Complex.I + z := by
    norm_num [noise, root, z]
    ring_nf
    norm_num [Complex.I_sq]
  rw [h₀, h₁, h₂, h₃]
  simp only [Complex.exp_add, Complex.cos, Complex.cosh]
  change _ = ((Complex.exp (z*Complex.I) + Complex.exp (-z*Complex.I))/2) *
    ((Complex.exp z + Complex.exp (-z))/2)
  ring

end OperatorDerivativeRewrite.Foundation.ComplexRootOneStepCalculus
