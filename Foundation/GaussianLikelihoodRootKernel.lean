import Foundation.GaussianRandomDensityKernel

/-! Exact square-root likelihood fibers and their Gaussian integrals. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.GaussianLikelihoodRootKernel
open GaussianCore GaussianRandomDensityKernel
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def rootKernel (a y : ℝ) : ℝ := Real.exp (-a*y/2-a^2/4)

theorem rootKernel_positive (a y : ℝ) : 0 < rootKernel a y := Real.exp_pos _

theorem rootKernel_continuous : Continuous (Function.uncurry rootKernel) := by
  unfold rootKernel
  fun_prop

theorem rootKernel_square (a y : ℝ) : (rootKernel a y)^2 = kernel a y := by
  simp only [rootKernel, kernel, pow_two, ← Real.exp_add]
  congr 1
  ring

theorem rootKernel_eq_sqrt (a y : ℝ) : rootKernel a y = Real.sqrt (kernel a y) := by
  rw [← rootKernel_square, Real.sqrt_sq_eq_abs, abs_of_pos (rootKernel_positive a y)]

theorem rootKernel_factor (a y : ℝ) :
    rootKernel a y = Real.exp (-a^2/8) * kernel (a/2) y := by
  simp only [rootKernel, kernel, ← Real.exp_add]
  congr 1
  ring

theorem rootKernel_integrable (a : ℝ) : Integrable (rootKernel a) γ := by
  have h : rootKernel a = fun y => Real.exp (-a^2/8) * kernel (a/2) y :=
    funext (rootKernel_factor a)
  rw [h]
  exact (kernel_integrable (a/2)).const_mul _

theorem rootKernel_integral (a : ℝ) :
    (∫ y, rootKernel a y ∂γ) = Real.exp (-a^2/8) := by
  have h : rootKernel a = fun y => Real.exp (-a^2/8) * kernel (a/2) y :=
    funext (rootKernel_factor a)
  rw [h, integral_const_mul, kernel_integral, mul_one]

theorem rootKernel_square_integral (a : ℝ) : (∫ y, (rootKernel a y)^2 ∂γ) = 1 := by
  simp_rw [rootKernel_square]
  exact kernel_integral a

theorem fiber_mean_le_one (a : ℝ) : Real.exp (-a^2/8) ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  nlinarith [sq_nonneg a]

theorem fiber_mean_lt_one (a : ℝ) (ha : a ≠ 0) : Real.exp (-a^2/8) < 1 := by
  apply Real.exp_lt_one_iff.mpr
  nlinarith [sq_pos_of_ne_zero ha]

end OperatorDerivativeRewrite.Foundation.GaussianLikelihoodRootKernel
