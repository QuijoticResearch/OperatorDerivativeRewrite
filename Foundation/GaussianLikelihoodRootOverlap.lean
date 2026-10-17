import Foundation.GaussianLikelihoodRootKernel

/-! Exact overlap and squared distance of two Gaussian likelihood roots. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.GaussianLikelihoodRootOverlap
open GaussianCore GaussianRandomDensityKernel GaussianLikelihoodRootKernel
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

theorem overlap_factor (a b y : ℝ) :
    rootKernel a y * rootKernel b y =
      Real.exp (-(a-b)^2/8) * kernel ((a+b)/2) y := by
  simp only [rootKernel, kernel, ← Real.exp_add]
  congr 1
  ring

theorem overlap_integrable (a b : ℝ) :
    Integrable (fun y => rootKernel a y * rootKernel b y) γ := by
  have h : (fun y => rootKernel a y * rootKernel b y) =
      fun y => Real.exp (-(a-b)^2/8) * kernel ((a+b)/2) y := funext (overlap_factor a b)
  rw [h]
  exact (kernel_integrable _).const_mul _

theorem overlap_integral (a b : ℝ) :
    (∫ y, rootKernel a y * rootKernel b y ∂γ) = Real.exp (-(a-b)^2/8) := by
  simp_rw [overlap_factor]
  rw [integral_const_mul, kernel_integral, mul_one]

theorem distance_square_integrable (a b : ℝ) :
    Integrable (fun y => (rootKernel a y-rootKernel b y)^2) γ := by
  have h : (fun y => (rootKernel a y-rootKernel b y)^2) =
      (fun y => kernel a y + kernel b y) -
        (fun y => 2 * (rootKernel a y * rootKernel b y)) := by
    funext y
    simp only [Pi.sub_apply]
    rw [← rootKernel_square a y, ← rootKernel_square b y]
    ring
  rw [h]
  exact ((kernel_integrable a).add (kernel_integrable b)).sub
    ((overlap_integrable a b).const_mul 2)

theorem distance_square_integral (a b : ℝ) :
    (∫ y, (rootKernel a y-rootKernel b y)^2 ∂γ) =
      2 * (1-Real.exp (-(a-b)^2/8)) := by
  have h : (fun y => (rootKernel a y-rootKernel b y)^2) =
      (fun y => kernel a y + kernel b y) -
        (fun y => 2 * (rootKernel a y * rootKernel b y)) := by
    funext y
    simp only [Pi.sub_apply]
    rw [← rootKernel_square a y, ← rootKernel_square b y]
    ring
  rw [h]
  change (∫ y, (kernel a y + kernel b y) -
    2 * (rootKernel a y * rootKernel b y) ∂γ) = _
  have hi : Integrable (fun y => kernel a y + kernel b y) γ :=
    (kernel_integrable a).add (kernel_integrable b)
  rw [integral_sub hi ((overlap_integrable a b).const_mul 2),
    integral_add (kernel_integrable a) (kernel_integrable b),
    integral_const_mul, kernel_integral, kernel_integral, overlap_integral]
  ring

theorem distance_square_positive (a b : ℝ) (hab : a ≠ b) :
    0 < ∫ y, (rootKernel a y-rootKernel b y)^2 ∂γ := by
  rw [distance_square_integral]
  have h := fiber_mean_lt_one (a-b) (sub_ne_zero.mpr hab)
  linarith

end OperatorDerivativeRewrite.Foundation.GaussianLikelihoodRootOverlap
