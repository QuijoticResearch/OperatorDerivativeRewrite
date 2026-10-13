import Foundation.IBMContinuousMalliavin
import Foundation.IBMMollifier

/-! The repository's explicit normalized smooth bumps applied to genuine
Gaussian L² scenery, without a supplied continuous sample path. -/
noncomputable section
open MeasureTheory Filter
open scoped Convolution Topology

namespace OperatorDerivativeRewrite.Foundation.IBMContinuousScenery
open IBMMollifier InfiniteGaussian
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

/-- The explicit normalized compactly supported bump convolutions converge
to the verified Brownian scenery in Gaussian L² at every fixed spatial point. -/
theorem concreteMollifier_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ => wholeLineScenery (kernel n) x) atTop
      (𝓝 (sourceScenery x)) := by
  exact ContDiffBump.convolution_tendsto_right_of_continuous
    (φ := bump) bump_outer_tendsto_zero sourceScenery_continuous x

theorem concreteMollifier_support (n : ℕ) (x r : ℝ)
    (hr : r ∉ Set.Icc (x - (bump n).rOut) (x + (bump n).rOut)) :
    kernel n (x - r) = 0 := by
  by_contra hne
  have hmem : x - r ∈ Function.support (kernel n) := hne
  rw [show Function.support (kernel n) = Metric.ball 0 (bump n).rOut from
    (bump n).support_normed_eq] at hmem
  have hd : |x - r| < (bump n).rOut := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hmem
  have hrl : x - (bump n).rOut ≤ r := by
    have := (abs_lt.mp hd).2
    linarith
  have hru : r ≤ x + (bump n).rOut := by
    have := (abs_lt.mp hd).1
    linarith
  exact hr ⟨hrl, hru⟩

theorem concreteMollifier_mass (n : ℕ) (x : ℝ) :
    (∫ r in Set.Icc (x - (bump n).rOut) (x + (bump n).rOut),
      kernel n (x - r)) = 1 := by
  have hfull : (∫ r : ℝ, kernel n (x - r)) = 1 := by
    have hneg := integral_neg_eq_self (fun r : ℝ => kernel n (x + r)) volume
    have htrans := integral_add_left_eq_self (μ := volume) (kernel n) x
    simpa only [sub_eq_add_neg] using hneg.trans (htrans.trans (kernel_integral n))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun r hr => concreteMollifier_support n x r hr)]
  exact hfull

theorem concreteMollifier_radius (n : ℕ) (x r : ℝ)
    (hr : r ∈ Set.Icc (x - (bump n).rOut) (x + (bump n).rOut)) :
    |r - x| ≤ (bump n).rOut := by
  rw [abs_le]
  constructor <;> linarith [hr.1, hr.2]

/-- The original smooth normalized bump family has the quantitative source
Gaussian L² smoothing rate `rOut = 2/(n+1)`. -/
theorem concreteMollifier_error_sq_le (n : ℕ) (x : ℝ) :
    ‖wholeLineScenery (kernel n) x - sourceScenery x‖ ^ 2 ≤
      (bump n).rOut := by
  exact wholeLineScenery_error_sq_le (x - (bump n).rOut)
    (x + (bump n).rOut) x (bump n).rOut
    (kernel_smooth n).continuous (concreteMollifier_support n x)
    (concreteMollifier_mass n x)
    (fun r hr => kernel_nonneg n (x - r)) (bump n).rOut_pos.le
    (concreteMollifier_radius n x)

theorem concreteMollifier_error_fourth_le (n : ℕ) (x : ℝ) :
    (∫ ω, (GaussianHilbertProcess.isonormal FractionalSpectralKernel.SpectralSpace
      (kernelDirection (x - (bump n).rOut) (x + (bump n).rOut) x (kernel n) -
        IBMFiniteScenerySmoothing.direction x) ω)^4 ∂gaussianProduct) ≤
      3 * ((bump n).rOut)^2 := by
  exact kernelScenery_error_fourth_le (x - (bump n).rOut)
    (x + (bump n).rOut) x (bump n).rOut
    (kernel_smooth n).continuous (concreteMollifier_mass n x)
    (fun r hr => kernel_nonneg n (x - r)) (bump n).rOut_pos.le
    (concreteMollifier_radius n x)

theorem concreteMollifier_derivative_domain (n : ℕ) (x : ℝ) :
    wholeLineScenery (kernel n) x ∈ closedCylindricalDerivative.domain :=
  wholeLineScenery_derivative_domain (x - (bump n).rOut)
    (x + (bump n).rOut) x (kernel n) (concreteMollifier_support n x)

theorem concreteMollifier_source_derivative (n : ℕ) (x : ℝ)
    (hdom : wholeLineScenery (kernel n) x ∈ closedCylindricalDerivative.domain) :
    closedCylindricalDerivative ⟨wholeLineScenery (kernel n) x, hdom⟩ =
      Lp.const 2 gaussianProduct
        (kernelCoefficient (x - (bump n).rOut) (x + (bump n).rOut) x (kernel n)) :=
  wholeLineScenery_derivative_apply (x - (bump n).rOut)
    (x + (bump n).rOut) x (kernel n) (concreteMollifier_support n x) hdom

theorem concreteMollifier_spatial_deriv (n : ℕ) (x : ℝ) :
    deriv (wholeLineScenery (kernel n)) x =
      ∫ r, deriv (kernel n) (x - r) • sourceScenery r := by
  exact wholeLineScenery_deriv_integral (kernel n) (kernel_compactSupport n)
    ((kernel_smooth n).of_le (by simp)) x

theorem concreteMollifier_spatial_second_deriv (n : ℕ) (x : ℝ) :
    deriv (fun y => deriv (wholeLineScenery (kernel n)) y) x =
      ∫ r, deriv (deriv (kernel n)) (x - r) • sourceScenery r := by
  exact wholeLineScenery_second_deriv_integral (kernel n) (kernel_compactSupport n)
    ((kernel_smooth n).of_le (by simp)) x

end OperatorDerivativeRewrite.Foundation.IBMContinuousScenery
