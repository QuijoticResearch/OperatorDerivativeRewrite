import Foundation.HigherHeatFourierBracket
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Exact finite-time resonance covariance for actual higher-even-order signed kernels.
This uses the semigroup and the fundamental theorem of calculus, not a stochastic
Itô formula or an assumed Clark–Ocone representation. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.HigherHeatResonanceCovariance
open HigherHeatL2 HigherHeatGenerator HigherHeatFourierCovariance
open HigherHeatFourierBracket HigherHeatFourierInnovations HigherHeatSignedLaws

def density (m : ℕ) (T ξ η t : ℝ) : ℝ :=
  rate m ξ η * Real.exp (-t * weight m (ξ+η) - (T-t) * (weight m ξ+weight m η))

theorem density_continuous (m : ℕ) (T ξ η : ℝ) : Continuous (density m T ξ η) := by
  unfold density
  fun_prop

theorem covariance_integral (m : ℕ) (T ξ η : ℝ) :
    realCovariance m T ξ η = ∫ t in 0..T, density m T ξ η t := by
  let f : ℝ → ℝ := fun t =>
    Real.exp (-t * weight m (ξ+η) - (T-t) * (weight m ξ+weight m η))
  have hd (t : ℝ) : HasDerivAt f (density m T ξ η t) t := by
    have h := ((((hasDerivAt_id t).neg.mul_const (weight m (ξ+η))).sub
      (((hasDerivAt_const t T).sub (hasDerivAt_id t)).mul_const
        (weight m ξ+weight m η))).exp)
    convert h using 1 <;> simp [f, density, rate] <;> ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((density_continuous m T ξ η).intervalIntegrable 0 T)
  rw [hi]
  simp only [f, realCovariance, sub_self, zero_mul, sub_zero]
  rw [← Real.exp_add]
  congr 2
  ring

theorem actual_kernel_covariance (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (ξ η : ℝ) :
    (∫ z : ℝ, (innovation m T ξ z * innovation m T η z) *
      (realKernel m hm T hT z : ℂ)) =
      ((∫ t in 0..(T : ℝ), density m T ξ η t) : ℝ) := by
  rw [kernel_product, covariance_eq, covariance_integral]

theorem fourth_order_density (T ξ η t : ℝ) :
    density 2 T ξ η t =
      (-(2*Real.pi)^4 * (4*ξ^3*η+6*ξ^2*η^2+4*ξ*η^3)) *
        Real.exp (-t * weight 2 (ξ+η) - (T-t) * (weight 2 ξ+weight 2 η)) := by
  rw [density, fourth_order_rate]

end OperatorDerivativeRewrite.Foundation.HigherHeatResonanceCovariance
