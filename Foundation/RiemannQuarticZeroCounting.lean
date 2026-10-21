import Foundation.RiemannQuarticZeroFreeRigidity
import Foundation.EntireSubquadraticZeroCounting

/-! Multiplicity counts for the actual quartic flow. Jensen's inequality
and the proved growth estimate give a subquadratic count at every real
time, without assuming that the zeros are real or simple. -/
noncomputable section
open Set Metric Filter Complex MeromorphicOn
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticZeroCounting
open RiemannQuarticFlow RiemannQuarticReality

def zeroCount (t R : ℝ) : ℤ :=
  ∑ᶠ z, divisor (flow t) (closedBall 0 R) z

theorem flow_analytic (t : ℝ) : AnalyticOnNhd ℂ (flow t) univ :=
  (flow_differentiable t).differentiableOn.analyticOnNhd isOpen_univ

theorem flow_zero_order_finite (t : ℝ) (z : ℂ) :
    meromorphicOrderAt (flow t) z ≠ ⊤ := by
  exact EntireSubquadraticZeroCounting.zero_order_finite
    (flow t) (flow_analytic t)
    (by simpa using flow_ne_zero_on_imaginary_axis t 0) z

theorem zeros_in_closedBall_finite (t R : ℝ) :
    (closedBall (0 : ℂ) R ∩ (flow t) ⁻¹' {0}).Finite := by
  exact EntireSubquadraticZeroCounting.zeros_in_closedBall_finite
    (flow t) (flow_analytic t)
    (by simpa using flow_ne_zero_on_imaginary_axis t 0) R

theorem zeroCount_nonneg (t R : ℝ) : 0 ≤ zeroCount t R := by
  exact EntireSubquadraticZeroCounting.zeroCount_nonneg
    (flow t) (flow_analytic t) R

theorem zeroCount_subquadratic_bound (t : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 1 ≤ R →
      (zeroCount t R : ℝ) ≤ K * (R * Real.sqrt R) := by
  exact EntireSubquadraticZeroCounting.zeroCount_subquadratic_bound
    (flow t) (flow_analytic t)
    (by simpa using flow_ne_zero_on_imaginary_axis t 0)
    (RiemannQuarticEntireGrowth.exists_subquadratic_growth t)

theorem normalized_zeroCount_tendsto_zero (t : ℝ) :
    Tendsto (fun R : ℝ => (zeroCount t R : ℝ) / R^2) atTop (𝓝 0) := by
  exact EntireSubquadraticZeroCounting.normalized_zeroCount_tendsto_zero
    (flow t) (flow_analytic t)
    (by simpa using flow_ne_zero_on_imaginary_axis t 0)
    (RiemannQuarticEntireGrowth.exists_subquadratic_growth t)

theorem weighted_zero_mass_bound (t R : ℝ) (hR : 0 < R) :
    0 ≤ (∑ᶠ z : ℂ, (divisor (flow t) (closedBall 0 R) z : ℝ) * ‖z‖^2 / R^4) ∧
    (∑ᶠ z : ℂ, (divisor (flow t) (closedBall 0 R) z : ℝ) * ‖z‖^2 / R^4) ≤
      (zeroCount t R : ℝ) / R^2 := by
  exact EntireSubquadraticZeroCounting.weighted_zero_mass_bound
    (flow t) (flow_analytic t) R hR

theorem weighted_zero_mass_tendsto_zero (t : ℝ) :
    Tendsto (fun R : ℝ =>
      ∑ᶠ z : ℂ, (divisor (flow t) (closedBall 0 R) z : ℝ) * ‖z‖^2 / R^4)
      atTop (𝓝 0) := by
  exact EntireSubquadraticZeroCounting.weighted_zero_mass_tendsto_zero
    (flow t) (flow_analytic t)
    (by simpa using flow_ne_zero_on_imaginary_axis t 0)
    (RiemannQuarticEntireGrowth.exists_subquadratic_growth t)

end OperatorDerivativeRewrite.Foundation.RiemannQuarticZeroCounting
