import Foundation.EvenEntireCanonicalDerivative
import Foundation.RiemannEvenEntireGrowth

/-! Actual quadratic Xi multiplicity counts and finite canonical disk remainders.
The hypotheses of the extracted entire-function machinery are discharged by
verified positivity, analyticity and growth. No real-zero assumption is used. -/
noncomputable section
open Set Metric Filter Complex MeromorphicOn
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuadraticDivisor
open RiemannEvenFlow

def zeroCount (t R : ℝ) : ℤ := EntireSubquadraticZeroCounting.zeroCount (flow 1 t) R

theorem flow_analytic (t : ℝ) : AnalyticOnNhd ℂ (flow 1 t) univ :=
  (flow_differentiable 1 t).differentiableOn.analyticOnNhd isOpen_univ

theorem flow_origin_ne_zero (t : ℝ) : flow 1 t 0 ≠ 0 :=
  ne_of_apply_ne Complex.re (ne_of_gt (RiemannEvenNormalizedCompact.actual_flow_zero_pos 1 t))

theorem zero_order_finite (t : ℝ) (z : ℂ) : meromorphicOrderAt (flow 1 t) z ≠ ⊤ :=
  EntireSubquadraticZeroCounting.zero_order_finite (flow 1 t) (flow_analytic t)
    (flow_origin_ne_zero t) z

theorem zeros_in_closedBall_finite (t R : ℝ) :
    (closedBall (0 : ℂ) R ∩ (flow 1 t) ⁻¹' {0}).Finite :=
  EntireSubquadraticZeroCounting.zeros_in_closedBall_finite (flow 1 t) (flow_analytic t)
    (flow_origin_ne_zero t) R

theorem zeroCount_nonneg (t R : ℝ) : 0 ≤ zeroCount t R :=
  EntireSubquadraticZeroCounting.zeroCount_nonneg (flow 1 t) (flow_analytic t) R

theorem zeroCount_subquadratic_bound (t : ℝ) :
    ∃ K : ℝ, 0<K ∧ ∀ R : ℝ, 1≤R → (zeroCount t R : ℝ) ≤ K*(R*Real.sqrt R) :=
  EntireSubquadraticZeroCounting.zeroCount_subquadratic_bound (flow 1 t) (flow_analytic t)
    (flow_origin_ne_zero t) (RiemannEvenEntireGrowth.exists_subquadratic_growth 1 t)

theorem normalized_zeroCount_tendsto_zero (t : ℝ) :
    Tendsto (fun R : ℝ => (zeroCount t R : ℝ)/R^2) atTop (𝓝 0) :=
  EntireSubquadraticZeroCounting.normalized_zeroCount_tendsto_zero (flow 1 t) (flow_analytic t)
    (flow_origin_ne_zero t) (RiemannEvenEntireGrowth.exists_subquadratic_growth 1 t)

theorem weighted_zero_mass_bound (t R : ℝ) (hR : 0<R) :
    0 ≤ (∑ᶠ z : ℂ, (divisor (flow 1 t) (closedBall 0 R) z : ℝ)*‖z‖^2/R^4) ∧
      (∑ᶠ z : ℂ, (divisor (flow 1 t) (closedBall 0 R) z : ℝ)*‖z‖^2/R^4) ≤
        (zeroCount t R : ℝ)/R^2 :=
  EntireSubquadraticZeroCounting.weighted_zero_mass_bound (flow 1 t) (flow_analytic t) R hR

theorem weighted_zero_mass_tendsto_zero (t : ℝ) :
    Tendsto (fun R : ℝ =>
      ∑ᶠ z : ℂ, (divisor (flow 1 t) (closedBall 0 R) z : ℝ)*‖z‖^2/R^4) atTop (𝓝 0) :=
  EntireSubquadraticZeroCounting.weighted_zero_mass_tendsto_zero (flow 1 t) (flow_analytic t)
    (flow_origin_ne_zero t) (RiemannEvenEntireGrowth.exists_subquadratic_growth 1 t)

theorem exists_disk_log_remainder (t R : ℝ) (hR : 0≤R) :
    ∃ r : ℝ, R<r ∧ r<R+1 ∧ divisor (flow 1 t) (sphere 0 r)=0 ∧
      ∃ h g : ℂ → ℂ, ECanonicalDecomp (flow 1 t) h r ∧
        DifferentiableOn ℂ g (ball 0 r) ∧ g 0=0 ∧
        (∀ z ∈ ball (0 : ℂ) r, HasDerivAt g (deriv h z/h z) z) ∧
        ∀ z ∈ ball (0 : ℂ) r, Complex.exp (g z)=h z/h 0 :=
  EntireDiskDecomposition.exists_disk_log_remainder (flow 1 t) (flow_analytic t)
    (flow_origin_ne_zero t) R hR

theorem exists_zero_derivative_log_remainder (t R : ℝ) (hR : 0≤R) :
    ∃ r : ℝ, R<r ∧ r<R+1 ∧ divisor (flow 1 t) (sphere 0 r)=0 ∧
      ∃ h g : ℂ → ℂ, ECanonicalDecomp (flow 1 t) h r ∧
        DifferentiableOn ℂ g (ball 0 r) ∧ g 0=0 ∧ deriv g 0=0 ∧
        (∀ z ∈ ball (0 : ℂ) r, HasDerivAt g (deriv h z/h z) z) ∧
        ∀ z ∈ ball (0 : ℂ) r, Complex.exp (g z)=h z/h 0 :=
  EvenEntireCanonicalDerivative.exists_zero_derivative_log_remainder (flow 1 t)
    (flow_analytic t) (flow_origin_ne_zero t) (RiemannEvenEvolution.flow_even 1 t) R hR

end OperatorDerivativeRewrite.Foundation.RiemannQuadraticDivisor
