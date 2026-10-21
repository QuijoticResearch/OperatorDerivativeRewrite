import Foundation.EvenEntireCanonicalApproximation
import Foundation.RiemannQuadraticDivisor

/-! Actual quadratic Xi canonical remainders and finite rational zero products.
All analytic/growth/normalization hypotheses are discharged. Convergence is local
uniform convergence on the whole complex plane, along expanding real radii.
These products are not yet real polynomial approximants. -/
noncomputable section
open Set Metric Filter Complex MeromorphicOn
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuadraticCanonical
open RiemannEvenFlow RiemannQuadraticDivisor

def inverseZeroProduct (t R : ℝ) : ℂ → ℂ :=
  EvenEntireCanonicalApproximation.inverseZeroProduct (flow 1 t) R

theorem exists_actual_locally_uniform_remainders (t : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ r : ℝ → ℝ, ∃ h g : ℝ → ℂ → ℂ,
      (∀ R : ℝ, 1 ≤ R → 2*R < r R ∧ r R < 2*R+1 ∧
        divisor (flow 1 t) (sphere 0 (r R)) = 0 ∧
        ECanonicalDecomp (flow 1 t) (h R) (r R) ∧
        DifferentiableOn ℂ (g R) (ball 0 (r R)) ∧ g R 0 = 0 ∧ deriv (g R) 0 = 0 ∧
        (∀ z ∈ ball (0 : ℂ) (r R), HasDerivAt (g R) (deriv (h R) z / h R z) z) ∧
        (∀ z ∈ ball (0 : ℂ) (r R), Complex.exp (g R z) = h R z / h R 0) ∧
        ∀ z ∈ ball (0 : ℂ) (2*R), (g R z).re ≤ A+6*(R*Real.sqrt R)) ∧
      TendstoLocallyUniformly g (fun _ => 0) atTop ∧
      TendstoLocallyUniformly (fun R z => Complex.exp (g R z)) (fun _ => 1) atTop ∧
      TendstoLocallyUniformly (fun R z => h R z / h R 0) (fun _ => 1) atTop := by
  exact EvenEntireCanonicalApproximation.exists_locally_uniform_remainders (flow 1 t)
    (RiemannQuadraticDivisor.flow_analytic t) (flow_origin_ne_zero t)
    (RiemannEvenEvolution.flow_even 1 t)
    (RiemannEvenEntireGrowth.exists_subquadratic_growth 1 t)

theorem exists_actual_product_approximation (t : ℝ) :
    ∃ r : ℝ → ℝ, ∃ h : ℝ → ℂ → ℂ,
      (∀ R : ℝ, 1 ≤ R → 2*R < r R ∧ r R < 2*R+1 ∧
        ECanonicalDecomp (flow 1 t) (h R) (r R) ∧
        divisor (flow 1 t) (sphere 0 (r R)) = 0 ∧
        inverseZeroProduct t (r R) 0 ≠ 0 ∧
        ∀ z ∈ closedBall (0 : ℂ) (r R),
          (flow 1 t) z = inverseZeroProduct t (r R) z * h R z) ∧
      TendstoLocallyUniformly
        (fun R z => inverseZeroProduct t (r R) z / inverseZeroProduct t (r R) 0)
        (fun z => (flow 1 t) z / (flow 1 t) 0) atTop ∧
      TendstoLocallyUniformly
        (fun R z => (flow 1 t) 0 * (inverseZeroProduct t (r R) z / inverseZeroProduct t (r R) 0))
        (flow 1 t) atTop := by
  exact EvenEntireCanonicalApproximation.exists_product_approximation (flow 1 t)
    (RiemannQuadraticDivisor.flow_analytic t) (flow_origin_ne_zero t)
    (RiemannEvenEvolution.flow_even 1 t)
    (RiemannEvenEntireGrowth.exists_subquadratic_growth 1 t)

end OperatorDerivativeRewrite.Foundation.RiemannQuadraticCanonical
