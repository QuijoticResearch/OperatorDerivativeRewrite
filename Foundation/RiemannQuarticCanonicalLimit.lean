import Foundation.EvenEntireCanonicalApproximation
import Foundation.RiemannQuarticCanonicalBounds

/-! Actual normalized zero-free canonical remainders converge locally
uniformly to one. The remaining zero-product and polynomial approximation
are not included in this theorem. -/
noncomputable section
open Set Metric Filter Complex MeromorphicOn
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticCanonicalLimit
open RiemannQuarticFlow RiemannQuarticCanonicalDerivative RiemannQuarticCanonicalBounds

theorem exists_actual_locally_uniform_remainders (t : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ r : ℝ → ℝ, ∃ h g : ℝ → ℂ → ℂ,
      (∀ R : ℝ, 1 ≤ R → 2*R < r R ∧ r R < 2*R+1 ∧
        divisor (flow t) (sphere 0 (r R)) = 0 ∧
        ECanonicalDecomp (flow t) (h R) (r R) ∧
        DifferentiableOn ℂ (g R) (ball 0 (r R)) ∧ g R 0 = 0 ∧ deriv (g R) 0 = 0 ∧
        (∀ z ∈ ball (0 : ℂ) (r R), HasDerivAt (g R) (deriv (h R) z / h R z) z) ∧
        (∀ z ∈ ball (0 : ℂ) (r R), Complex.exp (g R z) = h R z / h R 0) ∧
        ∀ z ∈ ball (0 : ℂ) (2*R), (g R z).re ≤ A+6*(R*Real.sqrt R)) ∧
      TendstoLocallyUniformly g (fun _ => 0) atTop ∧
      TendstoLocallyUniformly (fun R z => Complex.exp (g R z)) (fun _ => 1) atTop ∧
      TendstoLocallyUniformly (fun R z => h R z / h R 0) (fun _ => 1) atTop := by
  exact EvenEntireCanonicalApproximation.exists_locally_uniform_remainders
    (flow t) (RiemannQuarticZeroCounting.flow_analytic t)
    (by simpa using RiemannQuarticReality.flow_ne_zero_on_imaginary_axis t 0)
    (RiemannQuarticEvolution.flow_even t)
    (RiemannQuarticEntireGrowth.exists_subquadratic_growth t)

end OperatorDerivativeRewrite.Foundation.RiemannQuarticCanonicalLimit
