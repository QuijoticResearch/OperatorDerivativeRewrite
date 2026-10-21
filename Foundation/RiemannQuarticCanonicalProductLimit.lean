import Foundation.EvenEntireCanonicalApproximation
import Foundation.RiemannQuarticCanonicalReconstruction
import Mathlib.Analysis.Normed.Field.Lemmas

/-! Actual finite canonical products approximate the quartic transform
locally uniformly. These are analytic rational products on expanding
disks; conversion to real split polynomials remains a separate obligation. -/
noncomputable section
open Set Metric Filter Complex MeromorphicOn
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticCanonicalProductLimit
open RiemannQuarticFlow RiemannQuarticCanonicalReconstruction

theorem exists_actual_product_approximation (t : ℝ) :
    ∃ r : ℝ → ℝ, ∃ h : ℝ → ℂ → ℂ,
      (∀ R : ℝ, 1 ≤ R → 2*R < r R ∧ r R < 2*R+1 ∧
        ECanonicalDecomp (flow t) (h R) (r R) ∧
        divisor (flow t) (sphere 0 (r R)) = 0 ∧
        inverseZeroProduct t (r R) 0 ≠ 0 ∧
        ∀ z ∈ closedBall (0 : ℂ) (r R),
          flow t z = inverseZeroProduct t (r R) z * h R z) ∧
      TendstoLocallyUniformly
        (fun R z => inverseZeroProduct t (r R) z / inverseZeroProduct t (r R) 0)
        (fun z => flow t z / flow t 0) atTop ∧
      TendstoLocallyUniformly
        (fun R z => flow t 0 * (inverseZeroProduct t (r R) z / inverseZeroProduct t (r R) 0))
        (flow t) atTop := by
  exact EvenEntireCanonicalApproximation.exists_product_approximation
    (flow t) (RiemannQuarticZeroCounting.flow_analytic t)
    (by simpa using RiemannQuarticReality.flow_ne_zero_on_imaginary_axis t 0)
    (RiemannQuarticEvolution.flow_even t)
    (RiemannQuarticEntireGrowth.exists_subquadratic_growth t)

end OperatorDerivativeRewrite.Foundation.RiemannQuarticCanonicalProductLimit
