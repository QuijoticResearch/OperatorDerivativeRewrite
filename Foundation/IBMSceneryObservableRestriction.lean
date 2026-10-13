import Foundation.ObservableCoreDensity
import Foundation.FractionalGaussianOperators
import Foundation.IBMSourceLaws

/-! A concrete source-factor instance of abstract observable restriction:
positive-time Brownian scenery coordinates (the H=1/2 spectral source).
This is not the sigma-algebra of iterated Brownian motion. -/
noncomputable section
open Set
open scoped NNReal

namespace OperatorDerivativeRewrite.Foundation.IBMSceneryObservableRestriction
open InfiniteGaussian FractionalGaussianOperators ObservableRestriction

private theorem half_pos : (0 : ℝ) < 1 / 2 := by norm_num
private theorem half_lt_one : (1 / 2 : ℝ) < 1 := by norm_num

abbrev positiveScenerySpace : Submodule ℝ GaussianL2 :=
  scalarSpace (1 / 2) half_pos half_lt_one


/-- The positive-time coordinates are exactly those of the already verified
two-sided IBM scenery source, not merely equal in law. -/
theorem positiveScenery_coordinate (t : ℝ≥0) :
    IBMSourceLaws.sceneryBase (t : ℝ) =
      FractionalGaussianProcess.process (1 / 2) half_pos half_lt_one t := rfl
/-- The abstract restricted derivative is the repository's already
constructed closed Gaussian observable derivative for positive-time
Brownian scenery. -/
theorem derivative_eq_existing :
    derivative closedCylindricalDerivative positiveScenerySpace =
      FractionalGaussianOperators.derivative (1 / 2) half_pos half_lt_one := rfl

/-- This concrete Brownian scenery observable domain is dense, using the
independently verified Gaussian polynomial graph core. -/
theorem derivative_dense :
    Dense ((derivative closedCylindricalDerivative positiveScenerySpace).domain :
      Set positiveScenerySpace) := by
  rw [derivative_eq_existing]
  exact FractionalGaussianOperators.derivative_dense_domain (1 / 2) half_pos half_lt_one

/-- Closedness holds for the actual Gaussian source derivative restricted
to the positive-time scenery observable subspace. -/
theorem derivative_closed :
    (derivative closedCylindricalDerivative positiveScenerySpace).IsClosed :=
  derivative_isClosed _ _ closedCylindricalDerivative_isClosed

end OperatorDerivativeRewrite.Foundation.IBMSceneryObservableRestriction

