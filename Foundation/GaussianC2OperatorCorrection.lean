import Foundation.GaussianC2Ito
import Foundation.GaussianSmoothConditional
import Foundation.GaussianQuadraticCylinders

/-! Corrected operator interpretation of C2 Ito: the terminal predictable
adjoint includes the projection of the drift. It is not the running derivative. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianC2OperatorCorrection
open InfiniteGaussian GaussianTimeProcess GaussianLipschitzIntegrands GaussianPredictableFull
open GaussianPredictableAdjoint GaussianConditionalIto GaussianConditionalClarkOcone
open GaussianC2Ito GaussianSmoothConditional GaussianPredictableCutoff

variable (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (K0 K1 : ℝ≥0)
  (h0 : ∀ x, ‖deriv f x‖₊ ≤ K0) (h1 : ∀ x, ‖deriv (deriv f) x‖₊ ≤ K1)

def drift (T : ℝ≥0) : GaussianL2 := ∫ t in 0..(T:ℝ), curvatureValue f hf K1 h1 t.toNNReal

theorem terminal_adjoint (T : ℝ≥0) :
    predictableAdjoint (valueL2 (functionLip f hf K0 h0) T) =
      integrand (derivativeLip f hf K1 h1) T +
        (1/2:ℝ) • predictableAdjoint (drift f hf K1 h1 T) := by
  have he := c2_ito f hf K0 K1 h0 h1 T
  have hp := congrArg predictableAdjoint he
  rw [map_sub, map_add, map_smul, predictableAdjoint_integral,
    GaussianSmoothIto.valueL2_zero, GaussianQuadraticCylinders.predictableAdjoint_constant, sub_zero] at hp
  exact hp

theorem projection_difference (T : ℝ≥0) :
    predictableAdjoint (valueL2 (functionLip f hf K0 h0) T) -
      integrand (derivativeLip f hf K1 h1) T =
        (1/2:ℝ) • predictableAdjoint (drift f hf K1 h1 T) := by
  rw [terminal_adjoint f hf K0 K1 h0 h1]
  abel

/-- Exact criterion for the invalid substitution to happen to hold. No such
criterion is assumed in the Ito theorem or in its proof. -/
theorem terminal_adjoint_eq_running_iff (T : ℝ≥0) :
    predictableAdjoint (valueL2 (functionLip f hf K0 h0) T) =
      integrand (derivativeLip f hf K1 h1) T ↔
        predictableAdjoint (drift f hf K1 h1 T) = 0 := by
  rw [← sub_eq_zero, projection_difference f hf K0 K1 h0 h1]
  exact smul_eq_zero_iff_right (by norm_num : (1/2:ℝ) ≠ 0)

/-- The conditional identity concerns the compensated process, not an
identification between its terminal derivative and a running coefficient. -/
theorem compensated_projection (S T : ℝ≥0) :
    pastProjection S (valueL2 (functionLip f hf K0 h0) T - (1/2:ℝ) • drift f hf K1 h1 T) =
      valueL2 (functionLip f hf K0 h0) (min S T) - (1/2:ℝ) • drift f hf K1 h1 (min S T) := by
  have he (R : ℝ≥0) : valueL2 (functionLip f hf K0 h0) R - (1/2:ℝ) • drift f hf K1 h1 R =
      f 0 • gaussianOne + itoIntegral (integrand (derivativeLip f hf K1 h1) R) := by
    have h := c2_ito f hf K0 K1 h0 h1 R
    rw [GaussianSmoothIto.valueL2_zero] at h
    change _ = _ + (1/2:ℝ) • drift f hf K1 h1 R at h
    linear_combination (norm := module) h
  rw [he T, he (min S T), map_add, map_smul, pastProjection_one,
    pastProjection_integral, cut_integrand]

/-- If the terminal variable is separately known to belong to the full closed
Malliavin domain, the established identification gives the same corrected
formula. Domain membership is explicit and is not asserted by this corollary. -/
theorem full_derivative_projection (T : ℝ≥0)
    (hdom : valueL2 (functionLip f hf K0 h0) T ∈ closedCylindricalDerivative.domain) :
    predictableProjection (closedCylindricalDerivative ⟨valueL2 (functionLip f hf K0 h0) T, hdom⟩) =
      integrand (derivativeLip f hf K1 h1) T +
        (1/2:ℝ) • predictableAdjoint (drift f hf K1 h1 T) := by
  rw [← predictableAdjoint_eq_projected_derivative]
  exact terminal_adjoint f hf K0 K1 h0 h1 T

end OperatorDerivativeRewrite.Foundation.GaussianC2OperatorCorrection
