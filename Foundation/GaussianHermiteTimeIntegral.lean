import Foundation.GaussianBrownianPRP
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Genuine deterministic-time integration of known predictable Hermite fields.
These are Bochner integrals in the original predictable Hilbert space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianHermiteTimeIntegral
open InfiniteGaussian GaussianTimeSpaceHermite GaussianHermiteStochasticSums
open GaussianHermiteRepresentation GaussianHermiteIntegrand GaussianPredictableFull
open GaussianPredictableAdjoint
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe

theorem hermiteIntegrand_continuous (n : ℕ) : Continuous (hermiteIntegrand n) := by
  exact predictableAdjoint.continuous.comp
    ((continuous_const : Continuous (fun _ : ℝ≥0 => (n + 1 : ℝ)⁻¹)).smul
      (brownianCore_continuous (n + 1)))

theorem hermite_time_integrable (q : ℝ → ℝ) (hq : Continuous q) (n : ℕ) (T : ℝ≥0) :
    IntervalIntegrable (fun t => q t • hermiteIntegrand n t.toNNReal) volume 0 T :=
  (hq.smul ((hermiteIntegrand_continuous n).comp continuous_real_toNNReal)).intervalIntegrable _ _

theorem core_time_integrable (q : ℝ → ℝ) (hq : Continuous q) (n : ℕ) (T : ℝ≥0) :
    IntervalIntegrable (fun t => q t • (brownianCore t.toNNReal n : GaussianL2)) volume 0 T :=
  (hq.smul ((brownianCore_continuous n).comp continuous_real_toNNReal)).intervalIntegrable _ _

def integratedHermite (q : ℝ → ℝ) (n : ℕ) (T : ℝ≥0) : fullPredictable :=
  ∫ t in 0..(T : ℝ), q t • hermiteIntegrand n t.toNNReal

theorem integral_integratedHermite (q : ℝ → ℝ) (hq : Continuous q) (n : ℕ) (T : ℝ≥0) :
    itoIntegral (integratedHermite q n T) =
      (n + 1 : ℝ)⁻¹ • ∫ t in 0..(T : ℝ), q t • (brownianCore t.toNNReal (n + 1) : GaussianL2) := by
  change itoIntegral.toContinuousLinearMap (∫ t in 0..(T : ℝ), q t • hermiteIntegrand n t.toNNReal) = _
  rw [← itoIntegral.toContinuousLinearMap.intervalIntegral_comp_comm
    (hermite_time_integrable q hq n T), ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro t _
  change itoIntegral (q t • hermiteIntegrand n t.toNNReal) = _
  rw [map_smul, integral_hermiteIntegrand, smul_comm]

theorem integratedHermite_zero_horizon (q : ℝ → ℝ) (n : ℕ) :
    integratedHermite q n 0 = 0 := by simp [integratedHermite]

end OperatorDerivativeRewrite.Foundation.GaussianHermiteTimeIntegral
