import Foundation.HigherHeatEarlyDualContinuity

/-! Native position cylinders and normalized sample times agree on arbitrary finer grids. -/
noncomputable section
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.HigherHeatDyadicPositionRefinement
open HigherHeatPolynomialCylinders HigherHeatPolynomialPathDomain HigherHeatAnalyticCylinderDomain
open HigherHeatAnalyticTimeObstruction HigherHeatCausalTimeObstruction
open HigherHeatCompletedCausalProjection HigherHeatCylindricalConditioning
open HigherHeatContinuousCylinders HigherHeatEarlyDualContinuity

theorem position_fine (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (r : Fin (size n)) (k : ℕ) (hn : n ≤ k) :
    positionCylinder n r = positionCylinder k (endpoint n r k hn) := by
  have he := algebraic_terminal m hm T hT n r
  rw [HigherHeatTerminalPositions.terminal_on_grid k,
    dyadicProjection_apply m hm T hT n (r.val+1) k hn] at he
  have hc : (endpoint n r k hn).val+1 = (r.val+1)*2^(k-n) := endpoint_count n r k hn
  rw [← hc, HigherHeatTerminalPositions.localProjection_terminal k m hm T hT] at he
  exact he.symm

theorem sampleTime_fine (n : ℕ) (r : Fin (size n)) (k : ℕ) (hn : n ≤ k) :
    sampleTime k (endpoint n r k hn) = sampleTime n r := by
  let ω : HigherHeatPolynomialPathDomain.Path := ⟨⟨id, continuous_id⟩, rfl⟩
  have hp := congrArg (fun F => HigherHeatPolynomialPathDomain.realize F ω)
    (position_fine 1 (by norm_num) 1 (by norm_num) n r k hn)
  simp only [realize_position, coordinate] at hp
  change sampleTime n r = sampleTime k (endpoint n r k hn) at hp
  exact hp.symm

theorem sampleTime_formula (n : ℕ) (r : Fin (size n)) :
    sampleTime n r = ((r.val+1:ℕ):ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ) := by
  simp only [sampleTime, HigherHeatDyadicLaws.time, NNReal.coe_mul, NNReal.coe_natCast]

theorem duration_scale (T : ℝ≥0) (n : ℕ) :
    (HigherHeatDyadicLaws.duration T n:ℝ) = (T:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ) := by
  simp only [HigherHeatDyadicLaws.duration, NNReal.coe_div, NNReal.coe_one]
  ring

theorem elapsed_time (T : ℝ≥0) (n : ℕ) (r s : Fin (size n)) (hsr : s ≤ r) :
    ((r.val-s.val:ℕ):ℝ)*(HigherHeatDyadicLaws.duration T n:ℝ) =
      (T:ℝ)*(sampleTime n r - sampleTime n s) := by
  have hv : s.val ≤ r.val := hsr
  rw [Nat.cast_sub hv, sampleTime_formula, sampleTime_formula, duration_scale]
  push_cast
  ring

end OperatorDerivativeRewrite.Foundation.HigherHeatDyadicPositionRefinement
