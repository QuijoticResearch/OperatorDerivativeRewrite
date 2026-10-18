import Foundation.HigherHeatPositionPairedBound
import Foundation.HigherHeatCausalTimeObstruction
import Foundation.HigherHeatPairedDualCausality

/-! Genuine paired-dual time convergence for the actual early conditional terminal observable.
This does not assert continuity of the whole causal family in cut time. -/
noncomputable section
open scoped NNReal

namespace OperatorDerivativeRewrite.Foundation.HigherHeatEarlyDualContinuity
open HigherHeatPolynomialCylinders HigherHeatPolynomialPathDomain HigherHeatAnalyticCylinderDomain
open HigherHeatAnalyticTimeObstruction HigherHeatCausalTimeObstruction
open HigherHeatCompletedCausalProjection HigherHeatCylindricalConditioning
open HigherHeatCompletedPairing HigherHeatPairedDualCausality HigherHeatPositionPairedBound
open Filter
open scoped Topology

theorem firstPosition_fine (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n k : ℕ) (hn : n ≤ k) :
    firstPosition n = positionCylinder k (endpoint n (firstIndex n) k hn) := by
  have he := algebraic_terminal m hm T hT n (firstIndex n)
  rw [HigherHeatTerminalPositions.terminal_on_grid k,
    dyadicProjection_apply m hm T hT n ((firstIndex n).val+1) k hn] at he
  have hc : (endpoint n (firstIndex n) k hn).val+1 =
      ((firstIndex n).val+1)*2^(k-n) := endpoint_count n (firstIndex n) k hn
  rw [← hc,
    HigherHeatTerminalPositions.localProjection_terminal k m hm T hT] at he
  exact he.symm

theorem endpoint_duration (T : ℝ≥0) (n k : ℕ) (hn : n ≤ k) :
    (((endpoint n (firstIndex n) k hn).val+1:ℕ):ℝ) * (HigherHeatDyadicLaws.duration T k:ℝ) =
      (HigherHeatDyadicLaws.duration T n:ℝ) := by
  have hp : (size k:ℝ) = (size n:ℝ)*(2:ℝ)^(k-n) := by
    simp only [size, HigherHeatDyadicLaws.gridSize_pow, Nat.cast_pow, Nat.cast_ofNat]
    rw [← pow_add, Nat.add_sub_of_le hn]
  simp only [endpoint_count, cutCount, firstIndex, zero_add, one_mul,
    Nat.cast_pow, Nat.cast_ofNat, HigherHeatDyadicLaws.duration,
    NNReal.coe_div, NNReal.coe_natCast]
  change (2:ℝ)^(k-n) * ((T:ℝ)/(size k:ℝ)) = (T:ℝ)/(size n:ℝ)
  rw [hp]
  field_simp


theorem first_pair_core_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (F : Cylinder) :
    |pairing m hm T hT (core (firstPosition n)) (core F)| ≤
      ((2*m:ℕ):ℝ) * (HigherHeatDyadicLaws.duration T n:ℝ) * Real.exp (T:ℝ) * ‖core F‖ := by
  apply tail_induction n (fun F =>
    |pairing m hm T hT (core (firstPosition n)) (core F)| ≤
      ((2*m:ℕ):ℝ) * (HigherHeatDyadicLaws.duration T n:ℝ) * Real.exp (T:ℝ) * ‖core F‖) _ F
  intro k hn P
  rw [firstPosition_fine m hm T hT n k hn]
  have hb := position_pair_bound k m hm T hT (endpoint n (firstIndex n) k hn) P
  calc
    _ ≤ ((2*m:ℕ):ℝ) *
        ((((endpoint n (firstIndex n) k hn).val+1:ℕ):ℝ) * (HigherHeatDyadicLaws.duration T k:ℝ)) *
          Real.exp (T:ℝ) * ‖core (cylinderOf k P)‖ := by simpa only [mul_assoc] using hb
    _ = _ := by rw [endpoint_duration T n k hn]

theorem first_pair_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (v : Domain) :
    |pairing m hm T hT (core (firstPosition n)) v| ≤
      ((2*m:ℕ):ℝ) * (HigherHeatDyadicLaws.duration T n:ℝ) * Real.exp (T:ℝ) * ‖v‖ := by
  refine core_dense.induction_on v ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro F
    exact first_pair_core_bound m hm T hT n F

theorem first_dual_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    dualSeminorm m hm T hT (core (firstPosition n)) ≤
      ((2*m:ℕ):ℝ) * (HigherHeatDyadicLaws.duration T n:ℝ) * Real.exp (T:ℝ) := by
  rw [dualSeminorm_apply]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  simpa only [Real.norm_eq_abs] using first_pair_bound m hm T hT n v

theorem duration_coe (T : ℝ≥0) (n : ℕ) :
    (HigherHeatDyadicLaws.duration T n:ℝ) = (T:ℝ)*(1/2:ℝ)^n := by
  simp only [HigherHeatDyadicLaws.duration, NNReal.coe_div]
  change (T:ℝ)/(HigherHeatDyadicLaws.gridSize n:ℝ) = _
  have hs : (HigherHeatDyadicLaws.gridSize n:ℝ) = (2:ℝ)^n := by
    exact_mod_cast HigherHeatDyadicLaws.gridSize_pow n
  rw [hs, div_pow, one_pow]
  ring

theorem duration_tendsto (T : ℝ≥0) :
    Tendsto (fun n => (HigherHeatDyadicLaws.duration T n:ℝ)) atTop (𝓝 0) := by
  simp only [duration_coe]
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  simpa only [mul_zero] using (tendsto_const_nhds (x := (T:ℝ))).mul hp

theorem first_dual_tendsto (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => dualSeminorm m hm T hT (core (firstPosition n))) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => by
    rw [dualSeminorm_apply]
    exact ContinuousLinearMap.opNorm_nonneg _) (first_dual_bound m hm T hT)
  simpa only [mul_zero, zero_mul] using
    ((tendsto_const_nhds (x := ((2*m:ℕ):ℝ))).mul (duration_tendsto T)).mul
      (tendsto_const_nhds (x := Real.exp (T:ℝ)))

theorem terminal_gap_dual_tendsto (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => dualSeminorm m hm T hT
      ((earlyProjection m hm T hT n - HigherHeatCompletedEmptyPast.emptyProjection m hm T hT)
        (core terminalCylinder))) atTop (𝓝 0) := by
  simp only [sub_apply, earlyProjection_terminal, empty_terminal_zero, sub_zero]
  exact first_dual_tendsto m hm T hT

theorem first_pairing_tendsto (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => pairing m hm T hT (core (firstPosition n))) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_norm_tendsto_zero (E := Dual)).mpr
  exact first_dual_tendsto m hm T hT

end OperatorDerivativeRewrite.Foundation.HigherHeatEarlyDualContinuity
