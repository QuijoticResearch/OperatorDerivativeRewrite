import Foundation.HigherHeatDyadicPositionRefinement
import Foundation.HigherHeatPositionIncrementBound

/-! Grid-independent Lipschitz control of actual dyadic signed coordinate functionals. -/
noncomputable section
open scoped NNReal

namespace OperatorDerivativeRewrite.Foundation.HigherHeatDyadicDualLipschitz
open HigherHeatPolynomialCylinders HigherHeatPolynomialPathDomain HigherHeatAnalyticCylinderDomain
open HigherHeatCompletedPairing HigherHeatPositionIncrementBound HigherHeatDyadicPositionRefinement
open HigherHeatCylindricalConditioning HigherHeatContinuousCylinders HigherHeatCompletedCausalProjection
open HigherHeatPairedDualCausality

theorem sampleTime_mono (n : ℕ) : Monotone (sampleTime n) := by
  intro s r hsr
  rw [sampleTime_formula, sampleTime_formula]
  apply mul_le_mul_of_nonneg_right _ (HigherHeatDyadicLaws.duration 1 n).coe_nonneg
  exact_mod_cast Nat.succ_le_succ hsr

theorem grid_pair_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (r s : Fin (size n)) (P : Test n) :
    |pairing m hm T hT (core (positionCylinder n r)-core (positionCylinder n s))
      (core (cylinderOf n P))| ≤
      ((2*m:ℕ):ℝ) * (T:ℝ) * Real.exp (T:ℝ) * |sampleTime n r-sampleTime n s| *
        ‖core (cylinderOf n P)‖ := by
  have ho (r s : Fin (size n)) (hsr : s ≤ r) :
      |pairing m hm T hT (core (positionCylinder n r)-core (positionCylinder n s))
        (core (cylinderOf n P))| ≤
        ((2*m:ℕ):ℝ) * (T:ℝ) * Real.exp (T:ℝ) * |sampleTime n r-sampleTime n s| *
          ‖core (cylinderOf n P)‖ := by
    have hb := increment_pair_bound n m hm T hT r s hsr P
    calc
      _ ≤ ((2*m:ℕ):ℝ) * (((r.val-s.val:ℕ):ℝ)*(HigherHeatDyadicLaws.duration T n:ℝ)) *
        Real.exp (T:ℝ) * ‖core (cylinderOf n P)‖ := by simpa only [mul_assoc] using hb
      _ = _ := by
        rw [elapsed_time T n r s hsr, abs_of_nonneg (sub_nonneg.mpr (sampleTime_mono n hsr))]
        ring
  rcases le_total s r with hsr | hrs
  · exact ho r s hsr
  · have hb := ho s r hrs
    rw [← neg_sub (core (positionCylinder n r)), map_neg, neg_apply, abs_neg, abs_sub_comm] at hb
    exact hb

theorem same_grid_core_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (r s : Fin (size n)) (F : Cylinder) :
    |pairing m hm T hT (core (positionCylinder n r)-core (positionCylinder n s)) (core F)| ≤
      ((2*m:ℕ):ℝ) * (T:ℝ) * Real.exp (T:ℝ) * |sampleTime n r-sampleTime n s| * ‖core F‖ := by
  apply tail_induction n (fun F =>
    |pairing m hm T hT (core (positionCylinder n r)-core (positionCylinder n s)) (core F)| ≤
      ((2*m:ℕ):ℝ) * (T:ℝ) * Real.exp (T:ℝ) * |sampleTime n r-sampleTime n s| * ‖core F‖) _ F
  intro k hn P
  rw [position_fine m hm T hT n r k hn, position_fine m hm T hT n s k hn]
  have hb := grid_pair_bound k m hm T hT (endpoint n r k hn) (endpoint n s k hn) P
  simpa only [sampleTime_fine] using hb

theorem same_grid_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (r s : Fin (size n)) (v : Domain) :
    |pairing m hm T hT (core (positionCylinder n r)-core (positionCylinder n s)) v| ≤
      ((2*m:ℕ):ℝ) * (T:ℝ) * Real.exp (T:ℝ) * |sampleTime n r-sampleTime n s| * ‖v‖ := by
  refine core_dense.induction_on v ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro F
    exact same_grid_core_bound n m hm T hT r s F

theorem position_pair_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (r : Fin (size n)) (l : ℕ) (s : Fin (size l)) (v : Domain) :
    |pairing m hm T hT (core (positionCylinder n r)-core (positionCylinder l s)) v| ≤
      ((2*m:ℕ):ℝ) * (T:ℝ) * Real.exp (T:ℝ) * |sampleTime n r-sampleTime l s| * ‖v‖ := by
  rw [position_fine m hm T hT n r (max n l) (Nat.le_max_left n l),
    position_fine m hm T hT l s (max n l) (Nat.le_max_right n l)]
  have hb := same_grid_bound (max n l) m hm T hT
    (endpoint n r (max n l) (Nat.le_max_left n l))
    (endpoint l s (max n l) (Nat.le_max_right n l)) v
  simpa only [sampleTime_fine] using hb

def dualPosition (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (r : Fin (size n)) : Dual := pairing m hm T hT (core (positionCylinder n r))

theorem dualPosition_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (r : Fin (size n)) (l : ℕ) (s : Fin (size l)) :
    ‖dualPosition m hm T hT n r-dualPosition m hm T hT l s‖ ≤
      ((2*m:ℕ):ℝ) * (T:ℝ) * Real.exp (T:ℝ) * |sampleTime n r-sampleTime l s| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hb := position_pair_bound m hm T hT n r l s v
  simpa only [dualPosition, map_sub, sub_apply, Real.norm_eq_abs] using hb

end OperatorDerivativeRewrite.Foundation.HigherHeatDyadicDualLipschitz
