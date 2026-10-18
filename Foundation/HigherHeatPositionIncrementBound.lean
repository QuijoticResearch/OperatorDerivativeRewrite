import Foundation.HigherHeatEarlyDualContinuity

/-! Interval increment pairings controlled by actual elapsed time. -/
noncomputable section
open scoped NNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatPositionIncrementBound
open HigherHeatPolynomialCylinders HigherHeatPolynomialPathDomain HigherHeatAnalyticCylinderDomain
open HigherHeatCompletedPairing HigherHeatPositionPairedBound

theorem position_sub (n : ℕ) (r s : Fin (size n)) (hsr : s ≤ r) :
    positionPolynomial n r - positionPolynomial n s = ∑ j ∈ Finset.Ioc s r, MvPolynomial.X j := by
  classical
  have hf (a : Fin (size n)) : Finset.univ.filter (fun j => j ≤ a) = Finset.Iic a := by ext j; simp
  have hd : Disjoint (Finset.Iic s) (Finset.Ioc s r) := by
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    have hjs := Finset.mem_Iic.mp hj
    have hsj := (Finset.mem_Ioc.mp hj').1
    exact (not_lt_of_ge hjs) hsj
  rw [positionPolynomial, positionPolynomial, hf, hf, ← Finset.Iic_union_Ioc_eq_Iic hsr,
    Finset.sum_union hd, add_sub_cancel_left]

theorem increment_pair_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (r s : Fin (size n)) (hsr : s ≤ r) (P : Test n) :
    |pairing m hm T hT (core (positionCylinder n r)-core (positionCylinder n s))
      (core (cylinderOf n P))| ≤
      ((2*m:ℕ):ℝ) * ((r.val-s.val:ℕ):ℝ) * (HigherHeatDyadicLaws.duration T n:ℝ) *
        Real.exp (T:ℝ) * ‖core (cylinderOf n P)‖ := by
  classical
  have he : core (positionCylinder n r)-core (positionCylinder n s) =
      core (cylinderOf n (positionPolynomial n r-positionPolynomial n s)) := by
    rw [map_sub, map_sub]
    rfl
  rw [he, position_sub n r s hsr]
  simp only [map_sum, sum_apply]
  calc
    _ ≤ ∑ j ∈ Finset.Ioc s r,
        |pairing m hm T hT (core (cylinderOf n (MvPolynomial.X j))) (core (cylinderOf n P))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.Ioc s r, ((2*m:ℕ):ℝ) * (HigherHeatDyadicLaws.duration T n:ℝ) *
        Real.exp (T:ℝ) * ‖core (cylinderOf n P)‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact coordinate_pair_bound n m hm T hT j P
    _ = _ := by
      simp only [Finset.sum_const, Fin.card_Ioc, nsmul_eq_mul]
      ring

end OperatorDerivativeRewrite.Foundation.HigherHeatPositionIncrementBound
