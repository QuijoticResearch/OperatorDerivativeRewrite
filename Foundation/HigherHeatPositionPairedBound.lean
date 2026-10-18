import Foundation.MultivariateConditionalStein
import Foundation.HigherHeatPositionSteinDerivative
import Foundation.HigherHeatCompletedPairing
import Foundation.HigherHeatPolynomialPathDomain
import Mathlib.Order.Interval.Finset.Fin

/-! Actual signed position pairings bounded by physical elapsed time, uniformly in grid level. -/
noncomputable section
open scoped NNReal BigOperators

namespace OperatorDerivativeRewrite.Foundation.HigherHeatPositionPairedBound
open HigherHeatPolynomialCylinders HigherHeatPolynomialPathDomain HigherHeatAnalyticCylinderDomain
open HigherHeatCompletedPairing HigherHeatCompletedSignedMean HigherHeatPolynomialCoordinates
open MultivariateConditionalStein HigherHeatPositionSteinDerivative MultivariateFactorialDomain
open PureOrderPolynomialConditioning

theorem core_iterate_bound (n : ℕ) (j : Fin (size n)) (r : ℕ) (P : Test n) :
    ‖core (cylinderOf n ((polynomialDerivative (Pi.single j 1) : Test n → Test n)^[r] P))‖ ≤
      ‖core (cylinderOf n P)‖ := by
  simp only [core_norm, cylinderSeminorm_grid]
  exact encode_iterate_bound n j r P

theorem coordinate_pair_stein (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (P : Test n) :
    pairing m hm T hT (core (cylinderOf n (MvPolynomial.X j))) (core (cylinderOf n P)) =
      (((2*m:ℕ):ℝ)*parameters m (fun _ => HigherHeatDyadicLaws.duration T n) j) *
      mean m hm T hT (core (cylinderOf n
        ((polynomialDerivative (Pi.single j 1) : Test n → Test n)^[2*m-1] P))) := by
  rw [pairing_core_real, ← map_mul (cylinderOf n), cylindricalExpectation_apply,
    mean_core_real, cylindricalExpectation_apply]
  change (HigherHeatMultivariateMoments.mean m hm _ _ (MvPolynomial.X j * P)).re = _
  have he := congrArg Complex.re (actual_coordinate_stein m hm
    (fun _ : Fin (size n) => HigherHeatDyadicLaws.duration T n)
    (fun _ => HigherHeatDyadicLaws.duration_pos T hT n) j P)
  simpa only [HigherHeatPolynomialCylinders.expectation, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] using he

theorem coordinate_pair_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (P : Test n) :
    |pairing m hm T hT (core (cylinderOf n (MvPolynomial.X j))) (core (cylinderOf n P))| ≤
      ((2*m:ℕ):ℝ) * (HigherHeatDyadicLaws.duration T n:ℝ) * Real.exp (T:ℝ) *
        ‖core (cylinderOf n P)‖ := by
  rw [coordinate_pair_stein, abs_mul]
  have ha : |((2*m:ℕ):ℝ)*parameters m
      (fun _ : Fin (size n) => HigherHeatDyadicLaws.duration T n) j| =
        ((2*m:ℕ):ℝ)*(HigherHeatDyadicLaws.duration T n:ℝ) := by
    simp [parameters, abs_mul, abs_pow, abs_of_nonneg (HigherHeatDyadicLaws.duration T n).coe_nonneg]
  rw [ha]
  calc
    _ ≤ ((2*m:ℕ):ℝ) * (HigherHeatDyadicLaws.duration T n:ℝ) *
      (Real.exp (T:ℝ) * ‖core (cylinderOf n
        ((polynomialDerivative (Pi.single j 1) : Test n → Test n)^[2*m-1] P))‖) :=
      mul_le_mul_of_nonneg_left (mean_bound m hm T hT _) (by positivity)
    _ ≤ _ := by
      have hd := core_iterate_bound n j (2*m-1) P
      have he := mul_le_mul_of_nonneg_left hd
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg (2*m))
          (HigherHeatDyadicLaws.duration T n).coe_nonneg) (Real.exp_pos (T:ℝ)).le)
      simpa only [mul_assoc] using he

theorem position_pair_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (r : Fin (size n)) (P : Test n) :
    |pairing m hm T hT (core (positionCylinder n r)) (core (cylinderOf n P))| ≤
      ((2*m:ℕ):ℝ) * ((r.val+1:ℕ):ℝ) * (HigherHeatDyadicLaws.duration T n:ℝ) *
        Real.exp (T:ℝ) * ‖core (cylinderOf n P)‖ := by
  classical
  have hs : Finset.univ.filter (fun j : Fin (size n) => j ≤ r) = Finset.Iic r := by
    ext j
    simp
  simp only [positionCylinder, positionPolynomial, hs, map_sum, sum_apply]
  calc
    _ ≤ ∑ j ∈ Finset.Iic r,
        |pairing m hm T hT (core (cylinderOf n (MvPolynomial.X j))) (core (cylinderOf n P))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.Iic r, ((2*m:ℕ):ℝ) * (HigherHeatDyadicLaws.duration T n:ℝ) *
        Real.exp (T:ℝ) * ‖core (cylinderOf n P)‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact coordinate_pair_bound n m hm T hT j P
    _ = _ := by
      simp only [Finset.sum_const, Fin.card_Iic, nsmul_eq_mul]
      push_cast
      ring

end OperatorDerivativeRewrite.Foundation.HigherHeatPositionPairedBound
