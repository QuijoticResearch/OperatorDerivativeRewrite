import Foundation.HigherHeatAllPowerSteps

/-! Explicit nonnegative recursive bounds for signed increment powers.
These are operator norms, not positive moment or variation estimates. -/
noncomputable section
open scoped NNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatAllPowerBounds
open HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain HigherHeatCompletedPairing
open HigherHeatWeakTimeAdjoint HigherHeatWeakStepFields HigherHeatDyadicStepAgreement
open HigherHeatAllProductChannels HigherHeatAllPowerSteps HigherHeatPairedDualCausality

def powerConstant (m : ℕ) (T : ℝ≥0) : ℕ → ℝ
  | 0 => 1
  | r+1 => ((2*m:ℕ):ℝ)*(T:ℝ) * ∑ k ∈ Finset.range (2*m),
      ((2*m-1).choose k:ℝ) * (r.descFactorial k:ℝ) * powerConstant m T (r-k)
termination_by r => r

theorem powerConstant_nonneg (m : ℕ) (T : ℝ≥0) (r : ℕ) : 0 ≤ powerConstant m T r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => simp [powerConstant]
    | succ r =>
      rw [powerConstant]
      apply mul_nonneg (by positivity)
      apply Finset.sum_nonneg
      intro k _
      exact mul_nonneg (by positivity) (ih (r-k) (by omega))

theorem productChannel_step_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (k : ℕ) (j : Fin (size n)) (F : Test n) :
    ‖productChannel m T k (coefficientField n m hm T hT j F)‖ ≤
      ((2*m:ℕ):ℝ)*(T:ℝ)*((2*m-1).choose k:ℝ)*
        (‖pairing m hm T hT (core (cylinderOf n F))‖*(HigherHeatDyadicLaws.duration 1 n:ℝ)) := by
  simpa only [coefficientField, step_norm, gridCell_measure] using
    productChannel_bound m T k (coefficientField n m hm T hT j F)

theorem power_step_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (hF : j ∉ F.vars) (r : ℕ) :
    ‖pairing m hm T hT (core (cylinderOf n (F*(MvPolynomial.X j)^(r+1))))‖ ≤
      ∑ k ∈ Finset.range (2*m), (r.descFactorial k:ℝ)*
        (((2*m:ℕ):ℝ)*(T:ℝ)*((2*m-1).choose k:ℝ)*
          (‖pairing m hm T hT (core (cylinderOf n (F*(MvPolynomial.X j)^(r-k))))‖*
            (HigherHeatDyadicLaws.duration 1 n:ℝ))) := by
  rw [power_step_dual n m hm T hT j F hF r]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  exact norm_nsmul_le.trans (mul_le_mul_of_nonneg_left
    (productChannel_step_bound n m hm T hT k j (F*(MvPolynomial.X j)^(r-k)))
    (Nat.cast_nonneg _))

theorem duration_le_one (n : ℕ) : (HigherHeatDyadicLaws.duration 1 n:ℝ) ≤ 1 := by
  have hs : (1:ℝ) ≤ (size n:ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (HigherHeatDyadicLaws.gridSize_pos n))
  simp only [HigherHeatDyadicLaws.duration, NNReal.coe_div, NNReal.coe_one, NNReal.coe_natCast]
  exact (div_le_one (by positivity)).mpr hs

theorem uniform_increment_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (hF : j ∉ F.vars) (r : ℕ) :
    ‖pairing m hm T hT (core (cylinderOf n (F*(MvPolynomial.X j)^r)))‖ ≤
      powerConstant m T r * ‖pairing m hm T hT (core (cylinderOf n F))‖ := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => simp [powerConstant]
    | succ r =>
      have hh : ‖pairing m hm T hT (core (cylinderOf n (F*(MvPolynomial.X j)^(r+1))))‖ ≤
          powerConstant m T (r+1) * (HigherHeatDyadicLaws.duration 1 n:ℝ) *
            ‖pairing m hm T hT (core (cylinderOf n F))‖ := by
        calc
          _ ≤ _ := power_step_bound n m hm T hT j F hF r
          _ ≤ ∑ k ∈ Finset.range (2*m), (r.descFactorial k:ℝ)*
              (((2*m:ℕ):ℝ)*(T:ℝ)*((2*m-1).choose k:ℝ)*
                ((powerConstant m T (r-k)*‖pairing m hm T hT (core (cylinderOf n F))‖)*
                  (HigherHeatDyadicLaws.duration 1 n:ℝ))) := by
            apply Finset.sum_le_sum
            intro k _
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_right (ih (r-k) (by omega))
              (HigherHeatDyadicLaws.duration 1 n).coe_nonneg
          _ = _ := by
            rw [powerConstant]
            simp only [Finset.mul_sum, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k _
            ring
      exact hh.trans (mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right (powerConstant_nonneg m T (r+1)) (duration_le_one n))
        (norm_nonneg _))

theorem positive_increment_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (hF : j ∉ F.vars) (r : ℕ) :
    ‖pairing m hm T hT (core (cylinderOf n (F*(MvPolynomial.X j)^(r+1))))‖ ≤
      powerConstant m T (r+1) * (HigherHeatDyadicLaws.duration 1 n:ℝ) *
        ‖pairing m hm T hT (core (cylinderOf n F))‖ := by
  calc
    _ ≤ _ := power_step_bound n m hm T hT j F hF r
    _ ≤ ∑ k ∈ Finset.range (2*m), (r.descFactorial k:ℝ)*
        (((2*m:ℕ):ℝ)*(T:ℝ)*((2*m-1).choose k:ℝ)*
          ((powerConstant m T (r-k)*‖pairing m hm T hT (core (cylinderOf n F))‖)*
            (HigherHeatDyadicLaws.duration 1 n:ℝ))) := by
      apply Finset.sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right (uniform_increment_bound n m hm T hT j F hF (r-k))
        (HigherHeatDyadicLaws.duration 1 n).coe_nonneg
    _ = _ := by
      rw [powerConstant]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem higher_increment_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (hF : j ∉ F.vars) (r : ℕ) (hr : 2*m ≤ r) :
    ‖pairing m hm T hT (core (cylinderOf n (F*(MvPolynomial.X j)^(r+1))))‖ ≤
      powerConstant m T (r+1) * (HigherHeatDyadicLaws.duration 1 n:ℝ)^2 *
        ‖pairing m hm T hT (core (cylinderOf n F))‖ := by
  calc
    _ ≤ _ := power_step_bound n m hm T hT j F hF r
    _ ≤ ∑ k ∈ Finset.range (2*m), (r.descFactorial k:ℝ)*
        (((2*m:ℕ):ℝ)*(T:ℝ)*((2*m-1).choose k:ℝ)*
          ((powerConstant m T (r-k)*(HigherHeatDyadicLaws.duration 1 n:ℝ)*
            ‖pairing m hm T hT (core (cylinderOf n F))‖)*
              (HigherHeatDyadicLaws.duration 1 n:ℝ))) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have he : r-k-1+1=r-k := by omega
      have h := positive_increment_bound n m hm T hT j F hF (r-k-1)
      rw [he] at h
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right h (HigherHeatDyadicLaws.duration 1 n).coe_nonneg
    _ = _ := by
      rw [powerConstant]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring

end OperatorDerivativeRewrite.Foundation.HigherHeatAllPowerBounds
