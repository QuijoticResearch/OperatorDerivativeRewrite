import Foundation.HigherHeatAllChannelNormalization

/-! Every surviving signed power channel has a quadratic mesh remainder. -/
noncomputable section
open scoped NNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatAllChannelRemainder
open HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain HigherHeatCompletedPairing
open HigherHeatWeakTimeAdjoint HigherHeatDyadicStepAgreement HigherHeatAllProductChannels
open HigherHeatAllPowerSteps HigherHeatAllPowerBounds HigherHeatAllChannelNormalization
open HigherHeatPairedDualCausality

def cellRemainder (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (r : ℕ) : Dual :=
  ∑ k ∈ Finset.range r, r.descFactorial k • productChannel m T k
    (coefficientField n m hm T hT j (F*(MvPolynomial.X j)^(r-k)))

theorem power_step_split (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (hF : j ∉ F.vars) (r : ℕ) (hr : r < 2*m) :
    pairing m hm T hT (core (cylinderOf n (F*(MvPolynomial.X j)^(r+1)))) =
      cellRemainder n m hm T hT j F r + channel m T r (coefficientField n m hm T hT j F) := by
  rw [power_step_dual n m hm T hT j F hF r]
  have hs : (∑ k ∈ Finset.range (2*m), r.descFactorial k • productChannel m T k
      (coefficientField n m hm T hT j (F*(MvPolynomial.X j)^(r-k)))) =
      ∑ k ∈ Finset.range (r+1), r.descFactorial k • productChannel m T k
        (coefficientField n m hm T hT j (F*(MvPolynomial.X j)^(r-k))) := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro k hk hk'
    have hkr : r < k := by simp only [Finset.mem_range] at hk hk'; omega
    simp only [Nat.descFactorial_of_lt hkr, zero_nsmul]
  rw [hs, Finset.sum_range_succ]
  simp only [cellRemainder, Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one,
    channel, smul_apply]

theorem cell_remainder_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (hF : j ∉ F.vars) (r : ℕ) (hr : r < 2*m) :
    ‖cellRemainder n m hm T hT j F r‖ ≤
      powerConstant m T (r+1)*(HigherHeatDyadicLaws.duration 1 n:ℝ)^2*
        ‖pairing m hm T hT (core (cylinderOf n F))‖ := by
  unfold cellRemainder
  calc
    _ ≤ ∑ k ∈ Finset.range r, ‖r.descFactorial k • productChannel m T k
        (coefficientField n m hm T hT j (F*(MvPolynomial.X j)^(r-k)))‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range r, (r.descFactorial k:ℝ)*
        (((2*m:ℕ):ℝ)*(T:ℝ)*((2*m-1).choose k:ℝ)*
          ((powerConstant m T (r-k)*(HigherHeatDyadicLaws.duration 1 n:ℝ)*
            ‖pairing m hm T hT (core (cylinderOf n F))‖)*
              (HigherHeatDyadicLaws.duration 1 n:ℝ))) := by
      apply Finset.sum_le_sum
      intro k hk
      have he : r-k-1+1=r-k := by have := Finset.mem_range.mp hk; omega
      have h := positive_increment_bound n m hm T hT j F hF (r-k-1)
      rw [he] at h
      apply norm_nsmul_le.trans
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply (productChannel_step_bound n m hm T hT k j (F*(MvPolynomial.X j)^(r-k))).trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right h (HigherHeatDyadicLaws.duration 1 n).coe_nonneg
    _ ≤ ∑ k ∈ Finset.range (2*m), (r.descFactorial k:ℝ)*
        (((2*m:ℕ):ℝ)*(T:ℝ)*((2*m-1).choose k:ℝ)*
          ((powerConstant m T (r-k)*(HigherHeatDyadicLaws.duration 1 n:ℝ)*
            ‖pairing m hm T hT (core (cylinderOf n F))‖)*
              (HigherHeatDyadicLaws.duration 1 n:ℝ))) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_of_lt hr))
      intro k _ _
      have hc := powerConstant_nonneg m T (r-k)
      positivity
    _ = _ := by
      rw [powerConstant]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring

end OperatorDerivativeRewrite.Foundation.HigherHeatAllChannelRemainder
