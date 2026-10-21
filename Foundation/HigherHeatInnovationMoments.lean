import Foundation.HigherHeatAllChannelLimit
import Foundation.PureOrderPolynomialInnovations

/-! Native signed innovation moments and exact identification of the drift channel. -/
noncomputable section
open scoped NNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatInnovationMoments
open HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain HigherHeatCompletedPairing
open HigherHeatWeakTimeAdjoint HigherHeatWeakStepFields HigherHeatDyadicStepAgreement
open HigherHeatPairedDualCausality HigherHeatAllChannelNormalization HigherHeatAllPowerBounds

def cellMoment (n m : ℕ) (T : ℝ≥0) (q : ℕ) : ℝ :=
  PseudoPolynomialStein.moment (2*m)
    ((-1:ℝ)^(m+1)*(HigherHeatDyadicLaws.duration T n:ℝ)) q

theorem low_moment_zero (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (q : ℕ)
    (hq : 0 < q) (hqp : q < 2*m) : cellMoment n m T q = 0 := by
  apply PseudoPolynomialStein.moment_off_order (2*m) (by omega)
  intro hd
  exact (Nat.le_of_dvd hq hd).not_gt hqp

theorem moment_order (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) :
    cellMoment n m T (2*m) =
      (((2*m).factorial:ℝ)*(-1:ℝ)^(m+1)*(T:ℝ))*(HigherHeatDyadicLaws.duration 1 n:ℝ) := by
  have h := PseudoPolynomialStein.moment_multiple (2*m) (by omega)
    ((-1:ℝ)^(m+1)*(HigherHeatDyadicLaws.duration T n:ℝ)) 1
  simp only [Nat.mul_one, pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h
  rw [cellMoment, h, ← duration_scale T n]
  ring

theorem drift_step (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) :
    channel m T (2*m-1) (coefficientField n m hm T hT j F) =
      cellMoment n m T (2*m) • pairing m hm T hT (core (cylinderOf n F)) := by
  rw [drift_normalization m hm T]
  apply ContinuousLinearMap.ext
  intro G
  change (((2*m).factorial:ℝ)*(-1:ℝ)^(m+1)*(T:ℝ))*
    transpose timeMeasure 0 (step _ _ _ _ _) G =
      cellMoment n m T (2*m) * pairing m hm T hT (core (cylinderOf n F)) G
  rw [transpose_step_constant timeMeasure 0 (gridCell n j)
    (gridCell_measurable n j) (gridCell_finite n j) _ G G
    (Filter.Eventually.of_forall (fun _ => rfl)), gridCell_measure, moment_order n m hm T]
  ring

theorem higher_moment_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (q : ℕ) (hq : 2*m < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, |cellMoment n m T q| ≤
      C*(HigherHeatDyadicLaws.duration 1 n:ℝ)^2 := by
  by_cases hd : 2*m ∣ q
  · obtain ⟨k, rfl⟩ := hd
    have hk : 2 ≤ k := by nlinarith
    obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le hk
    let C : ℝ := (((2*m*k).factorial:ℝ)*(T:ℝ)^k)/(k.factorial:ℝ)
    refine ⟨C, by positivity, ?_⟩
    intro n
    have h := PseudoPolynomialStein.moment_multiple (2*m) (by omega)
      ((-1:ℝ)^(m+1)*(HigherHeatDyadicLaws.duration T n:ℝ)) k
    rw [cellMoment, h]
    have he : |(((2*m*k).factorial:ℝ)*
        ((-1:ℝ)^(m+1)*(HigherHeatDyadicLaws.duration T n:ℝ))^k)/(k.factorial:ℝ)| =
        C*(HigherHeatDyadicLaws.duration 1 n:ℝ)^k := by
      simp only [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (Nat.cast_nonneg ((2*m*k).factorial) : (0:ℝ) ≤ _),
        abs_of_nonneg (Nat.cast_nonneg (k.factorial) : (0:ℝ) ≤ _),
        abs_of_nonneg (HigherHeatDyadicLaws.duration T n).coe_nonneg]
      rw [← duration_scale T n, mul_pow]
      dsimp [C]
      ring
    rw [he, hl, pow_add]
    have hp : (HigherHeatDyadicLaws.duration 1 n:ℝ)^l ≤ 1 :=
      pow_le_one₀ (HigherHeatDyadicLaws.duration 1 n).coe_nonneg (duration_le_one n)
    calc
      _ = (C*(HigherHeatDyadicLaws.duration 1 n:ℝ)^2)*
          (HigherHeatDyadicLaws.duration 1 n:ℝ)^l := by ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) hp
  · refine ⟨0, le_rfl, ?_⟩
    intro n
    rw [cellMoment, PseudoPolynomialStein.moment_off_order (2*m) (by omega) _ _ hd]
    simp

end OperatorDerivativeRewrite.Foundation.HigherHeatInnovationMoments
