import Foundation.HigherHeatCompletedAffineSteps
import Foundation.HigherHeatEarlyDualContinuity

/-! Actual quadratic signed step sums converge to the complementary derivative channel
under explicit uniform coefficient bounds and genuine L1 field convergence. -/
noncomputable section
open scoped NNReal ENNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatQuadraticChannelLimit
open Filter HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain
open HigherHeatWeakTimeAdjoint HigherHeatDyadicStepAgreement HigherHeatAdaptedStepDuality
open HigherHeatCompletedPairing HigherHeatCompletedAffineSteps HigherHeatSecondChannelSteps
open HigherHeatPairedDualCausality

def quadraticPolynomial (n : ℕ) (F : Fin (size n) → Test n) : Test n :=
  ∑ j, F j * (MvPolynomial.X j)^2

def remainder (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (F : Fin (size n) → Test n) : Dual :=
  ∑ j, firstChannel m T (coefficientField n m hm T hT j (F j * MvPolynomial.X j))

theorem quadratic_sum_identity (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (F : Fin (size n) → Test n) (hF : Adapted F) :
    pairing m hm T hT (core (cylinderOf n (quadraticPolynomial n F))) =
      remainder n m hm T hT F + secondChannel m T (adaptedField n m hm T hT F) := by
  simp only [quadraticPolynomial, remainder, adaptedField, map_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j _ => quadratic_step_dual n m hm T hT j (F j) (adapted_missing hF j))

theorem size_duration (n : ℕ) :
    (size n:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ) = 1 := by
  have hn : (size n:ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast HigherHeatDyadicLaws.gridSize_pos n)
  simp only [HigherHeatDyadicLaws.duration, NNReal.coe_div, NNReal.coe_one, NNReal.coe_natCast]
  exact mul_one_div_cancel hn

theorem remainder_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (F : Fin (size n) → Test n) (hF : Adapted F) (M : ℝ)
    (hM : ∀ j, ‖pairing m hm T hT (core (cylinderOf n (F j)))‖ ≤ M) :
    ‖remainder n m hm T hT F‖ ≤
      (((2*m:ℕ):ℝ)*(T:ℝ))^2 * (HigherHeatDyadicLaws.duration 1 n:ℝ) * M := by
  calc
    _ ≤ ∑ j, ‖firstChannel m T (coefficientField n m hm T hT j (F j * MvPolynomial.X j))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : Fin (size n),
        ((((2*m:ℕ):ℝ)*(T:ℝ))*(HigherHeatDyadicLaws.duration 1 n:ℝ))^2 * M := by
      apply Finset.sum_le_sum
      intro j _
      exact (quadratic_remainder_bound n m hm T hT j (F j) (adapted_missing hF j)).trans
        (mul_le_mul_of_nonneg_left (hM j) (sq_nonneg _))
    _ = (((2*m:ℕ):ℝ)*(T:ℝ))^2 *
        ((size n:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ)) *
        (HigherHeatDyadicLaws.duration 1 n:ℝ) * M := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ = _ := by rw [size_duration]; ring

theorem remainder_tendsto (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (F : ∀ n, Fin (size n) → Test n) (hF : ∀ n, Adapted (F n)) (M : ℝ)
    (hM : ∀ n j, ‖pairing m hm T hT (core (cylinderOf n (F n j)))‖ ≤ M) :
    Tendsto (fun n => remainder n m hm T hT (F n)) atTop (𝓝 (0:Dual)) := by
  apply (tendsto_zero_iff_norm_tendsto_zero (E := Dual)).mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => remainder_bound n m hm T hT (F n) (hF n) M (hM n))
  simpa only [mul_zero, zero_mul] using
    ((tendsto_const_nhds (x := (((2*m:ℕ):ℝ)*(T:ℝ))^2)).mul
      (HigherHeatEarlyDualContinuity.duration_tendsto 1)).mul (tendsto_const_nhds (x := M))

theorem quadratic_sums_converge (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (F : ∀ n, Fin (size n) → Test n) (hF : ∀ n, Adapted (F n)) (M : ℝ)
    (hM : ∀ n j, ‖pairing m hm T hT (core (cylinderOf n (F n j)))‖ ≤ M)
    (A : HigherHeatAdaptedIntegralClosure.space m hm T hT)
    (hA : Tendsto (fun n => adaptedField n m hm T hT (F n)) atTop (𝓝 A.val)) :
    Tendsto (fun n => pairing m hm T hT (core (cylinderOf n (quadraticPolynomial n (F n)))))
      atTop (𝓝 (secondChannel m T A.val)) := by
  letI : ContinuousAdd Dual := (inferInstance : IsTopologicalAddGroup Dual).toContinuousAdd
  have hr := remainder_tendsto m hm T hT F hF M hM
  have hi := ((secondChannel m T).continuous.tendsto A.val).comp hA
  have hsum := hr.add hi
  change Tendsto (fun n => remainder n m hm T hT (F n) +
    secondChannel m T (adaptedField n m hm T hT (F n))) atTop
      (𝓝 ((0:Dual) + secondChannel m T A.val)) at hsum
  have he : (fun n => remainder n m hm T hT (F n) +
      secondChannel m T (adaptedField n m hm T hT (F n))) =
      (fun n => pairing m hm T hT (core (cylinderOf n (quadraticPolynomial n (F n))))) :=
    funext (fun n => (quadratic_sum_identity n m hm T hT (F n) (hF n)).symm)
  rw [he] at hsum
  simpa only [zero_add] using hsum

end OperatorDerivativeRewrite.Foundation.HigherHeatQuadraticChannelLimit
