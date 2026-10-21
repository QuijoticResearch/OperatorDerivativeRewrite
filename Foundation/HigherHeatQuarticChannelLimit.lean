import Foundation.HigherHeatQuarticRemainder
import Foundation.HigherHeatQuadraticItoFields

/-! Actual quartic signed sums converge in the completed analytic dual norm.
The coefficient bound and genuine L1 field convergence are explicit. -/
noncomputable section
open scoped NNReal ENNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatQuarticChannelLimit
open Filter HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain
open HigherHeatWeakTimeAdjoint HigherHeatDyadicStepAgreement HigherHeatAdaptedStepDuality
open HigherHeatCompletedPairing HigherHeatPairedDualCausality HigherHeatFourthChannelSteps
open HigherHeatQuarticRemainder HigherHeatQuarticStepIdentity HigherHeatQuadraticItoFields

def quarticPolynomial (n : ℕ) (F : Fin (size n) → Test n) : Test n :=
  ∑ j, F j * (MvPolynomial.X j)^4

def remainder (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (F : Fin (size n) → Test n) : Dual := ∑ j, cellRemainder n T hT j (F j)

theorem quartic_sum_identity (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (F : Fin (size n) → Test n) (hF : Adapted F) :
    pairing 2 (by norm_num) T hT (core (cylinderOf n (quarticPolynomial n F))) =
      remainder n T hT F + fourthChannel T (adaptedField n 2 (by norm_num) T hT F) := by
  simp only [quarticPolynomial, remainder, adaptedField, map_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j _ => quartic_step_dual n T hT j (F j) (adapted_missing hF j))

theorem remainder_bound (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (F : Fin (size n) → Test n) (hF : Adapted F) (M : ℝ)
    (hM : ∀ j, ‖pairing 2 (by norm_num) T hT (core (cylinderOf n (F j)))‖ ≤ M) :
    ‖remainder n T hT F‖ ≤
      (816*(T:ℝ)^2*(HigherHeatDyadicLaws.duration 1 n:ℝ) +
        1152*(T:ℝ)^3*(HigherHeatDyadicLaws.duration 1 n:ℝ)^2 +
        256*(T:ℝ)^4*(HigherHeatDyadicLaws.duration 1 n:ℝ)^3)*M := by
  calc
    _ ≤ ∑ j, ‖cellRemainder n T hT j (F j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin (size n),
        (816*(T:ℝ)^2*(HigherHeatDyadicLaws.duration 1 n:ℝ)^2 +
          1152*(T:ℝ)^3*(HigherHeatDyadicLaws.duration 1 n:ℝ)^3 +
        256*(T:ℝ)^4*(HigherHeatDyadicLaws.duration 1 n:ℝ)^4)*M := by
      apply Finset.sum_le_sum
      intro j _
      exact (cell_remainder_bound n T hT j (F j) (adapted_missing hF j)).trans
        (mul_le_mul_of_nonneg_left (hM j) (by positivity))
    _ = (size n:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ)*
        (816*(T:ℝ)^2*(HigherHeatDyadicLaws.duration 1 n:ℝ) +
          1152*(T:ℝ)^3*(HigherHeatDyadicLaws.duration 1 n:ℝ)^2 +
        256*(T:ℝ)^4*(HigherHeatDyadicLaws.duration 1 n:ℝ)^3)*M := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ = _ := by rw [HigherHeatQuadraticChannelLimit.size_duration]; ring

theorem remainder_tendsto (T : ℝ≥0) (hT : 0 < T)
    (F : ∀ n, Fin (size n) → Test n) (hF : ∀ n, Adapted (F n)) (M : ℝ)
    (hM : ∀ n j, ‖pairing 2 (by norm_num) T hT (core (cylinderOf n (F n j)))‖ ≤ M) :
    Tendsto (fun n => remainder n T hT (F n)) atTop (𝓝 (0:Dual)) := by
  apply (tendsto_zero_iff_norm_tendsto_zero (E := Dual)).mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => remainder_bound n T hT (F n) (hF n) M (hM n))
  have hd := HigherHeatEarlyDualContinuity.duration_tendsto 1
  have hp := (((tendsto_const_nhds (x := 816*(T:ℝ)^2)).mul hd).add
    ((tendsto_const_nhds (x := 1152*(T:ℝ)^3)).mul (hd.pow 2))).add
    ((tendsto_const_nhds (x := 256*(T:ℝ)^4)).mul (hd.pow 3))
  simpa using hp.mul (tendsto_const_nhds (x := M))

theorem quartic_sums_converge (T : ℝ≥0) (hT : 0 < T)
    (F : ∀ n, Fin (size n) → Test n) (hF : ∀ n, Adapted (F n)) (M : ℝ)
    (hM : ∀ n j, ‖pairing 2 (by norm_num) T hT (core (cylinderOf n (F n j)))‖ ≤ M)
    (A : Field timeMeasure)
    (hA : Tendsto (fun n => adaptedField n 2 (by norm_num) T hT (F n)) atTop (𝓝 A)) :
    Tendsto (fun n => pairing 2 (by norm_num) T hT (core (cylinderOf n (quarticPolynomial n (F n)))))
      atTop (𝓝 (fourthChannel T A)) := by
  let : ContinuousAdd Dual := (inferInstance : IsTopologicalAddGroup Dual).toContinuousAdd
  have hr := remainder_tendsto T hT F hF M hM
  have hi := ((fourthChannel T).continuous.tendsto A).comp hA
  have hsum := hr.add hi
  change Tendsto (fun n => remainder n T hT (F n) +
    fourthChannel T (adaptedField n 2 (by norm_num) T hT (F n))) atTop
      (𝓝 ((0:Dual) + fourthChannel T A)) at hsum
  have he : (fun n => remainder n T hT (F n) +
      fourthChannel T (adaptedField n 2 (by norm_num) T hT (F n))) =
      (fun n => pairing 2 (by norm_num) T hT (core (cylinderOf n (quarticPolynomial n (F n))))) :=
    funext (fun n => (quartic_sum_identity n T hT (F n) (hF n)).symm)
  rw [he] at hsum
  simpa only [zero_add] using hsum

theorem constant_quartic_sums_converge (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => pairing 2 (by norm_num) T hT
      (core (cylinderOf n (quarticPolynomial n (fun _ => 1))))) atTop
        (𝓝 (fourthChannel T (constantField 2 (by norm_num) T hT))) := by
  have hM (n : ℕ) (j : Fin (size n)) :
      ‖pairing 2 (by norm_num) T hT (core (cylinderOf n (1:Test n)))‖ ≤
        ‖pairing 2 (by norm_num) T hT (core (1:Cylinder))‖ := by rw [map_one]
  apply quartic_sums_converge T hT (fun _ _ => 1) HigherHeatQuadraticItoData.constants_adapted
    ‖pairing 2 (by norm_num) T hT (core (1:Cylinder))‖ hM
    (constantField 2 (by norm_num) T hT)
  simpa only [constants_field_eq] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => constantField 2 (by norm_num) T hT) atTop
      (𝓝 (constantField 2 (by norm_num) T hT)))

end OperatorDerivativeRewrite.Foundation.HigherHeatQuarticChannelLimit
