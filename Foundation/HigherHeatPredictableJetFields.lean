import Foundation.HigherHeatPredictableJetIdentity
import Foundation.HigherHeatPolynomialPredictableField

/-! Actual adapted native jet fields and degree-independent L1 bounds. -/
noncomputable section
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatPredictableJetFields
open HigherHeatPolynomialCylinders HigherHeatPredictableJetBounds HigherHeatAnalyticCylinderDomain
open HigherHeatPolynomialCoordinates HigherHeatCompletedPairing HigherHeatPairedDualCausality
open HigherHeatWeakTimeAdjoint HigherHeatDyadicStepAgreement HigherHeatWeakStepFields
open HigherHeatAdaptedStepDuality

theorem clampBefore_X (n : ℕ) (j i : Fin (size n)) :
    clampBefore n j (MvPolynomial.X i) = if i < j then MvPolynomial.X i else 0 := by
  apply MvPolynomial.funext
  intro x
  rw [eval_clampBefore, MvPolynomial.eval_X]
  by_cases hi : i < j <;> simp [basePoint, hi]

theorem clampBefore_C (n : ℕ) (j : Fin (size n)) (c : ℝ) :
    clampBefore n j (MvPolynomial.C c) = MvPolynomial.C c := by
  change (clampBefore n j) (algebraMap ℝ (Test n) c) = algebraMap ℝ (Test n) c
  exact AlgHom.commutes _ _

theorem clampBefore_vars (n : ℕ) (j : Fin (size n)) (P : Test n) :
    ∀ i ∈ (clampBefore n j P).vars, i < j := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    intro i hi
    simp [clampBefore_C] at hi
  | add P Q hp hq =>
    intro i hi
    rw [map_add] at hi
    rcases Finset.mem_union.mp
      (MvPolynomial.vars_add_subset (clampBefore n j P) (clampBefore n j Q) hi) with hi | hi
    · exact hp i hi
    · exact hq i hi
  | mul_X P k hp =>
    intro i hi
    rw [map_mul, clampBefore_X] at hi
    by_cases hk : k < j
    · rw [if_pos hk] at hi
      rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hi) with hi | hi
      · exact hp i hi
      · have he : i=k := by simpa only [MvPolynomial.vars_X, Finset.mem_singleton] using hi
        simpa only [he] using hk
    · simp [hk] at hi

theorem predictable_jets_adapted (n m : ℕ) (T : ℝ≥0) (q : ℕ) (P : Test n) :
    Adapted (fun j => predictableJet n m T j q P) := by
  intro j i hi
  dsimp only [predictableJet] at hi
  rw [MvPolynomial.smul_eq_C_mul,
    MvPolynomial.vars_C_mul _ (by positivity : (q.factorial:ℝ)⁻¹ ≠ 0)] at hi
  exact clampBefore_vars n j _ i hi

theorem jet_core_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (q : ℕ) (P : Test n) :
    ‖core (cylinderOf n (predictableJet n m T j q P))‖ ≤
      (q.factorial:ℝ)⁻¹ * Real.exp (T:ℝ) * ‖core (cylinderOf n P)‖ := by
  simpa only [core_norm, cylinderSeminorm_grid] using predictable_jet_bound n m hm T hT j q P

theorem jet_dual_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (q : ℕ) (P : Test n) :
    ‖pairing m hm T hT (core (cylinderOf n (predictableJet n m T j q P)))‖ ≤
      ‖pairing m hm T hT‖*((q.factorial:ℝ)⁻¹ * Real.exp (T:ℝ)*‖core (cylinderOf n P)‖) := by
  exact ((pairing m hm T hT).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (jet_core_bound n m hm T hT j q P) (norm_nonneg _))

theorem native_field_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : ℕ) (P : Test n) :
    ‖adaptedField n m hm T hT (fun j => predictableJet n m T j q P)‖ ≤
      ‖pairing m hm T hT‖*((q.factorial:ℝ)⁻¹ * Real.exp (T:ℝ)*‖core (cylinderOf n P)‖) := by
  let M : ℝ := ‖pairing m hm T hT‖*((q.factorial:ℝ)⁻¹ * Real.exp (T:ℝ)*‖core (cylinderOf n P)‖)
  calc
    _ ≤ ∑ j, ‖coefficientField n m hm T hT j (predictableJet n m T j q P)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin (size n), M*(HigherHeatDyadicLaws.duration 1 n:ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [coefficientField, step_norm, gridCell_measure]
      exact mul_le_mul_of_nonneg_right (jet_dual_bound n m hm T hT j q P)
        (HigherHeatDyadicLaws.duration 1 n).coe_nonneg
    _ = M*((size n:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ = _ := by rw [HigherHeatQuadraticChannelLimit.size_duration, mul_one]

end OperatorDerivativeRewrite.Foundation.HigherHeatPredictableJetFields
