import Foundation.HigherHeatRefinementDegree

/-! A degree-dependent, grid-independent paired-dual generator estimate for
actual signed conditional increments. No source-norm time continuity is claimed. -/
noncomputable section
open scoped NNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatConditionalCellBound
open HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain HigherHeatCompletedPairing
open HigherHeatPairedDualCausality HigherHeatPredictableJetBounds HigherHeatPredictableJetFields
open HigherHeatDyadicConditioning HigherHeatMultitimeJetTelescope HigherHeatPredictableJetDegree
open HigherHeatInnovationMoments HigherHeatAllPowerBounds

theorem positive_moment_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, |cellMoment n m T (r+1)| ≤
      C*(HigherHeatDyadicLaws.duration 1 n:ℝ) := by
  rcases lt_trichotomy (r+1) (2*m) with hl | he | hg
  · refine ⟨0, le_rfl, ?_⟩
    intro n
    rw [low_moment_zero n m hm T (r+1) (by omega) hl]
    simp
  · refine ⟨|((2*m).factorial:ℝ)*(-1:ℝ)^(m+1)*(T:ℝ)|, abs_nonneg _, ?_⟩
    intro n
    rw [he, moment_order n m hm T, abs_mul,
      abs_of_nonneg (HigherHeatDyadicLaws.duration 1 n).coe_nonneg]
  · obtain ⟨C, hC, hc⟩ := higher_moment_bound m hm T (r+1) hg
    refine ⟨C, hC, fun n => (hc n).trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ hC
    have h := duration_le_one n
    have hn := (HigherHeatDyadicLaws.duration 1 n).coe_nonneg
    nlinarith

theorem positive_cell_identity (n m : ℕ) (hm : 0 < m) (T : ℝ≥0)
    (j : Fin (size n)) (P : Test n) (D : ℕ) (hD : P.totalDegree ≤ D) :
    nextConditioned n m T j P-localProjection m T n (initialPast n j.val) P =
      ∑ r ∈ Finset.range D, predictableJet n m T j (r+1) P *
        ((MvPolynomial.X j)^(r+1)-MvPolynomial.C (cellMoment n m T (r+1))) := by
  rw [cell_identity n m hm T j P]
  have he : (∑ q ∈ Finset.range (P.totalDegree+1), predictableJet n m T j q P *
      ((MvPolynomial.X j)^q-MvPolynomial.C (cellMoment n m T q))) =
      ∑ q ∈ Finset.range (D+1), predictableJet n m T j q P *
        ((MvPolynomial.X j)^q-MvPolynomial.C (cellMoment n m T q)) := by
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hD))
    intro q _ hq
    have h : P.totalDegree < q := by simp only [Finset.mem_range] at hq; omega
    rw [jet_zero_above_degree n m T j q P h, zero_mul]
  rw [he, Finset.sum_range_succ']
  simp only [pow_zero, cellMoment, PseudoPolynomialStein.moment_zero,
    MvPolynomial.C_1, sub_self, mul_zero, add_zero]

theorem centered_cell_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (hF : j ∉ F.vars) (r : ℕ) (C : ℝ)
    (hC : |cellMoment n m T (r+1)| ≤ C*(HigherHeatDyadicLaws.duration 1 n:ℝ)) :
    ‖pairing m hm T hT (core (cylinderOf n
      (F*((MvPolynomial.X j)^(r+1)-MvPolynomial.C (cellMoment n m T (r+1))))))‖ ≤
      (powerConstant m T (r+1)+C)*(HigherHeatDyadicLaws.duration 1 n:ℝ)*
        ‖pairing m hm T hT (core (cylinderOf n F))‖ := by
  have hs : F*MvPolynomial.C (cellMoment n m T (r+1)) =
      cellMoment n m T (r+1) • F := by rw [MvPolynomial.smul_eq_C_mul, mul_comm]
  rw [mul_sub, map_sub, map_sub, map_sub]
  apply (norm_sub_le _ _).trans
  rw [hs, map_smul, map_smul, map_smul, norm_smul, Real.norm_eq_abs]
  exact (add_le_add (positive_increment_bound n m hm T hT j F hF r)
    (mul_le_mul_of_nonneg_right hC (norm_nonneg _))).trans_eq (by ring)

theorem conditional_cell_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (D : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n (j : Fin (size n)) (P : Test n), P.totalDegree ≤ D →
      ‖pairing m hm T hT (core (cylinderOf n
        (nextConditioned n m T j P-localProjection m T n (initialPast n j.val) P)))‖ ≤
        K*(HigherHeatDyadicLaws.duration 1 n:ℝ)*‖core (cylinderOf n P)‖ := by
  choose C hC hc using (fun r => positive_moment_bound m hm T r)
  let K : ℝ := ∑ r ∈ Finset.range D,
    (powerConstant m T (r+1)+C r)*‖pairing m hm T hT‖*
      ((r+1).factorial:ℝ)⁻¹*Real.exp (T:ℝ)
  refine ⟨K, Finset.sum_nonneg (fun r _ => by
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (add_nonneg (powerConstant_nonneg m T (r+1)) (hC r)) (norm_nonneg _))
      (by positivity)) (Real.exp_pos _).le), ?_⟩
  intro n j P hD
  rw [positive_cell_identity n m hm T j P D hD, map_sum, map_sum, map_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ r ∈ Finset.range D,
        ((powerConstant m T (r+1)+C r)*‖pairing m hm T hT‖*
          ((r+1).factorial:ℝ)⁻¹*Real.exp (T:ℝ))*
            (HigherHeatDyadicLaws.duration 1 n:ℝ)*‖core (cylinderOf n P)‖ := by
      apply Finset.sum_le_sum
      intro r _
      have ha : j ∉ (predictableJet n m T j (r+1) P).vars := by
        intro hj
        exact (HigherHeatPredictableJetFields.predictable_jets_adapted n m T (r+1) P
          j j hj).false
      exact ((centered_cell_bound n m hm T hT j _ ha r (C r) (hc r n)).trans
        (mul_le_mul_of_nonneg_left (jet_dual_bound n m hm T hT j (r+1) P)
          (mul_nonneg (add_nonneg (powerConstant_nonneg m T (r+1)) (hC r))
            (HigherHeatDyadicLaws.duration 1 n).coe_nonneg))).trans_eq (by ring)
    _ = _ := by dsimp [K]; rw [Finset.sum_mul, Finset.sum_mul]

end OperatorDerivativeRewrite.Foundation.HigherHeatConditionalCellBound
