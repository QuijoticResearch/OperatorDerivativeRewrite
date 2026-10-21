import Foundation.HigherHeatJetHeatCorrection
import Foundation.HigherHeatRefinedPredictableJets

/-! Actual L1 heat-correction errors along refinements of fixed multitime input.
Only the difference tends to zero; neither field is asserted to converge. -/
noncomputable section
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatJetCorrectionFields
open Filter MeasureTheory HigherHeatPolynomialCylinders HigherHeatPolynomialCoordinates
open HigherHeatAnalyticCylinderDomain HigherHeatCompletedPairing HigherHeatPairedDualCausality
open HigherHeatWeakTimeAdjoint HigherHeatWeakStepFields HigherHeatDyadicStepAgreement
open HigherHeatPredictableJetBounds HigherHeatRefinedPredictableJets HigherHeatJetHeatCorrection

theorem native_field_sub_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (F G : Fin (size n) → Test n) (M : ℝ)
    (hM : ∀ j, ‖pairing m hm T hT (core (cylinderOf n (F j - G j)))‖ ≤ M) :
    ‖adaptedField n m hm T hT F - adaptedField n m hm T hT G‖ ≤ M := by
  rw [adaptedField, adaptedField, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, ‖coefficientField n m hm T hT j (F j) -
      coefficientField n m hm T hT j (G j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin (size n), M*(HigherHeatDyadicLaws.duration 1 n:ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      simp only [coefficientField, HigherHeatWeakStepFields.step, indicatorConstLp_sub,
        ← map_sub]
      rw [← HigherHeatWeakStepFields.step, step_norm, gridCell_measure]
      exact mul_le_mul_of_nonneg_right (hM j) (HigherHeatDyadicLaws.duration 1 n).coe_nonneg
    _ = M*((size n:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ = M := by rw [HigherHeatQuadraticChannelLimit.size_duration, mul_one]

theorem refined_field_error_bound (b : ℕ) (P : Test b) (n m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (q : ℕ) (a : ℝ) :
    ‖adaptedField n m hm T hT (fun j => shiftedJet n m hm T j q a (refinedInput b P n)) -
      adaptedField n m hm T hT (fun j => predictableJet n m T j q (refinedInput b P n))‖ ≤
      ‖pairing m hm T hT‖*((q.factorial:ℝ)⁻¹*(Real.exp |a|-1)*
        Real.exp (T:ℝ)*‖core (cylinderOf b P)‖) := by
  apply native_field_sub_bound
  intro j
  have hc : ‖core (cylinderOf n
      (shiftedJet n m hm T j q a (refinedInput b P n) -
        predictableJet n m T j q (refinedInput b P n)))‖ ≤
      (q.factorial:ℝ)⁻¹*(Real.exp |a|-1)*Real.exp (T:ℝ)*
        ‖core (cylinderOf n (refinedInput b P n))‖ := by
    have h := shiftedJet_error n m hm T hT j q a (refinedInput b P n)
    rw [← map_sub] at h
    simpa only [core_norm, cylinderSeminorm_grid] using h
  apply ((pairing m hm T hT).le_opNorm _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact hc.trans (mul_le_mul_of_nonneg_left (refined_core_bound b P n)
    (by exact mul_nonneg (mul_nonneg (by positivity)
      (sub_nonneg.mpr (Real.one_le_exp (abs_nonneg a)))) (Real.exp_pos _).le))

theorem refined_field_error_vanish (b : ℕ) (P : Test b) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (q : ℕ) (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun n =>
      adaptedField n m hm T hT (fun j => shiftedJet n m hm T j q (a n) (refinedInput b P n)) -
      adaptedField n m hm T hT (fun j => predictableJet n m T j q (refinedInput b P n)))
      atTop (𝓝 (0:Field timeMeasure)) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => refined_field_error_bound b P n m hm T hT q (a n))
  have hab : Tendsto (fun n => |a n|) atTop (𝓝 (0:ℝ)) := by simpa using ha.abs
  have he := ((Real.continuous_exp.tendsto 0).comp hab).sub
    (tendsto_const_nhds (x := (1:ℝ)))
  simpa using (tendsto_const_nhds (x := ‖pairing m hm T hT‖)).mul
    (((tendsto_const_nhds (x := (q.factorial:ℝ)⁻¹)).mul he).mul
      (tendsto_const_nhds (x := Real.exp (T:ℝ))) |>.mul
        (tendsto_const_nhds (x := ‖core (cylinderOf b P)‖)))

theorem physical_cell_error_vanish (b : ℕ) (P : Test b) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (q : ℕ) :
    Tendsto (fun n =>
      adaptedField n m hm T hT (fun j => shiftedJet n m hm T j q
        ((-1:ℝ)^(m+1)*(HigherHeatDyadicLaws.duration T n:ℝ)) (refinedInput b P n)) -
      adaptedField n m hm T hT (fun j => predictableJet n m T j q (refinedInput b P n)))
      atTop (𝓝 (0:Field timeMeasure)) := by
  apply refined_field_error_vanish
  simpa using (tendsto_const_nhds (x := (-1:ℝ)^(m+1))).mul
    (HigherHeatEarlyDualContinuity.duration_tendsto T)

end OperatorDerivativeRewrite.Foundation.HigherHeatJetCorrectionFields
