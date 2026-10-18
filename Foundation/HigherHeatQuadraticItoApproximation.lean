import Foundation.HigherHeatQuadraticItoFields

/-! Genuine L1 convergence of the native predictable coefficients to the verified dual curve. -/
noncomputable section
open scoped NNReal ENNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatQuadraticItoApproximation
open MeasureTheory Filter HigherHeatWeakTimeAdjoint HigherHeatPairedDualCausality
open HigherHeatAnalyticCylinderDomain HigherHeatPolynomialCylinders HigherHeatCompletedPairing
open HigherHeatDyadicStepAgreement HigherHeatQuadraticItoData HigherHeatQuadraticItoFields
open HigherHeatContinuousDualCoordinate HigherHeatDyadicTimeDensity HigherHeatDyadicDualData

theorem left_time (n : ℕ) (j : Fin (size n)) :
    (node n (prefixNode n j.val (Nat.le_of_lt j.isLt)) : ℝ) =
      (j.val:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ) := by
  change HigherHeatContinuousCylinders.interpolationNode n (prefixNode n j.val _) = _
  rw [prefixNode_time]
  simp only [HigherHeatDyadicLaws.duration, NNReal.coe_div, NNReal.coe_one, NNReal.coe_natCast]
  ring

theorem curve_cell_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (t : ℝ) (ht : t ∈ gridCell n j) :
    ‖pairing m hm T hT (core (cylinderOf n (past n j))) - curveFunction m hm T hT t‖ ≤
      (constant m T:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ) := by
  rw [past_curve]
  have hdist : dist (node n (prefixNode n j.val (Nat.le_of_lt j.isLt)))
      (Set.projIcc 0 1 (by norm_num) t) ≤ (HigherHeatDyadicLaws.duration 1 n:ℝ) := by
    rw [Subtype.dist_eq, Real.dist_eq, left_time,
      Set.projIcc_of_mem (by norm_num : (0:ℝ) ≤ 1) (gridCell_subset n j ht)]
    rw [abs_of_nonpos (sub_nonpos.mpr ht.1.le)]
    nlinarith only [ht.2]
  change ‖curve m hm T hT (node n (prefixNode n j.val _)) -
    curve m hm T hT (Set.projIcc 0 1 (by norm_num) t)‖ ≤ _
  calc
    _ = dist (curve m hm T hT (node n (prefixNode n j.val _)))
        (curve m hm T hT (Set.projIcc 0 1 (by norm_num) t)) := (dist_eq_norm _ _).symm
    _ ≤ (constant m T:ℝ) * dist (node n (prefixNode n j.val _))
        (Set.projIcc 0 1 (by norm_num) t) := (curve_lipschitz m hm T hT).dist_le_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hdist (constant m T).coe_nonneg

theorem past_field_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    ‖adaptedField n m hm T hT (past n) - curveField m hm T hT‖ ≤
      (constant m T:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ) := by
  have hb : ∀ᵐ t : ℝ ∂timeMeasure,
      ‖(adaptedField n m hm T hT (past n) - curveField m hm T hT) t‖ ≤
        (constant m T:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ) := by
    filter_upwards [Lp.coeFn_sub (adaptedField n m hm T hT (past n)) (curveField m hm T hT),
      adaptedField_cell_ae n m hm T hT (past n), curveField_ae m hm T hT, time_ae]
      with t hs hf hc hI
    obtain ⟨j, hj⟩ := cell_exists n t hI
    rw [hs]
    change ‖adaptedField n m hm T hT (past n) t - curveField m hm T hT t‖ ≤ _
    rw [hf j hj, hc]
    exact curve_cell_bound n m hm T hT j t hj
  have hh := Lp.norm_le_of_ae_bound (E := Dual) (p := 1) (μ := timeMeasure)
    (f := adaptedField n m hm T hT (past n) - curveField m hm T hT) (by positivity) hb
  have hm : (measureUnivNNReal timeMeasure:ℝ) = 1 := by simp [measureUnivNNReal, timeMeasure]
  simpa only [ENNReal.toReal_one, inv_one, Real.rpow_one, NNReal.rpow_one, hm, one_mul] using hh

theorem past_fields_tendsto (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => adaptedField n m hm T hT (past n)) atTop (𝓝 (curveField m hm T hT)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => past_field_bound n m hm T hT)
  simpa only [mul_zero] using (tendsto_const_nhds (x := (constant m T:ℝ))).mul
    (HigherHeatEarlyDualContinuity.duration_tendsto 1)

theorem curve_mem (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    curveField m hm T hT ∈ HigherHeatAdaptedIntegralClosure.space m hm T hT := by
  apply (HigherHeatAdaptedIntegralClosure.stepSpan m hm T hT).isClosed_topologicalClosure.mem_of_tendsto
    (past_fields_tendsto m hm T hT)
  exact Eventually.of_forall (fun n =>
    (HigherHeatAdaptedIntegralClosure.native m hm T hT n (past n) (past_adapted n)).property)

def curveInput (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    HigherHeatAdaptedIntegralClosure.space m hm T hT := ⟨curveField m hm T hT, curve_mem m hm T hT⟩

def constantInput (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    HigherHeatAdaptedIntegralClosure.space m hm T hT := by
  refine ⟨constantField m hm T hT, ?_⟩
  rw [← constants_field_eq 0 m hm T hT]
  exact (HigherHeatAdaptedIntegralClosure.native m hm T hT 0 (fun _ => 1) (constants_adapted 0)).property

end OperatorDerivativeRewrite.Foundation.HigherHeatQuadraticItoApproximation
