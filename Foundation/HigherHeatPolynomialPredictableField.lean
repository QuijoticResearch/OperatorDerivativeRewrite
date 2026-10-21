import Foundation.HigherHeatPolynomialCurveAgreement
import Foundation.HigherHeatQuadraticItoApproximation

/-! Actual predictable all polynomial coordinate-power fields and native L1 approximation. -/
noncomputable section
open scoped NNReal ENNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatPolynomialPredictableField
open MeasureTheory Filter HigherHeatWeakTimeAdjoint HigherHeatPairedDualCausality
open HigherHeatAnalyticCylinderDomain HigherHeatPolynomialCylinders HigherHeatCompletedPairing
open HigherHeatDyadicStepAgreement HigherHeatQuadraticItoData HigherHeatQuadraticItoFields
open HigherHeatQuadraticItoApproximation HigherHeatPolynomialCurveAgreement HigherHeatDyadicTimeDensity
open HigherHeatAdaptedStepDuality

def powerPast (n r : ℕ) (j : Fin (size n)) : Test n := (past n j)^r

theorem powerPast_adapted (n r : ℕ) : Adapted (powerPast n r) := by
  intro j i hi
  exact past_adapted n j i (MvPolynomial.vars_pow (past n j) r hi)

def fieldFunction (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (r : ℕ) (t : ℝ) : Dual :=
  coordinateCurve m hm T hT r (Set.projIcc 0 1 (by norm_num) t)

theorem fieldFunction_memLp (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (r : ℕ) :
    MemLp (fieldFunction m hm T hT r) 1 timeMeasure := by
  have hc : Continuous (fieldFunction m hm T hT r) :=
    (coordinateCurve m hm T hT r).continuous.comp continuous_projIcc
  exact MemLp.of_bound hc.stronglyMeasurable.aestronglyMeasurable ‖coordinateCurve m hm T hT r‖
    (Eventually.of_forall (fun t => (coordinateCurve m hm T hT r).norm_coe_le_norm _))

def powerField (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (r : ℕ) : Field timeMeasure :=
  (fieldFunction_memLp m hm T hT r).toLp (fieldFunction m hm T hT r)

theorem powerField_ae (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (r : ℕ) :
    (powerField m hm T hT r : ℝ → Dual) =ᵐ[timeMeasure] fieldFunction m hm T hT r :=
  MemLp.coeFn_toLp _

theorem powerPast_curve (n : ℕ) (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (r : ℕ) (j : Fin (size n)) :
    pairing m hm T hT (core (cylinderOf n (powerPast n r j))) =
      coordinateCurve m hm T hT r (node n (prefixNode n j.val (Nat.le_of_lt j.isLt))) := by
  exact (coordinate_curve_prefix n m hm T hT j.val (Nat.le_of_lt j.isLt) r).symm

theorem powerPast_bound (n : ℕ) (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (r : ℕ) (j : Fin (size n)) :
    ‖pairing m hm T hT (core (cylinderOf n (powerPast n r j)))‖ ≤
      ‖coordinateCurve m hm T hT r‖ := by
  rw [powerPast_curve]
  exact (coordinateCurve m hm T hT r).norm_coe_le_norm _

theorem field_cell_bound (n : ℕ) (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (r : ℕ)
    (j : Fin (size n)) (t : ℝ) (ht : t ∈ gridCell n j) :
    ‖pairing m hm T hT (core (cylinderOf n (powerPast n r j))) -
      fieldFunction m hm T hT r t‖ ≤
        (coordinateConstant m hm T hT r:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ) := by
  rw [powerPast_curve]
  have hdist : dist (node n (prefixNode n j.val (Nat.le_of_lt j.isLt)))
      (Set.projIcc 0 1 (by norm_num) t) ≤ (HigherHeatDyadicLaws.duration 1 n:ℝ) := by
    rw [Subtype.dist_eq, Real.dist_eq, left_time,
      Set.projIcc_of_mem (by norm_num : (0:ℝ) ≤ 1) (gridCell_subset n j ht)]
    rw [abs_of_nonpos (sub_nonpos.mpr ht.1.le)]
    nlinarith only [ht.2]
  change ‖coordinateCurve m hm T hT r (node n (prefixNode n j.val _)) -
    coordinateCurve m hm T hT r (Set.projIcc 0 1 (by norm_num) t)‖ ≤ _
  calc
    _ = dist (coordinateCurve m hm T hT r (node n (prefixNode n j.val _)))
        (coordinateCurve m hm T hT r (Set.projIcc 0 1 (by norm_num) t)) := (dist_eq_norm _ _).symm
    _ ≤ (coordinateConstant m hm T hT r:ℝ)*dist (node n (prefixNode n j.val _))
        (Set.projIcc 0 1 (by norm_num) t) := (coordinate_curve_lipschitz m hm T hT r).dist_le_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hdist (coordinateConstant m hm T hT r).coe_nonneg

theorem field_bound (n : ℕ) (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (r : ℕ) :
    ‖adaptedField n m hm T hT (powerPast n r) - powerField m hm T hT r‖ ≤
      (coordinateConstant m hm T hT r:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ) := by
  have hb : ∀ᵐ t : ℝ ∂timeMeasure,
      ‖(adaptedField n m hm T hT (powerPast n r) - powerField m hm T hT r) t‖ ≤
        (coordinateConstant m hm T hT r:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ) := by
    filter_upwards [Lp.coeFn_sub (adaptedField n m hm T hT (powerPast n r))
      (powerField m hm T hT r), adaptedField_cell_ae n m hm T hT (powerPast n r),
      powerField_ae m hm T hT r, time_ae] with t hs hf hc hI
    obtain ⟨j, hj⟩ := cell_exists n t hI
    rw [hs]
    change ‖adaptedField n m hm T hT (powerPast n r) t - powerField m hm T hT r t‖ ≤ _
    rw [hf j hj, hc]
    exact field_cell_bound n m hm T hT r j t hj
  have hh := Lp.norm_le_of_ae_bound (E := Dual) (p := 1) (μ := timeMeasure)
    (f := adaptedField n m hm T hT (powerPast n r) - powerField m hm T hT r)
    (by positivity) hb
  have hm : (measureUnivNNReal timeMeasure:ℝ) = 1 := by simp [measureUnivNNReal, timeMeasure]
  simpa only [ENNReal.toReal_one, inv_one, Real.rpow_one, NNReal.rpow_one, hm, one_mul] using hh

theorem fields_tendsto (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (r : ℕ) :
    Tendsto (fun n => adaptedField n m hm T hT (powerPast n r)) atTop
      (𝓝 (powerField m hm T hT r)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => field_bound n m hm T hT r)
  simpa only [mul_zero] using (tendsto_const_nhds (x := (coordinateConstant m hm T hT r:ℝ))).mul
    (HigherHeatEarlyDualContinuity.duration_tendsto 1)

theorem field_mem (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (r : ℕ) :
    powerField m hm T hT r ∈ HigherHeatAdaptedIntegralClosure.space m hm T hT := by
  let S := HigherHeatAdaptedIntegralClosure.stepSpan m hm T hT
  apply S.isClosed_topologicalClosure.mem_of_tendsto (fields_tendsto m hm T hT r)
  exact Eventually.of_forall (fun n =>
    (HigherHeatAdaptedIntegralClosure.native m hm T hT n (powerPast n r)
      (powerPast_adapted n r)).property)

def powerInput (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (r : ℕ) :
    HigherHeatAdaptedIntegralClosure.space m hm T hT :=
  ⟨powerField m hm T hT r, field_mem m hm T hT r⟩

end OperatorDerivativeRewrite.Foundation.HigherHeatPolynomialPredictableField
