import Foundation.HigherHeatQuadraticDualCurve
import Foundation.HigherHeatQuadraticItoApproximation

/-! Actual predictable squared-coordinate fields and native L1 approximation. -/
noncomputable section
open scoped NNReal ENNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatQuadraticPredictableField
open MeasureTheory Filter HigherHeatWeakTimeAdjoint HigherHeatPairedDualCausality
open HigherHeatAnalyticCylinderDomain HigherHeatPolynomialCylinders HigherHeatCompletedPairing
open HigherHeatDyadicStepAgreement HigherHeatQuadraticItoData HigherHeatQuadraticItoFields
open HigherHeatQuadraticItoApproximation HigherHeatQuadraticDualCurve HigherHeatDyadicTimeDensity
open HigherHeatAdaptedStepDuality

def squarePast (n : ℕ) (j : Fin (size n)) : Test n := (past n j)^2

theorem squarePast_adapted (n : ℕ) : Adapted (squarePast n) := by
  intro j i hi
  exact past_adapted n j i (MvPolynomial.vars_pow (past n j) 2 hi)

def quadraticFunction (T : ℝ≥0) (hT : 0 < T) (t : ℝ) : Dual :=
  quadraticCurve T hT (Set.projIcc 0 1 (by norm_num) t)

theorem quadraticFunction_memLp (T : ℝ≥0) (hT : 0 < T) :
    MemLp (quadraticFunction T hT) 1 timeMeasure := by
  have hc : Continuous (quadraticFunction T hT) :=
    (quadraticCurve T hT).continuous.comp continuous_projIcc
  exact MemLp.of_bound hc.stronglyMeasurable.aestronglyMeasurable ‖quadraticCurve T hT‖
    (Eventually.of_forall (fun t => (quadraticCurve T hT).norm_coe_le_norm _))

def quadraticField (T : ℝ≥0) (hT : 0 < T) : Field timeMeasure :=
  (quadraticFunction_memLp T hT).toLp (quadraticFunction T hT)

theorem quadraticField_ae (T : ℝ≥0) (hT : 0 < T) :
    (quadraticField T hT : ℝ → Dual) =ᵐ[timeMeasure] quadraticFunction T hT :=
  MemLp.coeFn_toLp _

theorem squarePast_curve (n : ℕ) (T : ℝ≥0) (hT : 0 < T) (j : Fin (size n)) :
    pairing 2 (by norm_num) T hT (core (cylinderOf n (squarePast n j))) =
      quadraticCurve T hT (node n (prefixNode n j.val (Nat.le_of_lt j.isLt))) := by
  exact (quadratic_curve_prefix n T hT j.val (Nat.le_of_lt j.isLt)).symm

theorem squarePast_bound (n : ℕ) (T : ℝ≥0) (hT : 0 < T) (j : Fin (size n)) :
    ‖pairing 2 (by norm_num) T hT (core (cylinderOf n (squarePast n j)))‖ ≤
      ‖quadraticCurve T hT‖ := by
  rw [squarePast_curve]
  exact (quadraticCurve T hT).norm_coe_le_norm _

theorem field_cell_bound (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (t : ℝ) (ht : t ∈ gridCell n j) :
    ‖pairing 2 (by norm_num) T hT (core (cylinderOf n (squarePast n j))) -
      quadraticFunction T hT t‖ ≤
        (quadraticConstant T hT:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ) := by
  rw [squarePast_curve]
  have hdist : dist (node n (prefixNode n j.val (Nat.le_of_lt j.isLt)))
      (Set.projIcc 0 1 (by norm_num) t) ≤ (HigherHeatDyadicLaws.duration 1 n:ℝ) := by
    rw [Subtype.dist_eq, Real.dist_eq, left_time,
      Set.projIcc_of_mem (by norm_num : (0:ℝ) ≤ 1) (gridCell_subset n j ht)]
    rw [abs_of_nonpos (sub_nonpos.mpr ht.1.le)]
    nlinarith only [ht.2]
  change ‖quadraticCurve T hT (node n (prefixNode n j.val _)) -
    quadraticCurve T hT (Set.projIcc 0 1 (by norm_num) t)‖ ≤ _
  calc
    _ = dist (quadraticCurve T hT (node n (prefixNode n j.val _)))
        (quadraticCurve T hT (Set.projIcc 0 1 (by norm_num) t)) := (dist_eq_norm _ _).symm
    _ ≤ (quadraticConstant T hT:ℝ)*dist (node n (prefixNode n j.val _))
        (Set.projIcc 0 1 (by norm_num) t) := (quadratic_curve_lipschitz T hT).dist_le_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hdist (quadraticConstant T hT).coe_nonneg

theorem field_bound (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    ‖adaptedField n 2 (by norm_num) T hT (squarePast n) - quadraticField T hT‖ ≤
      (quadraticConstant T hT:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ) := by
  have hb : ∀ᵐ t : ℝ ∂timeMeasure,
      ‖(adaptedField n 2 (by norm_num) T hT (squarePast n) - quadraticField T hT) t‖ ≤
        (quadraticConstant T hT:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ) := by
    filter_upwards [Lp.coeFn_sub (adaptedField n 2 (by norm_num) T hT (squarePast n))
      (quadraticField T hT), adaptedField_cell_ae n 2 (by norm_num) T hT (squarePast n),
      quadraticField_ae T hT, time_ae] with t hs hf hc hI
    obtain ⟨j, hj⟩ := cell_exists n t hI
    rw [hs]
    change ‖adaptedField n 2 (by norm_num) T hT (squarePast n) t - quadraticField T hT t‖ ≤ _
    rw [hf j hj, hc]
    exact field_cell_bound n T hT j t hj
  have hh := Lp.norm_le_of_ae_bound (E := Dual) (p := 1) (μ := timeMeasure)
    (f := adaptedField n 2 (by norm_num) T hT (squarePast n) - quadraticField T hT)
    (by positivity) hb
  have hm : (measureUnivNNReal timeMeasure:ℝ) = 1 := by simp [measureUnivNNReal, timeMeasure]
  simpa only [ENNReal.toReal_one, inv_one, Real.rpow_one, NNReal.rpow_one, hm, one_mul] using hh

theorem fields_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => adaptedField n 2 (by norm_num) T hT (squarePast n)) atTop
      (𝓝 (quadraticField T hT)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => field_bound n T hT)
  simpa only [mul_zero] using (tendsto_const_nhds (x := (quadraticConstant T hT:ℝ))).mul
    (HigherHeatEarlyDualContinuity.duration_tendsto 1)

theorem field_mem (T : ℝ≥0) (hT : 0 < T) :
    quadraticField T hT ∈ HigherHeatAdaptedIntegralClosure.space 2 (by norm_num) T hT := by
  let S := HigherHeatAdaptedIntegralClosure.stepSpan 2 (by norm_num) T hT
  apply S.isClosed_topologicalClosure.mem_of_tendsto (fields_tendsto T hT)
  exact Eventually.of_forall (fun n =>
    (HigherHeatAdaptedIntegralClosure.native 2 (by norm_num) T hT n (squarePast n)
      (squarePast_adapted n)).property)

def quadraticInput (T : ℝ≥0) (hT : 0 < T) :
    HigherHeatAdaptedIntegralClosure.space 2 (by norm_num) T hT :=
  ⟨quadraticField T hT, field_mem T hT⟩

end OperatorDerivativeRewrite.Foundation.HigherHeatQuadraticPredictableField
