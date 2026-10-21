import Foundation.HigherHeatPolynomialPredictableField
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Right-time continuous weights on actual left-past polynomial coefficients.
These are genuine L1 fields in the existing closed adapted space. -/
noncomputable section
open scoped NNReal ENNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatWeightedPastFields
open MeasureTheory Filter HigherHeatWeakTimeAdjoint HigherHeatPairedDualCausality
open HigherHeatAnalyticCylinderDomain HigherHeatPolynomialCylinders HigherHeatCompletedPairing
open HigherHeatDyadicStepAgreement HigherHeatQuadraticItoData HigherHeatQuadraticItoFields
open HigherHeatPolynomialPredictableField HigherHeatPolynomialCurveAgreement HigherHeatDyadicTimeDensity
open HigherHeatQuadraticItoApproximation HigherHeatAdaptedStepDuality

def leftNode (n : ℕ) (j : Fin (size n)) : Interval :=
  node n (prefixNode n j.val (Nat.le_of_lt j.isLt))

def rightNode (n : ℕ) (j : Fin (size n)) : Interval :=
  node n (prefixNode n (j.val+1) (by omega))

theorem node_cell_dist (n : ℕ) (j : Fin (size n)) (t : ℝ) (ht : t ∈ gridCell n j) :
    dist (leftNode n j) (Set.projIcc 0 1 (by norm_num) t) ≤
      (HigherHeatDyadicLaws.duration 1 n:ℝ) ∧
    dist (rightNode n j) (Set.projIcc 0 1 (by norm_num) t) ≤
      (HigherHeatDyadicLaws.duration 1 n:ℝ) := by
  have hr : (rightNode n j:ℝ) =
      ((j.val:ℝ)+1)*(HigherHeatDyadicLaws.duration 1 n:ℝ) := by
    change HigherHeatContinuousCylinders.interpolationNode n
      (prefixNode n (j.val+1) (by omega)) = _
    rw [prefixNode_time]
    simp only [HigherHeatDyadicLaws.duration, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_natCast, Nat.cast_add, Nat.cast_one]
    ring
  constructor
  · rw [Subtype.dist_eq, Real.dist_eq, leftNode, left_time,
      Set.projIcc_of_mem (by norm_num : (0:ℝ) ≤ 1) (gridCell_subset n j ht),
      abs_of_nonpos (sub_nonpos.mpr ht.1.le)]
    nlinarith only [ht.2]
  · rw [Subtype.dist_eq, Real.dist_eq, hr,
      Set.projIcc_of_mem (by norm_num : (0:ℝ) ≤ 1) (gridCell_subset n j ht),
      abs_of_nonneg (sub_nonneg.mpr ht.2)]
    nlinarith only [ht.1]

def weightedPast (w : C(Interval,ℝ)) (n d : ℕ) (j : Fin (size n)) : Test n :=
  w (rightNode n j) • powerPast n d j

theorem weightedPast_adapted (w : C(Interval,ℝ)) (n d : ℕ) : Adapted (weightedPast w n d) := by
  classical
  intro j i hi
  by_cases hw : w (rightNode n j) = 0
  · simp [weightedPast, hw] at hi
  · rw [weightedPast, MvPolynomial.smul_eq_C_mul, MvPolynomial.vars_C_mul _ hw] at hi
    exact powerPast_adapted n d j i hi

def weightedCurve (w : C(Interval,ℝ)) (m : ℕ) (hm : 0 < m) (T : ℝ≥0)
    (hT : 0 < T) (d : ℕ) : C(Interval,Dual) :=
  ⟨fun t => w t • coordinateCurve m hm T hT d t,
    w.continuous.smul (coordinateCurve m hm T hT d).continuous⟩

def weightedFunction (w : C(Interval,ℝ)) (m : ℕ) (hm : 0 < m) (T : ℝ≥0)
    (hT : 0 < T) (d : ℕ) (t : ℝ) : Dual :=
  weightedCurve w m hm T hT d (Set.projIcc 0 1 (by norm_num) t)

theorem weighted_memLp (w : C(Interval,ℝ)) (m : ℕ) (hm : 0 < m) (T : ℝ≥0)
    (hT : 0 < T) (d : ℕ) : MemLp (weightedFunction w m hm T hT d) 1 timeMeasure := by
  have hc : Continuous (weightedFunction w m hm T hT d) :=
    (weightedCurve w m hm T hT d).continuous.comp continuous_projIcc
  exact MemLp.of_bound hc.stronglyMeasurable.aestronglyMeasurable
    ‖weightedCurve w m hm T hT d‖
    (Eventually.of_forall (fun t => (weightedCurve w m hm T hT d).norm_coe_le_norm _))

def weightedField (w : C(Interval,ℝ)) (m : ℕ) (hm : 0 < m) (T : ℝ≥0)
    (hT : 0 < T) (d : ℕ) : Field timeMeasure :=
  (weighted_memLp w m hm T hT d).toLp (weightedFunction w m hm T hT d)

theorem weightedField_ae (w : C(Interval,ℝ)) (m : ℕ) (hm : 0 < m) (T : ℝ≥0)
    (hT : 0 < T) (d : ℕ) :
    (weightedField w m hm T hT d : ℝ → Dual) =ᵐ[timeMeasure] weightedFunction w m hm T hT d :=
  MemLp.coeFn_toLp _

theorem weightedPast_curve (w : C(Interval,ℝ)) (n m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (d : ℕ) (j : Fin (size n)) :
    pairing m hm T hT (core (cylinderOf n (weightedPast w n d j))) =
      w (rightNode n j) • coordinateCurve m hm T hT d (leftNode n j) := by
  simp only [weightedPast, map_smul, powerPast_curve, leftNode]

theorem weightedPast_bound (w : C(Interval,ℝ)) (n m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (d : ℕ) (j : Fin (size n)) :
    ‖pairing m hm T hT (core (cylinderOf n (weightedPast w n d j)))‖ ≤
      ‖w‖*‖coordinateCurve m hm T hT d‖ := by
  rw [weightedPast_curve, norm_smul]
  exact mul_le_mul (w.norm_coe_le_norm _) ((coordinateCurve m hm T hT d).norm_coe_le_norm _)
    (norm_nonneg _) (norm_nonneg _)

end OperatorDerivativeRewrite.Foundation.HigherHeatWeightedPastFields
