import Foundation.HigherHeatQuadraticItoData
import Mathlib.Topology.ContinuousMap.Compact

/-! Actual Bochner time fields for the concrete quadratic Itô identity. -/
noncomputable section
open scoped NNReal ENNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatQuadraticItoFields
open MeasureTheory Filter HigherHeatWeakTimeAdjoint HigherHeatPairedDualCausality
open HigherHeatAnalyticCylinderDomain HigherHeatPolynomialCylinders HigherHeatCompletedPairing
open HigherHeatDyadicStepAgreement HigherHeatWeakStepFields HigherHeatQuadraticItoData
open HigherHeatContinuousDualCoordinate HigherHeatDyadicTimeDensity

instance timeFinite : IsFiniteMeasure timeMeasure := ⟨by simp [timeMeasure]⟩

theorem time_mass : timeMeasure.real Set.univ = 1 := by simp [timeMeasure, measureReal_def]

theorem time_ae : ∀ᵐ t : ℝ ∂timeMeasure, t ∈ Set.Ioc (0:ℝ) 1 := by
  change ∀ᵐ t : ℝ ∂volume.restrict (Set.Icc (0:ℝ) 1), t ∈ Set.Ioc (0:ℝ) 1
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0:ℝ)), ae_restrict_mem measurableSet_Icc] with t ht hI
  exact ⟨lt_of_le_of_ne hI.1 ht.symm, hI.2⟩

def curveFunction (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (t : ℝ) : Dual :=
  curve m hm T hT (Set.projIcc 0 1 (by norm_num) t)

theorem curveFunction_memLp (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    MemLp (curveFunction m hm T hT) 1 timeMeasure := by
  have hc : Continuous (curveFunction m hm T hT) :=
    (curve m hm T hT).continuous.comp continuous_projIcc
  exact MemLp.of_bound hc.stronglyMeasurable.aestronglyMeasurable ‖curve m hm T hT‖
    (Eventually.of_forall (fun t => (curve m hm T hT).norm_coe_le_norm _))

def curveField (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) : Field timeMeasure :=
  (curveFunction_memLp m hm T hT).toLp (curveFunction m hm T hT)

theorem curveField_ae (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    (curveField m hm T hT : ℝ → Dual) =ᵐ[timeMeasure] curveFunction m hm T hT :=
  MemLp.coeFn_toLp _

def constantField (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) : Field timeMeasure :=
  Lp.const 1 timeMeasure (pairing m hm T hT (core (1:HigherHeatPolynomialCylinders.Cylinder)))

theorem constantField_ae (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    (constantField m hm T hT : ℝ → Dual) =ᵐ[timeMeasure]
      (fun _ => pairing m hm T hT (core (1:HigherHeatPolynomialCylinders.Cylinder))) :=
  Lp.coeFn_const 1 timeMeasure (pairing m hm T hT (core (1:HigherHeatPolynomialCylinders.Cylinder)))

theorem adaptedField_cell_ae (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (F : Fin (size n) → Test n) :
    ∀ᵐ t : ℝ ∂timeMeasure, ∀ j : Fin (size n), t ∈ gridCell n j →
      (adaptedField n m hm T hT F) t = pairing m hm T hT (core (cylinderOf n (F j))) := by
  classical
  have hi (j : Fin (size n)) :
      (coefficientField n m hm T hT j (F j) : ℝ → Dual) =ᵐ[timeMeasure]
        (gridCell n j).indicator (fun _ => pairing m hm T hT (core (cylinderOf n (F j)))) :=
    step_ae timeMeasure _ _ _ _
  have hs (S : Finset (Fin (size n))) :
      ((∑ j ∈ S, coefficientField n m hm T hT j (F j) : Field timeMeasure) : ℝ → Dual) =ᵐ[timeMeasure]
        (fun t => ∑ j ∈ S, (gridCell n j).indicator
          (fun _ => pairing m hm T hT (core (cylinderOf n (F j)))) t) := by
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      filter_upwards [Lp.coeFn_zero Dual 1 timeMeasure] with t ht
      exact ht
    | @insert j S hj ih =>
      simp only [Finset.sum_insert hj]
      filter_upwards [Lp.coeFn_add (coefficientField n m hm T hT j (F j))
        (∑ k ∈ S, coefficientField n m hm T hT k (F k)), hi j, ih] with t ha hj' hS
      simpa only [Pi.add_apply, hj', hS] using ha
  filter_upwards [hs Finset.univ] with t ht
  intro j hj
  change (∑ k : Fin (size n), coefficientField n m hm T hT k (F k)) t = _
  rw [ht, Finset.sum_eq_single j]
  · exact Set.indicator_of_mem hj _
  · intro k _ hkj
    apply Set.indicator_of_notMem
    intro hk
    exact hkj (cell_unique n k j t hk hj)
  · intro h
    exact (h (Finset.mem_univ j)).elim

theorem constants_field_eq (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    adaptedField n m hm T hT (fun _ => (1:Test n)) = constantField m hm T hT := by
  apply Lp.ext
  filter_upwards [adaptedField_cell_ae n m hm T hT (fun _ => (1:Test n)),
    constantField_ae m hm T hT, time_ae] with t ht hc hI
  obtain ⟨j, hj⟩ := cell_exists n t hI
  rw [ht j hj, hc, map_one]

end OperatorDerivativeRewrite.Foundation.HigherHeatQuadraticItoFields
