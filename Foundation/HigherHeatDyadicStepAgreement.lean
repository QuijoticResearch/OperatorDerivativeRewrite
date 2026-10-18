import Foundation.HigherHeatWeakStepFields
import Foundation.HigherHeatAdaptedStepDuality
import Foundation.HigherHeatPositionSteinDerivative

/-! Exact derivative and signed integral agreement on native dyadic test grids. -/
noncomputable section
open scoped NNReal ENNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatDyadicStepAgreement
open MeasureTheory HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain
open HigherHeatCommonDerivative HigherHeatTimeDerivative HigherHeatWeakTimeAdjoint
open HigherHeatWeakStepFields HigherHeatPolynomialCoordinates HigherHeatCompletedPairing
open MultivariateFactorialDomain HigherHeatPositionSteinDerivative
open HigherHeatAdaptedStepDuality

def gridCell (n : ℕ) (j : Fin (size n)) : Set ℝ :=
  Set.Ioc ((j.val:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ))
    (((j.val:ℝ)+1)*(HigherHeatDyadicLaws.duration 1 n:ℝ))

theorem gridCell_measurable (n : ℕ) (j : Fin (size n)) : MeasurableSet (gridCell n j) :=
  measurableSet_Ioc

theorem cutoff_on_cell (n : ℕ) (j : Fin (size n)) (t : ℝ) (ht : t ∈ gridCell n j) :
    (fun i => HigherHeatTimeDerivative.direction t (timeEmbedding n i)) =
      HigherHeatPositionTransport.direction (size n) j := by
  funext i
  have hd : 0 < (HigherHeatDyadicLaws.duration 1 n:ℝ) :=
    (HigherHeatDyadicLaws.duration_pos 1 (by norm_num) n)
  have he (k : Fin (size n)) : (timeEmbedding n k:ℝ) =
      ((k.val:ℝ)+1)*(HigherHeatDyadicLaws.duration 1 n:ℝ) := by
    simp [timeEmbedding, HigherHeatContinuousCylinders.sampleTime, HigherHeatDyadicLaws.time]
  have hcut : t ≤ (timeEmbedding n i:ℝ) ↔ j ≤ i := by
    rw [he]
    constructor
    · intro h
      by_contra hn
      have hji : (i.val:ℝ)+1 ≤ (j.val:ℝ) := by exact_mod_cast (show i.val+1 ≤ j.val by omega)
      have hh := mul_le_mul_of_nonneg_right hji hd.le
      exact (not_lt_of_ge (h.trans hh)) ht.1
    · intro h
      have hji : (j.val:ℝ)+1 ≤ (i.val:ℝ)+1 := by exact_mod_cast (show j.val+1 ≤ i.val+1 by omega)
      exact ht.2.trans (mul_le_mul_of_nonneg_right hji hd.le)
  simp only [HigherHeatTimeDerivative.direction, HigherHeatPositionTransport.direction, hcut]

theorem gridDerivative_tail (n : ℕ) (j : Fin (size n)) (P : Test n) :
    gridDerivative n (HigherHeatPositionTransport.direction (size n) j) P =
      polynomialDerivative (Pi.single j 1) P := by
  change coordinates n (polynomialDerivative _ ((coordinates n).symm P)) = _
  rw [coordinates_derivative, AlgEquiv.apply_symm_apply]

theorem derivative_core_on_cell (n : ℕ) (j : Fin (size n)) (t : ℝ)
    (ht : t ∈ gridCell n j) (r : ℕ) (G : Test n) :
    ((atTime t)^r) (core (cylinderOf n G)) =
      core (cylinderOf n
        ((polynomialDerivative (Pi.single j 1) : Test n → Test n)^[r] G)) := by
  rw [atTime, operator_pow_core, cutoff_on_cell n j t ht]
  have he : (gridDerivative n (HigherHeatPositionTransport.direction (size n) j) :
      Test n → Test n) = polynomialDerivative (Pi.single j 1) :=
    funext (gridDerivative_tail n j)
  rw [he]

theorem gridCell_subset (n : ℕ) (j : Fin (size n)) : gridCell n j ⊆ Set.Icc (0:ℝ) 1 := by
  intro t ht
  refine ⟨(mul_nonneg (Nat.cast_nonneg j.val) (HigherHeatDyadicLaws.duration 1 n).coe_nonneg).trans ht.1.le, ?_⟩
  have he : (((j.val:ℝ)+1)*(HigherHeatDyadicLaws.duration 1 n:ℝ)) ≤ 1 := by
    exact_mod_cast HigherHeatDyadicLaws.time_in_horizon 1 n j
  exact ht.2.trans he

theorem gridCell_measure (n : ℕ) (j : Fin (size n)) :
    timeMeasure.real (gridCell n j) = (HigherHeatDyadicLaws.duration 1 n:ℝ) := by
  have hd := (HigherHeatDyadicLaws.duration 1 n).coe_nonneg
  have he : timeMeasure (gridCell n j) = volume (gridCell n j) := by
    rw [timeMeasure, Measure.restrict_apply (gridCell_measurable n j),
      Set.inter_eq_left.mpr (gridCell_subset n j)]
  rw [measureReal_def, he, ← measureReal_def, gridCell, Real.volume_real_Ioc_of_le (by nlinarith)]
  ring

theorem gridCell_finite (n : ℕ) (j : Fin (size n)) : timeMeasure (gridCell n j) ≠ ∞ := by
  have he : timeMeasure (gridCell n j) = volume (gridCell n j) := by
    rw [timeMeasure, Measure.restrict_apply (gridCell_measurable n j),
      Set.inter_eq_left.mpr (gridCell_subset n j)]
  rw [he]
  exact measure_Ioc_lt_top.ne

def coefficientField (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) : Field timeMeasure :=
  step timeMeasure (gridCell n j) (gridCell_measurable n j) (gridCell_finite n j)
    (pairing m hm T hT (core (cylinderOf n F)))

theorem coefficientField_integral (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F G : Test n) :
    firstChannel m T (coefficientField n m hm T hT j F) (core (cylinderOf n G)) =
      coefficient m T * (HigherHeatDyadicLaws.duration 1 n:ℝ) *
        pairing m hm T hT (core (cylinderOf n F))
          (core (cylinderOf n ((polynomialDerivative (Pi.single j 1) : Test n → Test n)^[2*m-1] G))) := by
  change coefficient m T * transpose timeMeasure (2*m-1)
    (step _ _ _ _ _) (core (cylinderOf n G)) = _
  rw [transpose_step_constant timeMeasure (2*m-1) (gridCell n j)
    (gridCell_measurable n j) (gridCell_finite n j) _ _ _
    ((ae_restrict_mem (gridCell_measurable n j)).mono (fun t ht =>
      derivative_core_on_cell n j t ht (2*m-1) G)), gridCell_measure]
  ring

theorem duration_scale (T : ℝ≥0) (n : ℕ) :
    (T:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ) =
      (HigherHeatDyadicLaws.duration T n:ℝ) := by
  simp [HigherHeatDyadicLaws.duration, div_eq_mul_inv]

theorem actual_adapted_step_agreement (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F G : Test n) (hF : j ∉ F.vars) :
    firstChannel m T (coefficientField n m hm T hT j F) (core (cylinderOf n G)) =
      pairing m hm T hT (core (cylinderOf n (F * MvPolynomial.X j)))
        (core (cylinderOf n G)) := by
  have hp (A B : Test n) :
      pairing m hm T hT (core (cylinderOf n A)) (core (cylinderOf n B)) =
        (HigherHeatMultivariateMoments.mean m hm
          (fun _ : Fin (size n) => HigherHeatDyadicLaws.duration T n)
          (fun _ => HigherHeatDyadicLaws.duration_pos T hT n) (A*B)).re := by
    rw [pairing_core_real, ← map_mul (cylinderOf n), cylindricalExpectation_apply]
    rfl
  rw [coefficientField_integral, hp, hp, actual_step_duality _ _ _ _ j F G hF]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, PureOrderPolynomialConditioning.parameters, coefficient]
  rw [← duration_scale T n]
  ring

def adaptedField (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (F : Fin (size n) → Test n) : Field timeMeasure :=
  ∑ j, coefficientField n m hm T hT j (F j)

theorem actual_adapted_sum_agreement (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (F : Fin (size n) → Test n) (hF : Adapted F) (G : Test n) :
    firstChannel m T (adaptedField n m hm T hT F) (core (cylinderOf n G)) =
      pairing m hm T hT (core (cylinderOf n (stepPolynomial F)))
        (core (cylinderOf n G)) := by
  simp only [adaptedField, stepPolynomial, map_sum, sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact actual_adapted_step_agreement n m hm T hT j (F j) G (adapted_missing hF j)

end OperatorDerivativeRewrite.Foundation.HigherHeatDyadicStepAgreement
