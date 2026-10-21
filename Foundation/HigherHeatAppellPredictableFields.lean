import Foundation.PureOrderAppellParameter
import Foundation.HigherHeatWeightedPastApproximation
import Foundation.HigherHeatCubicStepIdentity

/-! Actual backward-heat Appell coefficients, with right-time native sampling,
finite polynomial weights and genuine predictable L1 limits. -/
noncomputable section
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatAppellPredictableFields
open Filter HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain HigherHeatCompletedPairing
open HigherHeatPairedDualCausality HigherHeatWeakTimeAdjoint HigherHeatDyadicStepAgreement
open HigherHeatWeightedPastFields HigherHeatWeightedPastApproximation HigherHeatDyadicTimeDensity
open HigherHeatQuadraticItoData HigherHeatAdaptedStepDuality PureOrderAppellCalculus
open PureOrderAppellParameter HigherHeatPolynomialCurveAgreement

def parameter (m : ℕ) (T : ℝ≥0) : ℝ := (-1:ℝ)^(m+1)*(T:ℝ)

def weight (m : ℕ) (T : ℝ≥0) (N r : ℕ) : C(Interval,ℝ) :=
  ⟨fun t => ((parametric (2*m) N).coeff r).eval (parameter m T*((t:ℝ)-1)),
    (((parametric (2*m) N).coeff r).continuous).comp (continuous_const.mul (continuous_subtype_val.sub continuous_const))⟩

def appellPast (n m : ℕ) (T : ℝ≥0) (N : ℕ) (j : Fin (size n)) : Test n :=
  Polynomial.aeval (past n j)
    (appell (2*m) (parameter m T*((rightNode n j:ℝ)-1)) N)

theorem appellPast_expansion (n m : ℕ) (T : ℝ≥0) (N : ℕ) (j : Fin (size n)) :
    appellPast n m T N j = ∑ r ∈ (parametric (2*m) N).support,
      weightedPast (weight m T N r) n r j := by
  rw [appellPast, expansion]
  simp only [map_sum, map_smul, map_pow, Polynomial.aeval_X, weightedPast,
    HigherHeatPolynomialPredictableField.powerPast, weight]
  rfl

theorem appellPast_adapted (n m : ℕ) (T : ℝ≥0) (N : ℕ) : Adapted (appellPast n m T N) := by
  classical
  intro j i hi
  rw [appellPast_expansion] at hi
  obtain ⟨r, _, hr⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_sum_subset _ _ hi)
  exact weightedPast_adapted (weight m T N r) n r j i hr

theorem coefficient_field_sum {ι : Type*} (s : Finset ι) (n m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (j : Fin (size n)) (F : ι → Test n) :
    coefficientField n m hm T hT j (∑ i ∈ s, F i) =
      ∑ i ∈ s, coefficientField n m hm T hT j (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    apply norm_eq_zero.mp
    rw [coefficientField, HigherHeatWeakStepFields.step_norm]
    simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, HigherHeatCubicStepIdentity.coefficientField_add,
      ih, Finset.sum_insert hi]

def appellField (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (N : ℕ) : Field timeMeasure :=
  ∑ r ∈ (parametric (2*m) N).support, weightedField (weight m T N r) m hm T hT r

theorem appell_native_fields_eq (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (N : ℕ) :
    adaptedField n m hm T hT (appellPast n m T N) =
      ∑ r ∈ (parametric (2*m) N).support,
        adaptedField n m hm T hT (weightedPast (weight m T N r) n r) := by
  simp only [adaptedField, appellPast_expansion, coefficient_field_sum]
  rw [Finset.sum_comm]

theorem appell_fields_tendsto (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (N : ℕ) :
    Tendsto (fun n => adaptedField n m hm T hT (appellPast n m T N)) atTop
      (𝓝 (appellField m hm T hT N)) := by
  let : ContinuousAdd (Field timeMeasure) :=
    (inferInstance : IsTopologicalAddGroup (Field timeMeasure)).toContinuousAdd
  simp_rw [appell_native_fields_eq]
  exact tendsto_finsetSum _ (fun r _ => weighted_fields_tendsto (weight m T N r) m hm T hT r)

theorem appell_field_mem (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (N : ℕ) :
    appellField m hm T hT N ∈ HigherHeatAdaptedIntegralClosure.space m hm T hT := by
  apply Submodule.sum_mem
  intro r _
  exact weighted_field_mem (weight m T N r) m hm T hT r

theorem appellPast_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (N : ℕ)
    (j : Fin (size n)) :
    ‖pairing m hm T hT (core (cylinderOf n (appellPast n m T N j)))‖ ≤
      ∑ r ∈ (parametric (2*m) N).support,
        ‖weight m T N r‖*‖coordinateCurve m hm T hT r‖ := by
  simp only [appellPast_expansion, map_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun r _ =>
    weightedPast_bound (weight m T N r) n m hm T hT r j))

end OperatorDerivativeRewrite.Foundation.HigherHeatAppellPredictableFields
