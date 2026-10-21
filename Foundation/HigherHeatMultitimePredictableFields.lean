import Foundation.HigherHeatMultitimeFieldLimits

/-! Canonical L1 limits, actual adapted membership and original-source bounds
for every multitime polynomial coefficient channel. -/
noncomputable section
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatMultitimePredictableFields
open Filter HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain HigherHeatWeakTimeAdjoint
open HigherHeatMultitimeFieldLimits HigherHeatDyadicStepAgreement HigherHeatPredictableJetBounds
open HigherHeatRefinedPredictableJets HigherHeatPredictableJetFields HigherHeatCompletedPairing
open HigherHeatCausalFieldCauchy HigherHeatCausalJetIdentification

def field (b : ℕ) (P : Test b) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (q : ℕ) : Field timeMeasure :=
  Classical.choose (native_fields_tendsto b P m hm T hT q)

theorem field_tendsto (b : ℕ) (P : Test b) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (q : ℕ) :
    Tendsto (fun n => adaptedField n m hm T hT
      (fun j => predictableJet n m T j q (refinedInput b P n)))
      atTop (𝓝 (field b P m hm T hT q)) :=
  Classical.choose_spec (native_fields_tendsto b P m hm T hT q)

theorem causal_tendsto (b : ℕ) (P : Test b) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (q : ℕ) :
    Tendsto (fun n => causalField n m hm T hT q (refinedInput b P n))
      atTop (𝓝 (field b P m hm T hT q)) := by
  have h := (causal_field_approximation b P m hm T hT q).add (field_tendsto b P m hm T hT q)
  simpa only [causalField, sub_add_cancel, zero_add] using h

theorem field_bound (b : ℕ) (P : Test b) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (q : ℕ) :
    ‖field b P m hm T hT q‖ ≤
      ‖pairing m hm T hT‖*((q.factorial:ℝ)⁻¹*Real.exp (T:ℝ)*‖core (cylinderOf b P)‖) := by
  exact le_of_tendsto (field_tendsto b P m hm T hT q).norm
    (Eventually.of_forall (fun n => refined_field_bound b P n m hm T hT q))

theorem field_mem (b : ℕ) (P : Test b) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (q : ℕ) :
    field b P m hm T hT q ∈ HigherHeatAdaptedIntegralClosure.space m hm T hT := by
  apply (HigherHeatAdaptedIntegralClosure.stepSpan m hm T hT).isClosed_topologicalClosure.mem_of_tendsto
    (field_tendsto b P m hm T hT q)
  exact Eventually.of_forall (fun n =>
    (HigherHeatAdaptedIntegralClosure.native m hm T hT n
      (fun j => predictableJet n m T j q (refinedInput b P n))
      (predictable_jets_adapted n m T q _)).property)

theorem field_zero_above_degree (b : ℕ) (P : Test b) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (q : ℕ) (hq : P.totalDegree < q) :
    field b P m hm T hT q = 0 := by
  apply tendsto_nhds_unique (field_tendsto b P m hm T hT q)
  have he : (fun n => adaptedField n m hm T hT
      (fun j => predictableJet n m T j q (refinedInput b P n))) = fun _ => (0:Field timeMeasure) := by
    funext n
    have hz : ∀ j, predictableJet n m T j q (refinedInput b P n) = 0 := fun j =>
      HigherHeatPredictableJetDegree.jet_zero_above_degree n m T j q _
        ((HigherHeatRefinementDegree.refined_input_degree b P n).trans_lt hq)
    simp only [hz, adaptedField]
    apply Finset.sum_eq_zero
    intro j _
    apply norm_eq_zero.mp
    rw [coefficientField, HigherHeatWeakStepFields.step_norm, map_zero, map_zero, map_zero,
      norm_zero, zero_mul]
  rw [he]
  exact tendsto_const_nhds

end OperatorDerivativeRewrite.Foundation.HigherHeatMultitimePredictableFields
