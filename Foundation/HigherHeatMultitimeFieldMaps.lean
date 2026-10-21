import Foundation.HigherHeatMultitimeReconstruction
import Mathlib.Analysis.Normed.Operator.Extend

/-! Cofinal, linear multichannel coefficients and their bounded extension to
completed observables, with values in the actual Bochner L1 field space. -/
noncomputable section
open scoped NNReal ENNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatMultitimeFieldMaps
open MeasureTheory Filter HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain
open HigherHeatCompletedPairing HigherHeatPairedDualCausality HigherHeatWeakTimeAdjoint
open HigherHeatDyadicStepAgreement HigherHeatWeakStepFields HigherHeatPredictableJetBounds
open HigherHeatRefinedPredictableJets HigherHeatMultitimePredictableFields

def stepMap (s : Set ℝ) (hs : MeasurableSet s) (hμs : timeMeasure s ≠ ∞) :
    Dual →ₗ[ℝ] Field timeMeasure where
  toFun := step timeMeasure s hs hμs
  map_add' _ _ := indicatorConstLp_add.symm
  map_smul' c a := by
    change step timeMeasure s hs hμs (c • a) = c • step timeMeasure s hs hμs a
    apply Lp.ext
    filter_upwards [step_ae timeMeasure s hs hμs (c • a),
      step_ae timeMeasure s hs hμs a, Lp.coeFn_smul c (step timeMeasure s hs hμs a)]
      with t h1 h2 h3
    rw [h1, h3, Pi.smul_apply, h2]
    by_cases ht : t ∈ s <;> simp [Set.indicator, ht]

def jetMap (n m : ℕ) (T : ℝ≥0) (j : Fin (size n)) (q : ℕ) : Test n →ₗ[ℝ] Test n :=
  (q.factorial:ℝ)⁻¹ • ((clampBefore n j).toLinearMap.comp
    (((MultivariateFactorialDomain.polynomialDerivative (Pi.single j 1)).toLinearMap ^ q).comp
      (HigherHeatDyadicConditioning.localProjection m T n
        (HigherHeatDyadicConditioning.initialPast n (j.val+1)))))

theorem jetMap_apply (n m : ℕ) (T : ℝ≥0) (j : Fin (size n)) (q : ℕ) (P : Test n) :
    jetMap n m T j q P = predictableJet n m T j q P := by
  simp only [jetMap, LinearMap.smul_apply, LinearMap.comp_apply, Module.End.pow_apply]
  rfl

def nativeMap (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (q : ℕ) :
    Test n →ₗ[ℝ] Field timeMeasure :=
  ∑ j : Fin (size n), (stepMap (gridCell n j) (gridCell_measurable n j) (gridCell_finite n j)).comp
    ((pairing m hm T hT).toLinearMap.comp
      (core.comp ((cylinderOf n).toLinearMap.comp (jetMap n m T j q))))

theorem nativeMap_apply (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : ℕ) (P : Test n) : nativeMap n m hm T hT q P =
      adaptedField n m hm T hT (fun j => predictableJet n m T j q P) := by
  simp only [nativeMap, LinearMap.sum_apply, LinearMap.comp_apply, jetMap_apply]
  rfl

theorem refined_add (b : ℕ) (P Q : Test b) (n : ℕ) :
    refinedInput b (P+Q) n = refinedInput b P n + refinedInput b Q n := by
  by_cases hn : b ≤ n
  · simp only [refinedInput, dif_pos hn, transfer_add]
  · simp only [refinedInput, dif_neg hn, zero_add]

theorem refined_smul (b : ℕ) (c : ℝ) (P : Test b) (n : ℕ) :
    refinedInput b (c • P) n = c • refinedInput b P n := by
  by_cases hn : b ≤ n
  · simp only [refinedInput, dif_pos hn]
    exact (transition b n hn).toLinearMap.map_smul c P
  · simp only [refinedInput, dif_neg hn, smul_zero]

theorem field_add (b : ℕ) (P Q : Test b) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (q : ℕ) :
    field b (P+Q) m hm T hT q = field b P m hm T hT q + field b Q m hm T hT q := by
  apply tendsto_nhds_unique (field_tendsto b (P+Q) m hm T hT q)
  have h := (field_tendsto b P m hm T hT q).add (field_tendsto b Q m hm T hT q)
  simpa only [← nativeMap_apply, refined_add, map_add] using h

theorem field_smul (b : ℕ) (c : ℝ) (P : Test b) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (q : ℕ) :
    field b (c • P) m hm T hT q = c • field b P m hm T hT q := by
  apply tendsto_nhds_unique (field_tendsto b (c • P) m hm T hT q)
  have h := (field_tendsto b P m hm T hT q).const_smul c
  simpa only [← nativeMap_apply, refined_smul, map_smul] using h

def gridMap (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (q b : ℕ) :
    Test b →ₗ[ℝ] Field timeMeasure where
  toFun P := field b P m hm T hT q
  map_add' P Q := field_add b P Q m hm T hT q
  map_smul' c P := field_smul b c P m hm T hT q

theorem field_transfer (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (q i j : ℕ)
    (hij : i ≤ j) (P : Test i) :
    field j (transfer i j hij P) m hm T hT q = field i P m hm T hT q := by
  apply tendsto_nhds_unique (field_tendsto j (transfer i j hij P) m hm T hT q)
  apply (field_tendsto i P m hm T hT q).congr'
  filter_upwards [eventually_ge_atTop j] with n hn
  simp only [refinedInput, dif_pos hn, dif_pos (hij.trans hn),
    HigherHeatCylindricalConditioning.transfer_trans]

def cylinderMap (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (q : ℕ) :
    Cylinder →ₗ[ℝ] Field timeMeasure :=
  DirectLimit.Module.lift ℝ ℕ Test transition (gridMap m hm T hT q)
    (fun i j h P => field_transfer m hm T hT q i j h P)

theorem cylinderMap_apply (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q b : ℕ) (P : Test b) :
    cylinderMap m hm T hT q (cylinderOf b P) = field b P m hm T hT q := rfl

def bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (q : ℕ) : ℝ :=
  ‖pairing m hm T hT‖ * (q.factorial:ℝ)⁻¹ * Real.exp (T:ℝ)

theorem cylinderMap_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : ℕ) (F : Cylinder) : ‖cylinderMap m hm T hT q F‖ ≤ bound m hm T hT q * ‖core F‖ := by
  apply HigherHeatCylindricalConditioning.tail_induction 0 (fun F =>
    ‖cylinderMap m hm T hT q F‖ ≤ bound m hm T hT q * ‖core F‖) _ F
  intro b _ P
  rw [cylinderMap_apply]
  exact (field_bound b P m hm T hT q).trans_eq (by unfold bound; ring)

def completed (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (q : ℕ) :
    Domain →L[ℝ] Field timeMeasure := (cylinderMap m hm T hT q).extendOfNorm core

theorem completed_core (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : ℕ) (F : Cylinder) : completed m hm T hT q (core F) = cylinderMap m hm T hT q F :=
  LinearMap.extendOfNorm_eq core_dense ⟨bound m hm T hT q, cylinderMap_bound m hm T hT q⟩ F

theorem completed_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : ℕ) (u : Domain) : ‖completed m hm T hT q u‖ ≤ bound m hm T hT q * ‖u‖ :=
  LinearMap.norm_extendOfNorm_apply_le core_dense _ (cylinderMap_bound m hm T hT q) u

theorem completed_mem (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : ℕ) (u : Domain) :
    completed m hm T hT q u ∈ HigherHeatAdaptedIntegralClosure.space m hm T hT := by
  have hc := ((HigherHeatAdaptedIntegralClosure.stepSpan m hm T hT).isClosed_topologicalClosure).preimage
    (completed m hm T hT q).continuous
  have hs : closure (Set.range core) ⊆
      {v | completed m hm T hT q v ∈ HigherHeatAdaptedIntegralClosure.space m hm T hT} := by
    apply hc.closure_subset_iff.mpr
    rintro _ ⟨F, rfl⟩
    change completed m hm T hT q (core F) ∈ HigherHeatAdaptedIntegralClosure.space m hm T hT
    rw [completed_core]
    apply HigherHeatCylindricalConditioning.tail_induction 0 (fun F =>
      cylinderMap m hm T hT q F ∈ HigherHeatAdaptedIntegralClosure.space m hm T hT) _ F
    intro b _ P
    rw [cylinderMap_apply]
    exact field_mem b P m hm T hT q
  apply hs
  rw [core_dense.closure_range]
  trivial

end OperatorDerivativeRewrite.Foundation.HigherHeatMultitimeFieldMaps
