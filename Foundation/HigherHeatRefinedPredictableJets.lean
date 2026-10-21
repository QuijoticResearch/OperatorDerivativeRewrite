import Foundation.HigherHeatMultitimeJetTelescope

/-! Uniform actual predictable-jet bounds along refinements of one fixed
multitime cylinder. Every centered channel at or above the heat order vanishes. -/
noncomputable section
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatRefinedPredictableJets
open Filter HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain HigherHeatCompletedPairing
open HigherHeatPairedDualCausality HigherHeatWeakTimeAdjoint HigherHeatPredictableJetBounds
open HigherHeatPredictableJetFields HigherHeatAdaptedStepDuality HigherHeatCenteredPowerLimits

def refinedInput (b : ℕ) (P : Test b) (n : ℕ) : Test n :=
  if hn : b ≤ n then transfer b n hn P else 0

theorem refined_core (b : ℕ) (P : Test b) (n : ℕ) (hn : b ≤ n) :
    core (cylinderOf n (refinedInput b P n)) = core (cylinderOf b P) := by
  rw [refinedInput, dif_pos hn, cylinder_refinement]

theorem refined_core_bound (b : ℕ) (P : Test b) (n : ℕ) :
    ‖core (cylinderOf n (refinedInput b P n))‖ ≤ ‖core (cylinderOf b P)‖ := by
  by_cases hn : b ≤ n
  · rw [refined_core b P n hn]
  · rw [refinedInput, dif_neg hn, map_zero, map_zero, norm_zero]
    exact norm_nonneg _

theorem refined_jet_bound (b : ℕ) (P : Test b) (n m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (j : Fin (size n)) (q : ℕ) :
    ‖pairing m hm T hT (core (cylinderOf n (predictableJet n m T j q (refinedInput b P n))))‖ ≤
      ‖pairing m hm T hT‖*((q.factorial:ℝ)⁻¹*Real.exp (T:ℝ)*‖core (cylinderOf b P)‖) := by
  apply (jet_dual_bound n m hm T hT j q _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact mul_le_mul_of_nonneg_left (refined_core_bound b P n) (by positivity)

theorem refined_field_bound (b : ℕ) (P : Test b) (n m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (q : ℕ) :
    ‖HigherHeatDyadicStepAgreement.adaptedField n m hm T hT
      (fun j => predictableJet n m T j q (refinedInput b P n))‖ ≤
      ‖pairing m hm T hT‖*((q.factorial:ℝ)⁻¹*Real.exp (T:ℝ)*‖core (cylinderOf b P)‖) := by
  apply (native_field_bound n m hm T hT q _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact mul_le_mul_of_nonneg_left (refined_core_bound b P n) (by positivity)

theorem critical_refined_vanish (b : ℕ) (P : Test b) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => pairing m hm T hT (core (cylinderOf n
      (centeredPower n m T (2*m) (fun j => predictableJet n m T j (2*m) (refinedInput b P n))))))
      atTop (𝓝 (0:Dual)) := by
  exact critical_centered_vanish m hm T hT _
    (fun n => predictable_jets_adapted n m T (2*m) _) _
    (fun n j => refined_jet_bound b P n m hm T hT j (2*m))

theorem higher_refined_vanish (b : ℕ) (P : Test b) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (r : ℕ) (hr : 2*m ≤ r) :
    Tendsto (fun n => pairing m hm T hT (core (cylinderOf n
      (centeredPower n m T (r+1) (fun j => predictableJet n m T j (r+1) (refinedInput b P n))))))
      atTop (𝓝 (0:Dual)) := by
  exact higher_centered_vanish m hm T hT _
    (fun n => predictable_jets_adapted n m T (r+1) _) r hr _
    (fun n j => refined_jet_bound b P n m hm T hT j (r+1))

end OperatorDerivativeRewrite.Foundation.HigherHeatRefinedPredictableJets
