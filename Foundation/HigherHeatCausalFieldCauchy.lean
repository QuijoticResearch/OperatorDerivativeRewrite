import Foundation.HigherHeatCausalRefinementBound
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Genuine L1 adjacent-refinement estimates for the actual causal fields. -/
noncomputable section
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatCausalFieldCauchy
open MeasureTheory Filter HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain
open HigherHeatCompletedPairing HigherHeatPairedDualCausality HigherHeatWeakTimeAdjoint
open HigherHeatDyadicStepAgreement HigherHeatQuadraticItoFields HigherHeatGridDoubling
open HigherHeatCausalJetIdentification HigherHeatCausalRefinementBound HigherHeatRefinedPredictableJets

theorem fine_cell_subset (n : ℕ) (i : Fin (size (n+1))) :
    gridCell (n+1) i ⊆ gridCell n (pairBlock i) := by
  intro t ht
  have hd : (HigherHeatDyadicLaws.duration 1 n:ℝ) =
      2*(HigherHeatDyadicLaws.duration 1 (n+1):ℝ) := by
    have h := congrArg (fun x : ℝ≥0 => (x:ℝ)) (HigherHeatDyadicLaws.duration_halves 1 n)
    simp only [NNReal.coe_add] at h
    linarith
  have hl : 2*(pairBlock i).val ≤ i.val := by simp only [pairBlock]; omega
  have hr : i.val+1 ≤ 2*((pairBlock i).val+1) := by simp only [pairBlock]; omega
  have hlr : 2*((pairBlock i).val:ℝ) ≤ (i.val:ℝ) := by exact_mod_cast hl
  have hrr : (i.val:ℝ)+1 ≤ 2*((pairBlock i).val+1:ℝ) := by exact_mod_cast hr
  have h1 := mul_le_mul_of_nonneg_right hlr (HigherHeatDyadicLaws.duration 1 (n+1)).coe_nonneg
  have h2 := mul_le_mul_of_nonneg_right hrr (HigherHeatDyadicLaws.duration 1 (n+1)).coe_nonneg
  change (i.val:ℝ)*(HigherHeatDyadicLaws.duration 1 (n+1):ℝ) < t ∧
    t ≤ ((i.val:ℝ)+1)*(HigherHeatDyadicLaws.duration 1 (n+1):ℝ) at ht
  change ((pairBlock i).val:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ) < t ∧
    t ≤ (((pairBlock i).val:ℝ)+1)*(HigherHeatDyadicLaws.duration 1 n:ℝ)
  rw [hd]
  constructor <;> nlinarith [ht.1, ht.2]

def causalField (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (q : ℕ)
    (P : Test n) : Field timeMeasure :=
  adaptedField n m hm T hT (fun j => causalJet n m T j q P)

theorem causal_fields_step_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (D : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n (P : Test n), P.totalDegree ≤ D → ∀ q : ℕ,
      ‖causalField (n+1) m hm T hT q (step n P)-causalField n m hm T hT q P‖ ≤
        (q.factorial:ℝ)⁻¹*K*(HigherHeatDyadicLaws.duration 1 (n+1):ℝ)*‖core (cylinderOf n P)‖ := by
  obtain ⟨K, hK, hc⟩ := causal_refinement_bound m hm T hT D
  refine ⟨K, hK, ?_⟩
  intro n P hD q
  have hb : ∀ᵐ t : ℝ ∂timeMeasure,
      ‖(causalField (n+1) m hm T hT q (step n P)-causalField n m hm T hT q P) t‖ ≤
        (q.factorial:ℝ)⁻¹*K*(HigherHeatDyadicLaws.duration 1 (n+1):ℝ)*‖core (cylinderOf n P)‖ := by
    filter_upwards [Lp.coeFn_sub (causalField (n+1) m hm T hT q (step n P))
      (causalField n m hm T hT q P),
      adaptedField_cell_ae (n+1) m hm T hT (fun j => causalJet (n+1) m T j q (step n P)),
      adaptedField_cell_ae n m hm T hT (fun j => causalJet n m T j q P),
      HigherHeatQuadraticItoFields.time_ae] with t hs hf hg ht
    obtain ⟨i, hi⟩ := HigherHeatQuadraticItoData.cell_exists (n+1) t ht
    rw [hs]
    change ‖adaptedField (n+1) m hm T hT _ t-adaptedField n m hm T hT _ t‖ ≤ _
    rw [hf i hi, hg (pairBlock i) (fine_cell_subset n i hi)]
    exact hc n P hD i q
  have hh := Lp.norm_le_of_ae_bound (E := Dual) (p := 1) (μ := timeMeasure)
    (f := causalField (n+1) m hm T hT q (step n P)-causalField n m hm T hT q P)
    (by positivity) hb
  have hmass : (measureUnivNNReal timeMeasure:ℝ) = 1 := by simp [measureUnivNNReal, timeMeasure]
  simpa only [ENNReal.toReal_one, inv_one, Real.rpow_one, NNReal.rpow_one, hmass, one_mul] using hh

end OperatorDerivativeRewrite.Foundation.HigherHeatCausalFieldCauchy
