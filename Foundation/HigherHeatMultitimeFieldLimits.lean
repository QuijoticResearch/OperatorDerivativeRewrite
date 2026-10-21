import Foundation.HigherHeatCausalFieldCauchy

/-! Genuine L1 limits of every channel for each fixed multitime polynomial.
This supplies coefficient convergence, not yet a completed-observable reconstruction. -/
noncomputable section
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatMultitimeFieldLimits
open Filter HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain HigherHeatWeakTimeAdjoint
open HigherHeatCausalFieldCauchy HigherHeatRefinedPredictableJets HigherHeatRefinementDegree
open HigherHeatDyadicStepAgreement HigherHeatPredictableJetBounds HigherHeatCausalJetIdentification

theorem refined_input_step (b : ℕ) (P : Test b) (n : ℕ) (hn : b ≤ n) :
    refinedInput b P (n+1) = step n (refinedInput b P n) := by
  rw [refinedInput, dite_eq_left (hn.trans (Nat.le_succ n)), refinedInput, dite_eq_left hn]
  exact transfer_succ b n hn P

theorem refined_fields_cauchy (b : ℕ) (P : Test b) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (q : ℕ) :
    CauchySeq (fun k => causalField (b+k) m hm T hT q (refinedInput b P (b+k))) := by
  obtain ⟨K, hK, hc⟩ := causal_fields_step_bound m hm T hT P.totalDegree
  let C : ℝ := (q.factorial:ℝ)⁻¹*K*‖core (cylinderOf b P)‖
  apply cauchySeq_of_dist_le_of_summable
    (fun k => C*(HigherHeatDyadicLaws.duration 1 (b+k+1):ℝ))
  · intro k
    rw [dist_comm, dist_eq_norm]
    have he : b+(k+1) = b+k+1 := by omega
    rw [he, refined_input_step b P (b+k) (by omega)]
    apply (hc (b+k) (refinedInput b P (b+k)) (refined_input_degree b P (b+k)) q).trans
    calc
      _ ≤ (q.factorial:ℝ)⁻¹*K*(HigherHeatDyadicLaws.duration 1 (b+k+1):ℝ)*
          ‖core (cylinderOf b P)‖ :=
        mul_le_mul_of_nonneg_left (refined_core_bound b P (b+k)) (by positivity)
      _ = _ := by dsimp [C]; ring
  · have hg : Summable (fun k : ℕ => (1/2:ℝ)^k) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have he : (fun k : ℕ => (HigherHeatDyadicLaws.duration 1 (b+k+1):ℝ)) =
        fun k => (1/2:ℝ)^(b+1)*(1/2:ℝ)^k := by
      funext k
      rw [HigherHeatEarlyDualContinuity.duration_coe]
      norm_num only [NNReal.coe_one, one_mul]
      rw [show b+k+1 = b+1+k by omega, pow_add]
    exact (he ▸ hg.mul_left ((1/2:ℝ)^(b+1))).mul_left C

theorem causal_fields_tendsto (b : ℕ) (P : Test b) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (q : ℕ) :
    ∃ A : Field timeMeasure, Tendsto
      (fun n => causalField n m hm T hT q (refinedInput b P n)) atTop (𝓝 A) := by
  obtain ⟨A, hA⟩ := cauchySeq_tendsto_of_complete (refined_fields_cauchy b P m hm T hT q)
  refine ⟨A, (tendsto_add_atTop_iff_nat b).mp ?_⟩
  convert hA using 1
  funext k
  rw [Nat.add_comm k b]

theorem native_fields_tendsto (b : ℕ) (P : Test b) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (q : ℕ) :
    ∃ A : Field timeMeasure, Tendsto
      (fun n => adaptedField n m hm T hT
        (fun j => predictableJet n m T j q (refinedInput b P n))) atTop (𝓝 A) := by
  obtain ⟨A, hA⟩ := causal_fields_tendsto b P m hm T hT q
  refine ⟨A, ?_⟩
  have h := hA.sub (causal_field_approximation b P m hm T hT q)
  simpa only [causalField, sub_sub_cancel, sub_zero] using h

end OperatorDerivativeRewrite.Foundation.HigherHeatMultitimeFieldLimits
