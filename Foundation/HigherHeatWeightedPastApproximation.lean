import Foundation.HigherHeatWeightedPastFields

/-! Genuine L1 convergence with the time weight sampled at the RIGHT endpoint
and the polynomial path value sampled at the LEFT endpoint. -/
noncomputable section
open scoped NNReal ENNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatWeightedPastApproximation
open MeasureTheory Filter HigherHeatWeakTimeAdjoint HigherHeatPairedDualCausality
open HigherHeatAnalyticCylinderDomain HigherHeatPolynomialCylinders HigherHeatCompletedPairing
open HigherHeatDyadicStepAgreement HigherHeatQuadraticItoData HigherHeatQuadraticItoFields
open HigherHeatPolynomialCurveAgreement HigherHeatDyadicTimeDensity HigherHeatWeightedPastFields

theorem weighted_fields_tendsto (w : C(Interval,ℝ)) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (d : ℕ) :
    Tendsto (fun n => adaptedField n m hm T hT (weightedPast w n d)) atTop
      (𝓝 (weightedField w m hm T hT d)) := by
  let f : Interval × Interval → Dual := fun z => w z.1 • coordinateCurve m hm T hT d z.2
  have hc : Continuous f := (w.continuous.comp continuous_fst).smul
    ((coordinateCurve m hm T hT d).continuous.comp continuous_snd)
  have hu := CompactSpace.uniformContinuous_of_continuous hc
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := Metric.uniformContinuous_iff.mp hu (ε/2) (by positivity)
  have hn : ∀ᶠ n in atTop, (HigherHeatDyadicLaws.duration 1 n:ℝ) < δ :=
    (HigherHeatEarlyDualContinuity.duration_tendsto 1).eventually (gt_mem_nhds hδ)
  filter_upwards [hn] with n hn
  have hb : ∀ᵐ t : ℝ ∂timeMeasure,
      ‖(adaptedField n m hm T hT (weightedPast w n d) - weightedField w m hm T hT d) t‖ ≤ ε/2 := by
    filter_upwards [Lp.coeFn_sub (adaptedField n m hm T hT (weightedPast w n d))
      (weightedField w m hm T hT d), adaptedField_cell_ae n m hm T hT (weightedPast w n d),
      weightedField_ae w m hm T hT d, time_ae] with t hs hf hw ht
    obtain ⟨j, hj⟩ := cell_exists n t ht
    have hd := node_cell_dist n j t hj
    have hp : dist (rightNode n j, leftNode n j)
        (Set.projIcc 0 1 (by norm_num) t, Set.projIcc 0 1 (by norm_num) t) < δ := by
      rw [Prod.dist_eq]
      exact (max_le hd.2 hd.1).trans_lt hn
    have he := hh hp
    rw [hs]
    change ‖adaptedField n m hm T hT (weightedPast w n d) t - weightedField w m hm T hT d t‖ ≤ _
    rw [hf j hj, hw, weightedPast_curve]
    change ‖f (rightNode n j, leftNode n j) -
      f (Set.projIcc 0 1 (by norm_num) t, Set.projIcc 0 1 (by norm_num) t)‖ ≤ ε/2
    simpa only [dist_eq_norm] using he.le
  have hh := Lp.norm_le_of_ae_bound (E := Dual) (p := 1) (μ := timeMeasure)
    (f := adaptedField n m hm T hT (weightedPast w n d) - weightedField w m hm T hT d)
    (by positivity) hb
  have hmass : (measureUnivNNReal timeMeasure:ℝ) = 1 := by simp [measureUnivNNReal, timeMeasure]
  have hb' : ‖adaptedField n m hm T hT (weightedPast w n d) - weightedField w m hm T hT d‖ ≤ ε/2 := by
    simpa only [ENNReal.toReal_one, inv_one, Real.rpow_one, NNReal.rpow_one, hmass, one_mul] using hh
  rw [dist_eq_norm]
  exact hb'.trans_lt (by linarith)

theorem weighted_field_mem (w : C(Interval,ℝ)) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (d : ℕ) :
    weightedField w m hm T hT d ∈ HigherHeatAdaptedIntegralClosure.space m hm T hT := by
  let S := HigherHeatAdaptedIntegralClosure.stepSpan m hm T hT
  apply S.isClosed_topologicalClosure.mem_of_tendsto (weighted_fields_tendsto w m hm T hT d)
  exact Eventually.of_forall (fun n =>
    (HigherHeatAdaptedIntegralClosure.native m hm T hT n (weightedPast w n d)
      (weightedPast_adapted w n d)).property)

end OperatorDerivativeRewrite.Foundation.HigherHeatWeightedPastApproximation
