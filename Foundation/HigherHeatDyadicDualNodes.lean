import Foundation.HigherHeatDyadicDualLipschitz

/-! Simultaneous signed dual endpoint data including zero, with a global time Lipschitz bound. -/
noncomputable section
open scoped NNReal

namespace OperatorDerivativeRewrite.Foundation.HigherHeatDyadicDualNodes
open HigherHeatPolynomialCylinders HigherHeatPolynomialPathDomain HigherHeatAnalyticCylinderDomain
open HigherHeatCompletedPairing HigherHeatDyadicDualLipschitz HigherHeatContinuousCylinders
open HigherHeatAnalyticTimeObstruction HigherHeatEarlyDualContinuity HigherHeatPairedDualCausality
open Filter
open scoped Topology

theorem dualPosition_zero_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (r : Fin (size n)) :
    ‖dualPosition m hm T hT n r‖ ≤
      ((2*m:ℕ):ℝ) * (T:ℝ) * Real.exp (T:ℝ) * sampleTime n r := by
  have hfirst : Tendsto (fun k => dualPosition m hm T hT k (firstIndex k)) atTop (𝓝 0) :=
    first_pairing_tendsto m hm T hT
  have hv := Filter.Tendsto.norm (E := Dual) hfirst
  have hlow : Tendsto (fun k => ‖dualPosition m hm T hT n r‖ -
      ‖dualPosition m hm T hT k (firstIndex k)‖) atTop (𝓝 ‖dualPosition m hm T hT n r‖) := by
    simpa only [ContinuousLinearMap.opNorm_zero, sub_zero] using
      (tendsto_const_nhds (x := ‖dualPosition m hm T hT n r‖)).sub hv
  have hupp : Tendsto (fun k => ‖dualPosition m hm T hT n r‖ +
      ‖dualPosition m hm T hT k (firstIndex k)‖) atTop (𝓝 ‖dualPosition m hm T hT n r‖) := by
    simpa only [ContinuousLinearMap.opNorm_zero, add_zero] using
      (tendsto_const_nhds (x := ‖dualPosition m hm T hT n r‖)).add hv
  have hl : Tendsto (fun k => ‖dualPosition m hm T hT n r -
      dualPosition m hm T hT k (firstIndex k)‖) atTop (𝓝 ‖dualPosition m hm T hT n r‖) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
      (Eventually.of_forall (fun k => norm_sub_norm_le (dualPosition m hm T hT n r) (dualPosition m hm T hT k (firstIndex k))))
      (Eventually.of_forall (fun k => norm_sub_le (dualPosition m hm T hT n r) (dualPosition m hm T hT k (firstIndex k))))
  have hr : Tendsto (fun k => ((2*m:ℕ):ℝ) * (T:ℝ) * Real.exp (T:ℝ) *
      |sampleTime n r-sampleTime k (firstIndex k)|) atTop
      (𝓝 (((2*m:ℕ):ℝ) * (T:ℝ) * Real.exp (T:ℝ) * sampleTime n r)) := by
    have hh := (tendsto_const_nhds (x := ((2*m:ℕ):ℝ) * (T:ℝ) * Real.exp (T:ℝ))).mul
      ((tendsto_const_nhds (x := sampleTime n r)).sub first_time_tendsto).abs
    simpa only [sub_zero, abs_of_pos (sampleTime_pos n r)] using hh
  exact le_of_tendsto_of_tendsto hl hr
    (Eventually.of_forall (fun k => dualPosition_bound m hm T hT n r k (firstIndex k)))

def dualNode (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (o : Option (Fin (size n))) : Dual := o.elim 0 (dualPosition m hm T hT n)

theorem dualNode_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n l : ℕ) (a : Option (Fin (size n))) (b : Option (Fin (size l))) :
    ‖dualNode m hm T hT n a-dualNode m hm T hT l b‖ ≤
      ((2*m:ℕ):ℝ) * (T:ℝ) * Real.exp (T:ℝ) * |interpolationNode n a-interpolationNode l b| := by
  have hz (u : Dual) : (0:Dual)-u = -u := by
    ext v
    simp only [sub_apply, zero_apply, neg_apply, zero_sub]
  have hs (u : Dual) : u-(0:Dual) = u := by
    ext v
    simp only [sub_apply, zero_apply, sub_zero]
  cases a with
  | none =>
    cases b with
    | none =>
      change ‖(0:Dual)-(0:Dual)‖ ≤ _
      rw [hs, ContinuousLinearMap.opNorm_zero]
      simp only [interpolationNode, sub_self, abs_zero, mul_zero]
      exact le_rfl
    | some s =>
      change ‖(0:Dual)-dualPosition m hm T hT l s‖ ≤
        ((2*m:ℕ):ℝ) * (T:ℝ) * Real.exp (T:ℝ) * |0-sampleTime l s|
      rw [hz, ContinuousLinearMap.opNorm_neg, zero_sub, abs_neg, abs_of_pos (sampleTime_pos l s)]
      exact dualPosition_zero_bound m hm T hT l s
  | some r =>
    cases b with
    | none =>
      change ‖dualPosition m hm T hT n r-(0:Dual)‖ ≤
        ((2*m:ℕ):ℝ) * (T:ℝ) * Real.exp (T:ℝ) * |sampleTime n r-0|
      rw [hs, sub_zero, abs_of_pos (sampleTime_pos n r)]
      exact dualPosition_zero_bound m hm T hT n r
    | some s => exact dualPosition_bound m hm T hT n r l s

theorem dualNode_same_time (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n l : ℕ) (a : Option (Fin (size n))) (b : Option (Fin (size l)))
    (h : interpolationNode n a = interpolationNode l b) :
    dualNode m hm T hT n a = dualNode m hm T hT l b := by
  have hb := dualNode_bound m hm T hT n l a b
  rw [h, sub_self, abs_zero, mul_zero] at hb
  have he := le_antisymm hb (ContinuousLinearMap.opNorm_nonneg _)
  exact sub_eq_zero.mp ((ContinuousLinearMap.opNorm_zero_iff _).mp he)

theorem interpolationNode_mem (n : ℕ) (o : Option (Fin (size n))) :
    interpolationNode n o ∈ Set.Icc (0:ℝ) 1 := by
  cases o with
  | none => exact ⟨le_rfl, zero_le_one⟩
  | some i => exact ⟨(sampleTime_pos n i).le, (timeEmbedding n i).property.2⟩

end OperatorDerivativeRewrite.Foundation.HigherHeatDyadicDualNodes
