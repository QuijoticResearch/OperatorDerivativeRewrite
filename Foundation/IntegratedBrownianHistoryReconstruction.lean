import Foundation.IntegratedBrownianStatePrediction
import Foundation.BrownianHistoryRecoveryCompactness

/-! Backward L2 differentiation reconstructs Brownian state from integrated history. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.IntegratedBrownianHistoryReconstruction
open GaussianTimeSpaceHermite InfiniteGaussian GaussianTimeHilbert SeparableHilbertEmbedding IntegratedBrownianStatePrediction
open GaussianWickConditionalProjection GaussianConditionalGraph GaussianSingleObservationPrediction
attribute [local instance] timeHilbert_secondCountable

def quotient (a s : ℝ≥0) : TimeHilbert := ((s : ℝ)-a)⁻¹ • (integratedVector s-integratedVector a)

theorem quotient_error_bound (a s : ℝ≥0) (has : a<s) :
    ‖quotient a s-timeVector s‖≤Real.sqrt ((s : ℝ)-a) := by
  have hgap : 0<(s : ℝ)-a := sub_pos.mpr has
  have hh : ‖quotient a s-timeVector s‖≤‖intervalVector a s‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_sub (quotient a s) (timeVector s),
      Lp.coeFn_smul (((s : ℝ)-a)⁻¹) (integratedVector s-integratedVector a),
      Lp.coeFn_sub (integratedVector s) (integratedVector a),
      integratedVector_coeFn s,integratedVector_coeFn a,timeVector_coeFn s,intervalVector_coeFn a s] with x he hq hd hs ha hb hi
    rw [he,Pi.sub_apply]
    change ‖(quotient a s) x-timeVector s x‖≤_
    rw [quotient,hq,Pi.smul_apply,hd,Pi.sub_apply,hs,ha,hb,hi]
    simp only [Real.norm_eq_abs,smul_eq_mul]
    by_cases hxs : x∈Ioc 0 (s : ℝ)
    · by_cases hxa : x∈Ioc 0 (a : ℝ)
      · have hnon : x∉Ioc (a : ℝ) s := fun hx => not_lt_of_ge hxa.2 hx.1
        simp only [indicator_of_mem hxs,indicator_of_mem hxa,indicator_of_notMem hnon]
        rw [show (s : ℝ)-x-((a : ℝ)-x)=(s : ℝ)-a by ring,inv_mul_cancel₀ hgap.ne']
        norm_num
      · have hax : (a : ℝ)<x := lt_of_not_ge (fun hx => hxa ⟨hxs.1,hx⟩)
        have hxi : x∈Ioc (a : ℝ) s := ⟨hax,hxs.2⟩
        simp only [indicator_of_mem hxs,indicator_of_notMem hxa,indicator_of_mem hxi,sub_zero,abs_one]
        have hl : 0≤((s : ℝ)-a)⁻¹*((s : ℝ)-x) := mul_nonneg (inv_nonneg.mpr hgap.le) (sub_nonneg.mpr hxs.2)
        have hu : ((s : ℝ)-a)⁻¹*((s : ℝ)-x)≤1 := by
          calc
            _≤((s : ℝ)-a)⁻¹*((s : ℝ)-a) := mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hgap.le)
            _=1 := inv_mul_cancel₀ hgap.ne'
        exact abs_le.mpr ⟨by linarith,by linarith⟩
    · have hxa : x∉Ioc 0 (a : ℝ) := fun hx => hxs ⟨hx.1,hx.2.trans has.le⟩
      have hxi : x∉Ioc (a : ℝ) s := fun hx => hxs ⟨lt_of_le_of_lt a.coe_nonneg hx.1,hx.2⟩
      simp [hxs,hxa,hxi]
  have he : ‖intervalVector a s‖^2=(s : ℝ)-a := by
    rw [← timeVector_sub a s has.le,timeVector_sub_norm_sq a s has.le]
  have hn : ‖intervalVector a s‖=Real.sqrt ((s : ℝ)-a) := by
    rw [← he,Real.sqrt_sq (norm_nonneg _)]
  exact hh.trans hn.le

def probeTime (s : ℝ≥0) (n : ℕ) : ℝ≥0 := s*((n : ℝ≥0)/((n : ℝ≥0)+1))

theorem probeTime_gap (s : ℝ≥0) (n : ℕ) : (s : ℝ)-(probeTime s n : ℝ)=(s : ℝ)/(n+1 : ℝ) := by
  simp only [probeTime,NNReal.coe_mul,NNReal.coe_div,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]
  field_simp
  ring

theorem probeTime_lt (s : ℝ≥0) (hs : 0<s) (n : ℕ) : probeTime s n<s := by
  have hgap := probeTime_gap s n
  have hp : 0<(s : ℝ)/(n+1 : ℝ) := by positivity
  exact_mod_cast (show (probeTime s n : ℝ)<s by linarith)

theorem quotient_tendsto (s : ℝ≥0) (hs : 0<s) :
    Tendsto (fun n => quotient (probeTime s n) s) atTop (𝓝 (timeVector s)) := by
  have hn : Tendsto (fun n : ℕ => (n+1 : ℝ)) atTop atTop := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hg : Tendsto (fun n : ℕ => (s : ℝ)/(n+1 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,div_eq_mul_inv,mul_zero] using tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hn)
  have hlim : Tendsto (fun n : ℕ => Real.sqrt ((s : ℝ)-(probeTime s n : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_zero,probeTime_gap] using Real.continuous_sqrt.continuousAt.tendsto.comp hg
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => quotient_error_bound _ _ (probeTime_lt s hs n)) hlim

theorem brownian_mem_integrated_history (s : ℝ≥0) :
    brownianDirection s∈sourceSpan (integratedPastDirections s) := by
  by_cases hs : s=0
  · subst s
    simp only [brownianDirection,timeVector_zero,map_zero]
    exact (sourceSpan (integratedPastDirections 0)).zero_mem
  · have hs' : 0<s := pos_iff_ne_zero.mpr hs
    apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
      ((hilbertEmbedding TimeHilbert).continuous.continuousAt.tendsto.comp (quotient_tendsto s hs'))
    apply Eventually.of_forall
    intro n
    change hilbertEmbedding TimeHilbert (((s : ℝ)-(probeTime s n : ℝ))⁻¹ •
      (integratedVector s-integratedVector (probeTime s n)))∈_
    rw [map_smul,map_sub]
    apply (sourceSpan (integratedPastDirections s)).smul_mem
    apply (sourceSpan (integratedPastDirections s)).sub_mem
    · exact (Submodule.span ℝ (range (integratedPastDirections s))).le_topologicalClosure
        (Submodule.subset_span ⟨⟨s,by simp⟩,rfl⟩)
    · exact (Submodule.span ℝ (range (integratedPastDirections s))).le_topologicalClosure
        (Submodule.subset_span ⟨⟨probeTime s n,(probeTime_lt s hs' n).le⟩,rfl⟩)

theorem integrated_history_source_projection (s t : ℝ≥0) (hst : s≤t) :
    sourceProjection (integratedPastDirections s) (direction t)=forecastDirection s t := by
  apply SPDEWickBrownianPrediction.sourceProjection_eq_of_pairings
  · apply (sourceSpan (integratedPastDirections s)).add_mem
    · exact (Submodule.span ℝ (range (integratedPastDirections s))).le_topologicalClosure
        (Submodule.subset_span ⟨⟨s,by simp⟩,rfl⟩)
    · exact (sourceSpan (integratedPastDirections s)).smul_mem _ (brownian_mem_integrated_history s)
  · intro r
    exact direction_pairing r s t r.property hst true

theorem integrated_history_state_sufficient (s t : ℝ≥0) (hst : s≤t)
    (f : GaussianL2) (hf : f∈singleGenerated (direction t)) :
    conditionalProjection (integratedPastDirections s) f=conditionalProjection (currentDirections s) f := by
  apply GaussianExponentialMarkovPrediction.terminal_prediction_eq_of_sourceProjection_eq _ _ _ _ f hf
  rw [integrated_history_source_projection s t hst,current_source_projection s t hst]

theorem integrated_history_wick_prediction (s t : ℝ≥0) (hst : s≤t) (n : ℕ) :
    conditionalProjection (integratedPastDirections s) (wick (direction t) n)=
      (wick (forecastDirection s t) n : GaussianL2) := by
  rw [conditional_wick_projection,integrated_history_source_projection s t hst]

end OperatorDerivativeRewrite.Foundation.IntegratedBrownianHistoryReconstruction


