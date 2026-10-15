import Foundation.GaussianExponentialMarkovPrediction
import Foundation.FractionalCurrentObservationObstruction

/-! Integrated Brownian terminal prediction requires a two-coordinate current state. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.IntegratedBrownianStatePrediction
open InfiniteGaussian GaussianTimeHilbert SeparableHilbertEmbedding GaussianTimeSpaceHermite
open GaussianConditionalGraph GaussianWickConditionalProjection GaussianSingleObservationPrediction
attribute [local instance] timeHilbert_secondCountable

def integratedVector (t : ℝ≥0) : TimeHilbert := GaussianPowerVolterra.vector 1 (by norm_num) t

theorem integratedVector_coeFn (t : ℝ≥0) : integratedVector t =ᵐ[volume]
    (Ioc 0 (t : ℝ)).indicator (fun x => (t : ℝ)-x) := by
  simpa [integratedVector,GaussianPowerVolterra.kernel] using GaussianPowerVolterra.vector_coeFn 1 (by norm_num) t

def direction (t : ℝ≥0) : CoefficientSpace := hilbertEmbedding TimeHilbert (integratedVector t)
def brownianDirection (t : ℝ≥0) : CoefficientSpace := hilbertEmbedding TimeHilbert (timeVector t)

def currentDirections (s : ℝ≥0) : Bool → CoefficientSpace := fun b => if b then direction s else brownianDirection s
def pastDirections (s : ℝ≥0) : Bool × Iic s → CoefficientSpace := fun p => currentDirections p.2 p.1

def forecastDirection (s t : ℝ≥0) : CoefficientSpace := direction s+((t : ℝ)-s) • brownianDirection s

theorem profile_pairing (r s t : ℝ≥0) (hrs : r≤s) (hst : s≤t) (b : Bool) :
    inner ℝ (integratedVector t) (if b then integratedVector r else timeVector r)=
      inner ℝ (integratedVector s+((t : ℝ)-s) • timeVector s)
        (if b then integratedVector r else timeVector r) := by
  rw [L2_inner_eq_integral,L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [integratedVector_coeFn t,integratedVector_coeFn s,integratedVector_coeFn r,
    timeVector_coeFn s,timeVector_coeFn r,Lp.coeFn_add (integratedVector s) (((t : ℝ)-s) • timeVector s),
    Lp.coeFn_smul ((t : ℝ)-s) (timeVector s)] with x ht hs hr hbs hbr ha hsm
  rw [ha,Pi.add_apply,hsm,Pi.smul_apply,ht,hs,hbs]
  cases b <;> simp only [Bool.false_eq_true,if_false,if_true,hr,hbr,Real.inner_apply,smul_eq_mul]
  all_goals
    by_cases hx : x∈Ioc 0 (r : ℝ)
    · have hxs : x∈Ioc 0 (s : ℝ) := ⟨hx.1,hx.2.trans hrs⟩
      have hxt : x∈Ioc 0 (t : ℝ) := ⟨hx.1,hxs.2.trans hst⟩
      simp only [indicator_of_mem hx,indicator_of_mem hxs,indicator_of_mem hxt]
      ring
    · simp [hx]

theorem direction_pairing (r s t : ℝ≥0) (hrs : r≤s) (hst : s≤t) (b : Bool) :
    inner ℝ (direction t) (currentDirections r b)=inner ℝ (forecastDirection s t) (currentDirections r b) := by
  have h := profile_pairing r s t hrs hst b
  cases b <;> simpa only [currentDirections,Bool.false_eq_true,if_false,if_true,direction,brownianDirection,
    forecastDirection,← map_smul,← map_add,LinearIsometry.inner_map_map] using h

theorem forecast_mem_current (s t : ℝ≥0) : forecastDirection s t∈sourceSpan (currentDirections s) := by
  have hm (b : Bool) : currentDirections s b∈sourceSpan (currentDirections s) :=
    (Submodule.span ℝ (range (currentDirections s))).le_topologicalClosure (Submodule.subset_span ⟨b,rfl⟩)
  exact (sourceSpan (currentDirections s)).add_mem (hm true)
    ((sourceSpan (currentDirections s)).smul_mem _ (hm false))

theorem forecast_mem_past (s t : ℝ≥0) : forecastDirection s t∈sourceSpan (pastDirections s) := by
  have hm (b : Bool) : currentDirections s b∈sourceSpan (pastDirections s) :=
    (Submodule.span ℝ (range (pastDirections s))).le_topologicalClosure
      (Submodule.subset_span ⟨(b,⟨s,by simp⟩),rfl⟩)
  exact (sourceSpan (pastDirections s)).add_mem (hm true)
    ((sourceSpan (pastDirections s)).smul_mem _ (hm false))

theorem current_source_projection (s t : ℝ≥0) (hst : s≤t) :
    sourceProjection (currentDirections s) (direction t)=forecastDirection s t :=
  SPDEWickBrownianPrediction.sourceProjection_eq_of_pairings _ _ _ (forecast_mem_current s t)
    (direction_pairing s s t le_rfl hst)

theorem past_source_projection (s t : ℝ≥0) (hst : s≤t) :
    sourceProjection (pastDirections s) (direction t)=forecastDirection s t := by
  apply SPDEWickBrownianPrediction.sourceProjection_eq_of_pairings _ _ _ (forecast_mem_past s t)
  intro p
  exact direction_pairing p.2 s t p.2.property hst p.1

theorem terminal_state_sufficient (s t : ℝ≥0) (hst : s≤t) (f : GaussianL2) (hf : f∈singleGenerated (direction t)) :
    conditionalProjection (pastDirections s) f=conditionalProjection (currentDirections s) f := by
  apply GaussianExponentialMarkovPrediction.terminal_prediction_eq_of_sourceProjection_eq _ _ _ _ f hf
  rw [past_source_projection s t hst,current_source_projection s t hst]

theorem wick_state_prediction (s t : ℝ≥0) (hst : s≤t) (n : ℕ) :
    conditionalProjection (pastDirections s) (wick (direction t) n)=(wick (forecastDirection s t) n : GaussianL2) := by
  rw [conditional_wick_projection,past_source_projection s t hst]

theorem integrated_pairing_exact (s t : ℝ≥0) (hst : s≤t) :
    inner ℝ (direction t) (direction s)=(t : ℝ)*(s : ℝ)^2/2-(s : ℝ)^3/6 := by
  rw [direction,direction,LinearIsometry.inner_map_map,L2_inner_eq_integral]
  have he : (fun x => inner ℝ (integratedVector t x) (integratedVector s x)) =ᵐ[volume]
      (Ioc 0 (s : ℝ)).indicator (fun x => ((t : ℝ)-x)*((s : ℝ)-x)) := by
    filter_upwards [integratedVector_coeFn t,integratedVector_coeFn s] with x ht hs
    rw [ht,hs]
    simp only [Real.inner_apply]
    by_cases hx : x∈Ioc 0 (s : ℝ)
    · have hxt : x∈Ioc 0 (t : ℝ) := ⟨hx.1,hx.2.trans hst⟩
      simp [hx,hxt,mul_comm]
    · simp [hx]
  rw [integral_congr_ae he,integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le s.coe_nonneg]
  have hd (x : ℝ) : HasDerivAt
      (fun x => (t : ℝ)*(s : ℝ)*x-((t : ℝ)+s)*x^2/2+x^3/3)
      (((t : ℝ)-x)*((s : ℝ)-x)) x := by
    convert ((((hasDerivAt_id x).const_mul ((t : ℝ)*s)).sub
      (((hasDerivAt_id x).pow 2).const_mul ((t : ℝ)+s) |>.div_const 2)).add
      (((hasDerivAt_id x).pow 3).div_const 3)) using 1 <;> (try funext y) <;> simp only [Pi.sub_apply,Pi.add_apply,Pi.pow_apply,id_eq] <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((by fun_prop : Continuous (fun x : ℝ => ((t : ℝ)-x)*((s : ℝ)-x))).intervalIntegrable _ _)]
  ring

def integratedPastDirections (s : ℝ≥0) : Iic s → CoefficientSpace := fun r => direction r

def terminal : GaussianL2 := firstChaosEmbedding (direction 3)
def fullForecast : GaussianL2 := conditionalProjection (integratedPastDirections 2) terminal
def valueOnlyForecast : GaussianL2 := conditionalProjection (fun _ : Unit => direction 2) terminal

theorem full_forecast_earlier_pairing :
    inner ℝ fullForecast (firstChaosEmbedding (direction 1))=4/3 := by
  have hm : firstChaosEmbedding (direction 1)∈generated (integratedPastDirections 2) := by
    rw [← IBMCubicFirstChaos.wick_one_eq_embedding]
    exact GaussianWickPredictionBound.observed_wick_mem (integratedPastDirections 2) ⟨1,by norm_num⟩ 1
  have he := (generated (integratedPastDirections 2)).starProjection_inner_eq_zero terminal
    (firstChaosEmbedding (direction 1)) hm
  change inner ℝ (terminal-fullForecast) (firstChaosEmbedding (direction 1))=0 at he
  rw [inner_sub_left,terminal,LinearIsometry.inner_map_map,integrated_pairing_exact 1 3 (by norm_num)] at he
  norm_num at he
  linarith

theorem value_only_earlier_pairing :
    inner ℝ valueOnlyForecast (firstChaosEmbedding (direction 1))=35/24 := by
  rw [valueOnlyForecast,terminal,conditional_firstChaos_projection,
    FractionalCurrentObservationObstruction.source_projection_single,map_smul,real_inner_smul_left,
    LinearIsometry.inner_map_map,← real_inner_self_eq_norm_sq]
  have h23 := (real_inner_comm (direction 2) (direction 3)).symm.trans (integrated_pairing_exact 2 3 (by norm_num))
  rw [h23,integrated_pairing_exact 2 2 le_rfl,
    integrated_pairing_exact 1 2 (by norm_num)]
  norm_num

theorem current_integrated_value_insufficient : fullForecast≠valueOnlyForecast := by
  intro he
  have h := full_forecast_earlier_pairing
  rw [he,value_only_earlier_pairing] at h
  norm_num at h

end OperatorDerivativeRewrite.Foundation.IntegratedBrownianStatePrediction




