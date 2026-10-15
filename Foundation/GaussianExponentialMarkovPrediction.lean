import Foundation.SPDEExponentialForcing
import Foundation.SPDEWickBrownianPrediction
import Foundation.GaussianSingleObservationPrediction

/-! Actual exponential kernels recover the Ornstein-Uhlenbeck terminal Markov prediction law. -/
noncomputable section
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianExponentialMarkovPrediction
open InfiniteGaussian GaussianTimeHilbert SeparableHilbertEmbedding
open GaussianConditionalGraph GaussianWickConditionalProjection GaussianTimeSpaceHermite
open GaussianSingleObservationPrediction SPDEExponentialForcing
attribute [local instance] timeHilbert_secondCountable

def decay (rate s t : ℝ≥0) : ℝ := Real.exp (-(rate : ℝ)*((t : ℝ)-s))

theorem response_pairing (rate r s t : ℝ≥0) (hrs : r≤s) (hst : s≤t) :
    inner ℝ (responseVector rate t) (responseVector rate r)=
      decay rate s t*inner ℝ (responseVector rate s) (responseVector rate r) := by
  rw [L2_inner_eq_integral,L2_inner_eq_integral,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [responseVector_coeFn rate t,responseVector_coeFn rate s,responseVector_coeFn rate r] with x ht hs hr
  rw [ht,hs,hr]
  simp only [Real.inner_apply]
  by_cases hx : x∈Ioc 0 (r : ℝ)
  · have hxs : x∈Ioc 0 (s : ℝ) := ⟨hx.1,hx.2.trans hrs⟩
    have hxt : x∈Ioc 0 (t : ℝ) := ⟨hx.1,hxs.2.trans hst⟩
    simp only [response,indicator_of_mem hx,indicator_of_mem hxs,indicator_of_mem hxt]
    have he : Real.exp (-(rate : ℝ)*((t : ℝ)-x))=
        decay rate s t*Real.exp (-(rate : ℝ)*((s : ℝ)-x)) := by
      rw [decay,← Real.exp_add]
      congr 1
      ring
    rw [he]
    ring
  · simp [response,hx]

def direction (rate t : ℝ≥0) : CoefficientSpace := hilbertEmbedding TimeHilbert (responseVector rate t)

def pastDirections (rate s : ℝ≥0) : Iic s → CoefficientSpace := fun r => direction rate r

theorem direction_pairing (rate r s t : ℝ≥0) (hrs : r≤s) (hst : s≤t) :
    inner ℝ (direction rate t) (direction rate r)=
      decay rate s t*inner ℝ (direction rate s) (direction rate r) := by
  simp only [direction,LinearIsometry.inner_map_map]
  exact response_pairing rate r s t hrs hst

theorem past_source_projection (rate s t : ℝ≥0) (hst : s≤t) :
    sourceProjection (pastDirections rate s) (direction rate t)=decay rate s t • direction rate s := by
  apply SPDEWickBrownianPrediction.sourceProjection_eq_of_pairings
  · apply (sourceSpan (pastDirections rate s)).smul_mem
    exact (Submodule.span ℝ (range (pastDirections rate s))).le_topologicalClosure
      (Submodule.subset_span ⟨⟨s,by simp⟩,rfl⟩)
  · intro r
    rw [real_inner_smul_left]
    exact direction_pairing rate r s t r.property hst

theorem current_source_projection (rate s t : ℝ≥0) (hst : s≤t) :
    sourceProjection (fun _ : Unit => direction rate s) (direction rate t)=decay rate s t • direction rate s := by
  apply SPDEWickBrownianPrediction.sourceProjection_eq_of_pairings
  · apply (sourceSpan (fun _ : Unit => direction rate s)).smul_mem
    exact (Submodule.span ℝ (range (fun _ : Unit => direction rate s))).le_topologicalClosure
      (Submodule.subset_span ⟨(),rfl⟩)
  · intro r
    rw [real_inner_smul_left]
    exact direction_pairing rate s s t le_rfl hst

theorem terminal_prediction_eq_of_sourceProjection_eq {I J : Type*}
    (h : I → CoefficientSpace) (k : J → CoefficientSpace) (u : CoefficientSpace)
    (he : sourceProjection h u=sourceProjection k u) (f : GaussianL2) (hf : f∈singleGenerated u) :
    conditionalProjection h f=conditionalProjection k f := by
  let L := conditionalProjection h-conditionalProjection k
  have hs : wickSpan u≤L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n,rfl⟩
    change conditionalProjection h (wick u n)-conditionalProjection k (wick u n)=0
    rw [conditional_wick_projection,conditional_wick_projection,he,sub_self]
  have hc := (wickSpan u).topologicalClosure_minimal hs L.isClosed_ker
  rw [wickSpan_closure] at hc
  have ht := hc hf
  change conditionalProjection h f-conditionalProjection k f=0 at ht
  exact sub_eq_zero.mp ht

theorem terminal_markov_prediction (rate s t : ℝ≥0) (hst : s≤t)
    (f : GaussianL2) (hf : f∈singleGenerated (direction rate t)) :
    conditionalProjection (pastDirections rate s) f=
      conditionalProjection (fun _ : Unit => direction rate s) f := by
  apply terminal_prediction_eq_of_sourceProjection_eq _ _ _ _ f hf
  rw [past_source_projection rate s t hst,current_source_projection rate s t hst]

theorem wick_prediction (rate s t : ℝ≥0) (hst : s≤t) (n : ℕ) :
    conditionalProjection (pastDirections rate s) (wick (direction rate t) n)=
      (wick (decay rate s t • direction rate s) n : GaussianL2) := by
  rw [conditional_wick_projection,past_source_projection rate s t hst]

theorem wick_prediction_energy (rate s t : ℝ≥0) (hst : s≤t) (n : ℕ) :
    ‖conditionalProjection (pastDirections rate s) (wick (direction rate t) n)‖^2=
      (n.factorial : ℝ)*(decay rate s t)^ (2*n)*(‖responseVector rate s‖^2)^n := by
  rw [wick_prediction rate s t hst,GaussianWickContinuity.wick_norm_sq,norm_smul,
    mul_pow,Real.norm_eq_abs,sq_abs,direction,LinearIsometry.norm_map,mul_pow,← pow_mul]
  ring

theorem response_support (rate t : ℝ≥0) :
    ∀ᵐ x ∂(volume : Measure ℝ), x∉Ioc 0 (t : ℝ) → responseVector rate t x=0 := by
  filter_upwards [responseVector_coeFn rate t] with x hx hxt
  rw [hx,response,indicator_of_notMem hxt]

def causalProfile (rate t : ℝ≥0) : GaussianDeterministicVolterra.positiveProfiles :=
  ⟨responseVector rate t,GaussianDeterministicVolterra.causal_profile_mem t _ (response_support rate t)⟩

def value (rate t : ℝ≥0) : GaussianL2 := firstChaosEmbedding (direction rate t)

theorem value_is_actual_ito (rate t : ℝ≥0) :
    value rate t=GaussianPredictableFull.itoIntegral
      (GaussianDeterministicVolterra.profileField (causalProfile rate t)) := by
  exact (GaussianDeterministicVolterra.profileIntegral_eq_isonormal (causalProfile rate t)).symm

theorem value_jointGaussian (rate : ℝ≥0) : ProbabilityTheory.IsGaussianProcess
    (fun t ω => value rate t ω) gaussianProduct :=
  firstChaos_isGaussianProcess.comp_right (direction rate)

theorem linear_prediction (rate s t : ℝ≥0) (hst : s≤t) :
    conditionalProjection (pastDirections rate s) (value rate t)=decay rate s t • value rate s := by
  rw [value,conditional_firstChaos_projection,past_source_projection rate s t hst,map_smul]
  rfl

def innovationDirection (rate s t : ℝ≥0) : CoefficientSpace :=
  direction rate t-decay rate s t • direction rate s

theorem innovation_orthogonal_past (rate s t : ℝ≥0) (hst : s≤t) (r : Iic s) :
    inner ℝ (innovationDirection rate s t) (direction rate r)=0 := by
  rw [innovationDirection,inner_sub_left,real_inner_smul_left,direction_pairing rate r s t r.property hst,sub_self]

theorem innovation_independent_history (rate s t : ℝ≥0) (hst : s≤t) :
    ProbabilityTheory.IndepFun (firstChaosEmbedding (innovationDirection rate s t))
      (fun ω (r : Iic s) => value rate r ω) gaussianProduct := by
  let X : Unit → SampleSpace → ℝ := fun _ => firstChaosEmbedding (innovationDirection rate s t)
  let Y : Iic s → SampleSpace → ℝ := fun r => value rate r
  have hg : ProbabilityTheory.IsGaussianProcess (Sum.elim X Y) gaussianProduct := by
    convert firstChaos_isGaussianProcess.comp_right
      (Sum.elim (fun _ : Unit => innovationDirection rate s t) (fun r : Iic s => direction rate r)) using 1
    funext p
    cases p <;> rfl
  have hi := hg.indepFun_of_covariance_eq_zero
    (fun _ => (Lp.stronglyMeasurable _).measurable.aemeasurable)
    (fun _ => (Lp.stronglyMeasurable _).measurable.aemeasurable)
    (fun _ r => by
      change cov[firstChaosEmbedding (innovationDirection rate s t),
        firstChaosEmbedding (direction rate r);gaussianProduct]=0
      rw [firstChaos_covariance,innovation_orthogonal_past rate s t hst r])
  exact hi.comp (measurable_pi_apply ()) measurable_id

end OperatorDerivativeRewrite.Foundation.GaussianExponentialMarkovPrediction



