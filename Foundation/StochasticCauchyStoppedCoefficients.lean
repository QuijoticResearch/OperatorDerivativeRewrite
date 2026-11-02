import Foundation.StochasticCauchyExitMoments
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! Actual stopped bounded coefficients in the original joint-past native domain. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyStoppedCoefficients
open InfiniteGaussian GaussianTimeProcess GaussianBrownianQuadraticVariation
open StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyPastReconstruction StochasticCauchyPhysicalInput StochasticCauchyExponentialInput
open StochasticCauchyStoppedDomains StochasticCauchyJointSteps StochasticCauchyBrownianRealization
attribute [local instance] StochasticCauchyParameterizedObstruction.finiteL2Exponent
  StochasticCauchyJointPastIntegral.input_complete
private abbrev μ := gaussianProduct.prod gaussianProduct
private abbrev Sample := SampleSpace × SampleSpace
variable (φ : ℂ →ᵇ ℝ) (τ : Sample → ℝ≥0)
  (hτ : IsStoppingTime augmentedJoint (fun w => (τ w:WithTop ℝ≥0)))

include hτ in
private theorem gt_measurable (s : ℝ≥0) : MeasurableSet[augmentedJoint s] {w | s<τ w} := by
  simpa only [WithTop.coe_lt_coe] using hτ.measurableSet_gt s
include hτ in
private theorem ge_measurable (s : ℝ≥0) : MeasurableSet[augmentedJoint s] {w | s≤τ w} := by
  simpa only [WithTop.coe_le_coe] using hτ.measurableSet_ge s

private theorem indicator_bound (A : Set Sample) (s : ℝ≥0) (w : Sample) :
    ‖A.indicator (fun w => φ (value s w)) w‖≤‖φ‖ := by
  by_cases hw : w∈A
  · simpa [hw] using φ.norm_coe_le_norm (value s w)
  · simp [hw]

include hτ in
private theorem coefficient_memLp (s : ℝ≥0) (strict : Bool) : MemLp
    (if strict then {w | s<τ w}.indicator (fun w => φ (value s w))
      else {w | s≤τ w}.indicator (fun w => φ (value s w))) 2 μ := by
  have hφ := φ.continuous.comp_stronglyMeasurable (continuous_stronglyAdapted s)
  cases strict
  · apply MemLp.of_bound ((hφ.indicator (ge_measurable τ hτ s)).mono (augmented_joint_le s)).aestronglyMeasurable ‖φ‖
    exact Eventually.of_forall (indicator_bound φ _ s)
  · apply MemLp.of_bound ((hφ.indicator (gt_measurable τ hτ s)).mono (augmented_joint_le s)).aestronglyMeasurable ‖φ‖
    exact Eventually.of_forall (indicator_bound φ _ s)

def strictCoefficient (s : ℝ≥0) : JointL2 := (coefficient_memLp φ τ hτ s true).toLp _
def coefficient (s : ℝ≥0) : JointL2 := (coefficient_memLp φ τ hτ s false).toLp _

theorem strictCoefficient_actual (s : ℝ≥0) :
    strictCoefficient φ τ hτ s =ᵐ[μ] {w | s<τ w}.indicator (fun w => φ (value s w)) := MemLp.coeFn_toLp _
theorem coefficient_actual (s : ℝ≥0) :
    coefficient φ τ hτ s =ᵐ[μ] {w | s≤τ w}.indicator (fun w => φ (value s w)) := MemLp.coeFn_toLp _

theorem strictCoefficient_past (s : ℝ≥0) : strictCoefficient φ τ hτ s∈jointPastL2 s := by
  apply raw_past_of_augmented
  exact ((φ.continuous.comp_stronglyMeasurable (continuous_stronglyAdapted s)).indicator
    (gt_measurable τ hτ s)).aestronglyMeasurable.congr (strictCoefficient_actual φ τ hτ s).symm

theorem strictCoefficient_norm (s : ℝ≥0) : ‖strictCoefficient φ τ hτ s‖≤‖φ‖ := by
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (μ := μ) (norm_nonneg φ)
    ((strictCoefficient_actual φ τ hτ s).mono fun w hw => by rw [hw];exact indicator_bound φ _ s w)
theorem coefficient_norm (s : ℝ≥0) : ‖coefficient φ τ hτ s‖≤‖φ‖ := by
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (μ := μ) (norm_nonneg φ)
    ((coefficient_actual φ τ hτ s).mono fun w hw => by rw [hw];exact indicator_bound φ _ s w)

/-- Left coefficients converge in actual source L2, including stopping atoms. -/
theorem coefficient_from_left (s : ℕ → ℝ≥0) (t : ℝ≥0) (hst : ∀ n,s n<t)
    (ht : Tendsto s atTop (𝓝 t)) :
    Tendsto (fun n => strictCoefficient φ τ hτ (s n)) atTop (𝓝 (coefficient φ τ hτ t)) := by
  let b : JointL2 := ‖φ‖ • jointOne
  have hb : b =ᵐ[μ] fun _ => ‖φ‖ := by
    filter_upwards [Lp.coeFn_smul ‖φ‖ jointOne,jointOne_ae] with w hw h1
    simpa only [Pi.smul_apply,smul_eq_mul,h1,mul_one] using hw
  apply BochnerL2Approximation.tendsto_of_dominated _ _ b
  · intro n
    filter_upwards [strictCoefficient_actual φ τ hτ (s n),hb] with w hw h1
    rw [hw,h1]
    simpa only [norm_norm] using indicator_bound φ _ _ w
  · filter_upwards [coefficient_actual φ τ hτ t,hb] with w hw h1
    rw [hw,h1]
    simpa only [norm_norm] using indicator_bound φ _ _ w
  · filter_upwards [ae_all_iff.mpr (fun n => strictCoefficient_actual φ τ hτ (s n)),coefficient_actual φ τ hτ t]
      with w hn hg
    simp only [hn,hg]
    by_cases htw : t≤τ w
    · have he (n : ℕ) : s n<τ w := (hst n).trans_le htw
      simp only [indicator_of_mem (show w∈{w | t≤τ w} from htw)]
      have hh := (φ.continuous.comp (value_continuous w)).continuousAt.tendsto.comp ht
      have hseq : (fun n => {w | s n<τ w}.indicator (fun w => φ (value (s n) w)) w) = fun n => φ (value (s n) w) := by
        funext n
        simp only [indicator_of_mem (show w∈{w | s n<τ w} from he n)]
      rw [hseq]
      exact hh
    · have he : ∀ᶠ n in atTop, τ w<s n := ht.eventually_const_lt (lt_of_not_ge htw)
      simp only [Set.indicator_of_notMem (show w∉{w | t≤τ w} from htw)]
      have hz : (fun n => {w | s n<τ w}.indicator (fun w => φ (value (s n) w)) w) =ᶠ[atTop] fun _ => 0 :=
        he.mono fun n hn => by simp [not_lt.mpr hn.le]
      exact (tendsto_congr' hz).mpr tendsto_const_nhds

private def pastCoefficient (s : ℝ≥0) : jointPastL2 s := ⟨strictCoefficient φ τ hτ s,strictCoefficient_past φ τ hτ s⟩

def gridInput (T : ℝ≥0) (n : ℕ) : Input T :=
  ∑ i : Fin (n+1),jointStep T (uniformTime T n i.castSucc) (uniformTime T n i.succ)
    (pastCoefficient φ τ hτ (uniformTime T n i.castSucc))

private def stepValue {m : ℕ} (t : Fin (m+1) → ℝ≥0) (r : ℝ) : JointL2 :=
  ∑ i : Fin m,(Ioc (t i.castSucc:ℝ) (t i.succ:ℝ)).indicator
    (fun _ => strictCoefficient φ τ hτ (t i.castSucc)) r

private theorem step_on {m : ℕ} (t : Fin (m+1) → ℝ≥0) (ht : Monotone t)
    (i : Fin m) (r : ℝ) (hr : r∈Ioc (t i.castSucc:ℝ) (t i.succ:ℝ)) :
    stepValue φ τ hτ t r=strictCoefficient φ τ hτ (t i.castSucc) := by
  rw [stepValue,Finset.sum_eq_single i,indicator_of_mem hr]
  · intro j _ hji
    apply indicator_of_notMem
    intro hj
    rcases lt_or_gt_of_ne hji with hjlt | hjgt
    · have hle : (t j.succ:ℝ)≤t i.castSucc := ht (Fin.succ_le_castSucc_iff.mpr hjlt)
      linarith [hr.1,hj.2]
    · have hle : (t i.succ:ℝ)≤t j.castSucc := ht (Fin.succ_le_castSucc_iff.mpr hjgt)
      linarith [hr.2,hj.1]
  · simp

private theorem grid_slices (T : ℝ≥0) (n : ℕ) :
    timeSections T (fieldEmbedding T (gridInput φ τ hτ T n)) =ᵐ[timeLaw T]
      stepValue φ τ hτ (uniformTime T n) := by
  have hb (i : Fin (n+1)) : uniformTime T n i.succ≤T := by
    simpa only [(uniformTime_endpoints T n).2] using uniformTime_monotone T n (Fin.le_last i.succ)
  simp only [gridInput,map_sum]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin (n+1) =>
      timeSections T (fieldEmbedding T (jointStep T (uniformTime T n i.castSucc)
        (uniformTime T n i.succ) (pastCoefficient φ τ hτ (uniformTime T n i.castSucc))))),
    ae_all_iff.mpr (fun i : Fin (n+1) => jointStep_slices T _ _
      (uniformTime_monotone T n (Fin.castSucc_le_succ i)) (hb i)
      (pastCoefficient φ τ hτ (uniformTime T n i.castSucc)))] with r hs hi
  rw [hs]
  simp only [Finset.sum_apply,stepValue]
  exact Finset.sum_congr rfl fun i _ => hi i

private theorem step_tendsto (T : ℝ≥0) (r : ℝ) (hr : r∈Ioc 0 (T:ℝ)) :
    Tendsto (fun n => stepValue φ τ hτ (uniformTime T n) r) atTop
      (𝓝 (coefficient φ τ hτ r.toNNReal)) := by
  choose i hi using fun n => GaussianQuadraticIto.uniformTime_covers T n r hr
  let s : ℕ → ℝ≥0 := fun n => uniformTime T n (i n).castSucc
  have hst (n : ℕ) : s n<r.toNNReal := by
    change (s n:ℝ)<(r.toNNReal:ℝ)
    rw [Real.coe_toNNReal _ hr.1.le]
    exact (hi n).1
  have hb (n : ℕ) : ‖(s n:ℝ)-r‖≤(T:ℝ)/(n+1) := by
    rw [Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr (hi n).1.le)]
    have hs := uniformTime_step T n (i n)
    linarith [(hi n).2]
  have hz : Tendsto (fun n : ℕ => (T:ℝ)/(n+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hreal := tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun n => norm_nonneg _) hb hz)
  have hnn := continuous_real_toNNReal.continuousAt.tendsto.comp hreal
  simp only [Function.comp_def,Real.toNNReal_coe] at hnn
  have hc := coefficient_from_left φ τ hτ s r.toNNReal hst hnn
  convert hc using 1
  funext n
  exact step_on φ τ hτ _ (uniformTime_monotone T n) (i n) r (hi n)

private def sections (T : ℝ≥0) : Input T →ₗᵢ[ℝ] Lp JointL2 2 (timeLaw T) :=
  (timeSections T).comp (fieldEmbedding T)

private theorem time_inside (T : ℝ≥0) : ∀ᵐ r ∂timeLaw T,r∈Ioc 0 (T:ℝ) :=
  ae_restrict_mem measurableSet_Ioc

private theorem grid_pointwise (T : ℝ≥0) : ∀ᵐ r ∂timeLaw T,
    Tendsto (fun n => sections T (gridInput φ τ hτ T n) r) atTop (𝓝 (coefficient φ τ hτ r.toNNReal)) := by
  filter_upwards [ae_all_iff.mpr (fun n => grid_slices φ τ hτ T n),time_inside T] with r hn hr
  change Tendsto (fun n => timeSections T (fieldEmbedding T (gridInput φ τ hτ T n)) r) _ _
  simpa only [hn] using step_tendsto φ τ hτ T r hr

private theorem target_memLp (T : ℝ≥0) : MemLp (fun r : ℝ => coefficient φ τ hτ r.toNNReal) 2 (timeLaw T) :=
  MemLp.of_bound (aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => Lp.aestronglyMeasurable (sections T (gridInput φ τ hτ T n)))
    (grid_pointwise φ τ hτ T)) ‖φ‖ (Eventually.of_forall fun r => coefficient_norm φ τ hτ r.toNNReal)

private def target (T : ℝ≥0) : Lp JointL2 2 (timeLaw T) := (target_memLp φ τ hτ T).toLp _
private theorem target_actual (T : ℝ≥0) : target φ τ hτ T =ᵐ[timeLaw T] fun r => coefficient φ τ hτ r.toNNReal :=
  MemLp.coeFn_toLp _

private theorem grid_sections_tendsto (T : ℝ≥0) :
    Tendsto (fun n => sections T (gridInput φ τ hτ T n)) atTop (𝓝 (target φ τ hτ T)) := by
  let b : Lp ℝ 2 (timeLaw T) := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top _ _) ‖φ‖
  have hb : b =ᵐ[timeLaw T] fun _ => ‖φ‖ := by
    simpa only [Set.indicator_univ] using (indicatorConstLp_coeFn (p := 2) (c := ‖φ‖)
      (μ := timeLaw T) (hs := MeasurableSet.univ) (hμs := measure_ne_top _ _))
  apply BochnerL2Approximation.tendsto_of_dominated _ _ b
  · intro n
    filter_upwards [hb,grid_slices φ τ hτ T n,time_inside T] with r hb hs hr
    obtain ⟨i,hi⟩ := GaussianQuadraticIto.uniformTime_covers T n r hr
    change ‖timeSections T (fieldEmbedding T (gridInput φ τ hτ T n)) r‖≤_
    rw [hb,hs,step_on φ τ hτ _ (uniformTime_monotone T n) i r hi]
    simpa only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg φ)] using strictCoefficient_norm φ τ hτ (uniformTime T n i.castSucc)
  · filter_upwards [hb,target_actual φ τ hτ T] with r hb ht
    rw [hb,ht]
    simpa only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg φ)] using coefficient_norm φ τ hτ r.toNNReal
  · filter_upwards [grid_pointwise φ τ hτ T,target_actual φ τ hτ T] with r hr ht
    rw [ht];exact hr

/-- The target weighted stopped coefficient lies in the CLOSED ORIGINAL native range. -/
theorem stoppedInput_exists (T : ℝ≥0) :
    ∃ u : Input T,sections T u=target φ τ hτ T := by
  have hc : IsClosed (Set.range (sections T)) :=
    (sections T).isometry.isClosedEmbedding.isClosed_range
  exact hc.mem_of_tendsto (grid_sections_tendsto φ τ hτ T)
    (Eventually.of_forall fun n => ⟨gridInput φ τ hτ T n,rfl⟩)

def stoppedInput (T : ℝ≥0) : Input T := Classical.choose (stoppedInput_exists φ τ hτ T)
private theorem stoppedInput_sections (T : ℝ≥0) :
    sections T (stoppedInput φ τ hτ T)=target φ τ hτ T := Classical.choose_spec (stoppedInput_exists φ τ hτ T)

theorem gridInput_tendsto (T : ℝ≥0) :
    Tendsto (gridInput φ τ hτ T) atTop (𝓝 (stoppedInput φ τ hτ T)) := by
  apply (sections T).isometry.tendsto_nhds_iff.mpr
  simpa only [Function.comp_def,stoppedInput_sections φ τ hτ T] using grid_sections_tendsto φ τ hτ T

theorem stoppedInput_physical (T : ℝ≥0) :
    ∀ᵐ r ∂timeLaw T,∀ᵐ w ∂μ,fieldEmbedding T (stoppedInput φ τ hτ T) ((r,w.1),w.2)=
      (Ioc (0:ℝ) (τ w:ℝ)).indicator (fun r => φ (value r.toNNReal w)) r := by
  filter_upwards [timeSections_ae T (fieldEmbedding T (stoppedInput φ τ hτ T)),
    target_actual φ τ hτ T,time_inside T] with r hr ht hin
  change sections T (stoppedInput φ τ hτ T) r =ᵐ[μ] _ at hr
  rw [stoppedInput_sections φ τ hτ T,ht] at hr
  filter_upwards [hr,coefficient_actual φ τ hτ r.toNNReal] with w hw hs
  rw [← hw,hs]
  have he : r.toNNReal≤τ w ↔ r≤(τ w:ℝ) := by
    rw [Real.toNNReal_le_iff_le_coe]
  simp only [Set.indicator,Set.mem_ofPred_eq,Set.mem_Ioc,hin.1,true_and,he]

open ComplexL2Isometry StochasticCauchyComplexChannels
attribute [local instance] StochasticCauchyComplexChannels.complexInput_complete
private abbrev valueIntegral := StochasticCauchyStoppedIndicators.valueIntegral

private theorem valueIntegral_apply (T : ℝ≥0) (u : Input T) :
    valueIntegral T u=combine μ (integralX T u) (integralY T u) := rfl

private theorem valueIntegral_step (T s t : ℝ≥0) (hst : s≤t) (htT : t≤T) (C : jointPastL2 s) :
    valueIntegral T (jointStep T s t C) =ᵐ[μ] fun w => (C.val w:ℂ)*
      (StochasticCauchyPolynomialPrediction.position t w-StochasticCauchyPolynomialPrediction.position s w) := by
  rw [valueIntegral_apply]
  filter_upwards [combine_ae μ _ _,(jointStep_integrals T s t hst htT C).1,
    (jointStep_integrals T s t hst htT C).2] with w hc hx hy
  rw [hc,hx,hy]
  simp only [StochasticCauchyPolynomialPrediction.position,Complex.ofReal_mul,Complex.ofReal_sub]
  ring

/-- The actual left chronological sums, including the crossing cell. -/
def chronologicalSum (T : ℝ≥0) (n : ℕ) (w : Sample) : ℂ :=
  ∑ i : Fin (n+1),if uniformTime T n i.castSucc<τ w then
    (φ (value (uniformTime T n i.castSucc) w):ℂ)*
      (value (uniformTime T n i.succ) w-value (uniformTime T n i.castSucc) w) else 0

theorem chronological_actual (T : ℝ≥0) (n : ℕ) :
    valueIntegral T (gridInput φ τ hτ T n) =ᵐ[μ] chronologicalSum φ τ T n := by
  have hb (i : Fin (n+1)) : uniformTime T n i.succ≤T := by
    simpa only [(uniformTime_endpoints T n).2] using uniformTime_monotone T n (Fin.le_last i.succ)
  simp only [gridInput,map_sum]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin (n+1) =>
      valueIntegral T (jointStep T (uniformTime T n i.castSucc) (uniformTime T n i.succ)
        (pastCoefficient φ τ hτ (uniformTime T n i.castSucc)))),
    ae_all_iff.mpr (fun i : Fin (n+1) => valueIntegral_step T _ _
      (uniformTime_monotone T n (Fin.castSucc_le_succ i)) (hb i)
      (pastCoefficient φ τ hτ (uniformTime T n i.castSucc))),
    ae_all_iff.mpr (fun i : Fin (n+1) => strictCoefficient_actual φ τ hτ (uniformTime T n i.castSucc)),
    ae_all_iff.mpr (fun i : Fin (n+2) => StochasticCauchyContinuousPolynomials.continuous_value_ae (uniformTime T n i))]
    with w hs hi hc hz
  rw [hs]
  simp only [Finset.sum_apply,chronologicalSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hi i]
  change (strictCoefficient φ τ hτ (uniformTime T n i.castSucc) w:ℂ)*_=_
  rw [hc i,← hz i.succ,← hz i.castSucc]
  by_cases hw : uniformTime T n i.castSucc<τ w <;> simp [hw]

/-- A genuine native stochastic integral, before any terminal-value identity. -/
def stochasticIntegral (T : ℝ≥0) : JointComplex := valueIntegral T (stoppedInput φ τ hτ T)

theorem chronological_L2_tendsto (T : ℝ≥0) :
    Tendsto (fun n => valueIntegral T (gridInput φ τ hτ T n)) atTop
      (𝓝 (stochasticIntegral φ τ hτ T)) :=
  ((valueIntegral T).continuous.tendsto _).comp (gridInput_tendsto φ τ hτ T)

include hτ in
theorem chronological_memLp (T : ℝ≥0) (n : ℕ) : MemLp (chronologicalSum φ τ T n) 2 μ :=
  (Lp.memLp (valueIntegral T (gridInput φ τ hτ T n))).ae_eq (chronological_actual φ τ hτ T n)

theorem chronological_mean_square (T : ℝ≥0) :
    Tendsto (fun n => ∫ w,‖chronologicalSum φ τ T n w-stochasticIntegral φ τ hτ T w‖^2 ∂μ)
      atTop (𝓝 0) := by
  have hl := chronological_L2_tendsto φ τ hτ T
  have hn : Tendsto (fun n => ‖valueIntegral T (gridInput φ τ hτ T n)-stochasticIntegral φ τ hτ T‖^2) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)] using
      ((hl.sub_const (stochasticIntegral φ τ hτ T)).norm.pow 2)
  have he (n : ℕ) : ‖valueIntegral T (gridInput φ τ hτ T n)-stochasticIntegral φ τ hτ T‖^2=
      ∫ w,‖chronologicalSum φ τ T n w-stochasticIntegral φ τ hτ T w‖^2 ∂μ := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (valueIntegral T (gridInput φ τ hτ T n)) (stochasticIntegral φ τ hτ T),
      chronological_actual φ τ hτ T n] with w hs hf
    simp only [hs,Pi.sub_apply,hf]
  simpa only [he] using hn

def normalizedInput (T : ℝ≥0) : ComplexInput T :=
  ((Real.sqrt 2:ℝ):ℂ) • combineInput T (stoppedInput φ τ hτ T) 0

theorem normalized_reconstruction (T : ℝ≥0) :
    channel T false (normalizedInput φ τ hτ T)=stochasticIntegral φ τ hτ T := by
  rw [normalizedInput,StochasticCauchyExponentialReconstruction.normalized_channel_combine,
    map_zero,sub_zero,map_zero,zero_add,stochasticIntegral,valueIntegral_apply]

theorem stochasticIntegral_mean_zero (T : ℝ≥0) : (∫ w,stochasticIntegral φ τ hτ T w ∂μ)=0 := by
  rw [← normalized_reconstruction]
  exact StochasticCauchyMeanResidual.channel_centered T false _

/-- The input is determined by its physical stopped coefficient, not the chosen grid. -/
theorem stoppedInput_unique (T : ℝ≥0) (u : Input T)
    (hu : ∀ᵐ r ∂timeLaw T,∀ᵐ w ∂μ,fieldEmbedding T u ((r,w.1),w.2)=
      (Ioc (0:ℝ) (τ w:ℝ)).indicator (fun r => φ (value r.toNNReal w)) r) :
    u=stoppedInput φ τ hτ T := by
  apply (fieldEmbedding T).injective
  apply (timeSections T).injective
  apply Lp.ext
  filter_upwards [timeSections_ae T (fieldEmbedding T u),
    timeSections_ae T (fieldEmbedding T (stoppedInput φ τ hτ T)),hu,stoppedInput_physical φ τ hτ T]
    with r h1 h2 h3 h4
  apply Lp.ext
  filter_upwards [h1,h2,h3,h4] with w h1 h2 h3 h4
  exact h1.trans (h3.trans (h4.symm.trans h2.symm))

private def clamp (f : ℂ → ℝ) (hf : Continuous f) (M : ℝ) (hM : 0≤M) : ℂ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun z => max (-M) (min M (f z)))
    (continuous_const.max (continuous_const.min hf)) M (fun z => by
      rw [Real.norm_eq_abs,abs_le]
      exact ⟨le_max_left _ _,max_le (by linarith) (min_le_left _ _)⟩)

private theorem clamp_eq (f : ℂ → ℝ) (hf : Continuous f) (M : ℝ) (hM : 0≤M)
    (z : ℂ) (hz : ‖f z‖≤M) : clamp f hf M hM z=f z := by
  change max (-M) (min M (f z))=f z
  have h := abs_le.mp (show |f z|≤M by simpa only [Real.norm_eq_abs] using hz)
  rw [min_eq_right h.2,max_eq_right h.1]

/-- An actual polynomial derivative admits a bounded continuous real component
extension agreeing on the closed disk. No global polynomial bound is claimed. -/
theorem derivative_component_extension (p : Polynomial ℂ) (R : ℝ) (imag : Bool) :
    ∃ φ : ℂ →ᵇ ℝ,∀ z : ℂ,‖z‖≤R → φ z=if imag then (p.derivative.eval z).im else (p.derivative.eval z).re := by
  obtain ⟨M,hM,hbound⟩ := StochasticCauchyExitMoments.polynomial_disk_bound p.derivative R
  let f : ℂ → ℝ := fun z => if imag then (p.derivative.eval z).im else (p.derivative.eval z).re
  have hp : Continuous (fun z : ℂ => p.derivative.eval z) := by fun_prop
  have hf : Continuous f := by
    cases imag
    · simpa only [f,Bool.false_eq_true,ite_false,Function.comp_def] using Complex.continuous_re.comp hp
    · simpa only [f,ite_true,Function.comp_def] using Complex.continuous_im.comp hp
  refine ⟨clamp f hf M hM,?_⟩
  intro z hz
  apply clamp_eq
  cases imag
  · exact Complex.abs_re_le_norm (p.derivative.eval z) |>.trans (hbound z hz)
  · exact Complex.abs_im_le_norm (p.derivative.eval z) |>.trans (hbound z hz)

/-- Actual stopped polynomial derivative components belong to the ORIGINAL
native domain, with infinite original clocks handled by genuine clipping. -/
theorem stopped_derivative_inputs (p : Polynomial ℂ) (R : ℝ) (hR : 0≤R) (T : ℝ≥0) :
    ∃ a b : Input T,∀ᵐ r ∂timeLaw T,∀ᵐ w ∂μ,
      fieldEmbedding T a ((r,w.1),w.2)=
        {w : Sample | (r.toNNReal:WithTop ℝ≥0)≤StochasticCauchyExitClock.exitTime R w}.indicator
          (fun w => (p.derivative.eval (value r.toNNReal w)).re) w ∧
      fieldEmbedding T b ((r,w.1),w.2)=
        {w : Sample | (r.toNNReal:WithTop ℝ≥0)≤StochasticCauchyExitClock.exitTime R w}.indicator
          (fun w => (p.derivative.eval (value r.toNNReal w)).im) w := by
  obtain ⟨φ,hφ⟩ := derivative_component_extension p R false
  obtain ⟨ψ,hψ⟩ := derivative_component_extension p R true
  let τ := StochasticCauchyExitClock.clippedClock T (StochasticCauchyExitClock.exitTime R)
  have hτ := StochasticCauchyExitClock.clippedClock_stopping T (StochasticCauchyExitClock.exitTime R)
    (StochasticCauchyExitClock.exitTime_stopping R)
  refine ⟨stoppedInput φ τ hτ T,stoppedInput ψ τ hτ T,?_⟩
  filter_upwards [stoppedInput_physical φ τ hτ T,stoppedInput_physical ψ τ hτ T,time_inside T]
    with r hr hi hin
  have hrT : r.toNNReal≤T := Real.toNNReal_le_iff_le_coe.mpr hin.2
  filter_upwards [hr,hi,StochasticCauchyExitClock.exit_bounded_ae R hR r.toNNReal] with w hr hi hb
  have he : r≤(τ w:ℝ) ↔ (r.toNNReal:WithTop ℝ≥0)≤StochasticCauchyExitClock.exitTime R w := by
    rw [← Real.toNNReal_le_iff_le_coe]
    change r.toNNReal≤StochasticCauchyExitClock.clippedClock T (StochasticCauchyExitClock.exitTime R) w ↔ _
    rw [← WithTop.coe_le_coe,StochasticCauchyExitClock.clippedClock_coe,le_min_iff]
    simp only [WithTop.coe_le_coe,hrT,and_true]
  have hdisc (hh : (r.toNNReal:WithTop ℝ≥0)≤StochasticCauchyExitClock.exitTime R w) : ‖value r.toNNReal w‖≤R := by
    have hc : StochasticCauchyExitClock.clippedClock r.toNNReal (StochasticCauchyExitClock.exitTime R) w=r.toNNReal := by
      apply WithTop.coe_injective
      rw [StochasticCauchyExitClock.clippedClock_coe,min_eq_right hh]
    simpa only [hc] using hb
  constructor
  · rw [hr]
    by_cases hh : (r.toNNReal:WithTop ℝ≥0)≤StochasticCauchyExitClock.exitTime R w
    · simp only [Set.indicator,Set.mem_Ioc,hin.1,true_and,he,Set.mem_ofPred_eq,hh,ite_true]
      exact hφ _ (hdisc hh)
    · simp only [Set.indicator,Set.mem_Ioc,hin.1,true_and,he,Set.mem_ofPred_eq,hh,ite_false]
  · rw [hi]
    by_cases hh : (r.toNNReal:WithTop ℝ≥0)≤StochasticCauchyExitClock.exitTime R w
    · simp only [Set.indicator,Set.mem_Ioc,hin.1,true_and,he,Set.mem_ofPred_eq,hh,ite_true]
      exact hψ _ (hdisc hh)
    · simp only [Set.indicator,Set.mem_Ioc,hin.1,true_and,he,Set.mem_ofPred_eq,hh,ite_false]

/-- Both components assemble into the existing COMPLEX native domain.
The physical coefficient here is unnormalized; dZ integration uses sqrt2*u
against the existing normalized channel dZ/sqrt2. -/
theorem stopped_derivative_complex_input (p : Polynomial ℂ) (R : ℝ) (hR : 0≤R) (T : ℝ≥0) :
    ∃ u : ComplexInput T,∀ᵐ r ∂timeLaw T,∀ᵐ w ∂μ,
      (fieldEmbedding T (realInput T u) ((r,w.1),w.2):ℂ)+
        Complex.I*(fieldEmbedding T (imagInput T u) ((r,w.1),w.2):ℂ)=
      {w : Sample | (r.toNNReal:WithTop ℝ≥0)≤StochasticCauchyExitClock.exitTime R w}.indicator
        (fun w => p.derivative.eval (value r.toNNReal w)) w := by
  obtain ⟨a,b,hab⟩ := stopped_derivative_inputs p R hR T
  refine ⟨combineInput T a b,?_⟩
  simp only [realInput_combine,imagInput_combine]
  filter_upwards [hab] with r hr
  filter_upwards [hr] with w hw
  rw [hw.1,hw.2]
  by_cases hh : (r.toNNReal:WithTop ℝ≥0)≤StochasticCauchyExitClock.exitTime R w
  · simp only [indicator_of_mem (show w∈{w : Sample | (r.toNNReal:WithTop ℝ≥0)≤StochasticCauchyExitClock.exitTime R w} from hh)]
    simpa only [mul_comm] using Complex.re_add_im (p.derivative.eval (value r.toNNReal w))
  · simp only [indicator_of_notMem (show w∉{w : Sample | (r.toNNReal:WithTop ℝ≥0)≤StochasticCauchyExitClock.exitTime R w} from hh),Complex.ofReal_zero,mul_zero,add_zero]

/-- Weighted stopped energy is controlled by the genuine unweighted occupation
input, rather than the full deterministic horizon. -/
theorem stoppedInput_norm_le (T : ℝ≥0) :
    ‖stoppedInput φ τ hτ T‖≤‖φ‖*‖StochasticCauchyStoppedIndicators.stoppedInput τ hτ T‖ := by
  let u := stoppedInput φ τ hτ T
  let v := StochasticCauchyStoppedIndicators.stoppedInput τ hτ T
  have hb : ‖sections T u‖≤‖‖φ‖ • sections T v‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_smul ‖φ‖ (sections T v),
      timeSections_ae T (fieldEmbedding T u),timeSections_ae T (fieldEmbedding T v),
      stoppedInput_physical φ τ hτ T,StochasticCauchyStoppedIndicators.stoppedInput_physical τ hτ T]
      with r hs hu hv hφ h1
    simp only [Pi.smul_apply] at hs
    rw [hs]
    have hh : ‖sections T u r‖≤‖‖φ‖ • sections T v r‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [hu,hv,hφ,h1,Lp.coeFn_smul ‖φ‖ (sections T v r)] with w hu hv hφ h1 hs
      simp only [Pi.smul_apply,smul_eq_mul] at hs
      change sections T u r w = _ at hu
      change sections T v r w = _ at hv
      change fieldEmbedding T u ((r,w.1),w.2) = _ at hφ
      change fieldEmbedding T v ((r,w.1),w.2) = _ at h1
      rw [hs,hu,hv,hφ,h1]
      by_cases hw : r∈Ioc (0:ℝ) (τ w:ℝ)
      · simpa only [indicator_of_mem hw,mul_one,norm_norm] using φ.norm_coe_le_norm (value r.toNNReal w)
      · simp only [indicator_of_notMem hw,mul_zero,norm_zero,le_refl]
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg φ)] using hh
  simpa only [(sections T).norm_map,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg φ)] using hb

/-- Uniform-in-horizon bound for the ACTUAL exit-weighted native input. -/
theorem exit_weighted_energy (φ : ℂ →ᵇ ℝ) (R : ℝ) (hR : 0≤R) (T : ℝ≥0) :
    ‖stoppedInput φ (StochasticCauchyExitClock.clippedClock T (StochasticCauchyExitClock.exitTime R))
      (StochasticCauchyExitClock.clippedClock_stopping T _ (StochasticCauchyExitClock.exitTime_stopping R)) T‖^2≤
        ‖φ‖^2*R^2/2 := by
  have hb := stoppedInput_norm_le φ
    (StochasticCauchyExitClock.clippedClock T (StochasticCauchyExitClock.exitTime R))
    (StochasticCauchyExitClock.clippedClock_stopping T _ (StochasticCauchyExitClock.exitTime_stopping R)) T
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [mul_pow] at hs
  have he := mul_le_mul_of_nonneg_left (StochasticCauchyExitClock.exit_input_energy R hR T) (sq_nonneg ‖φ‖)
  calc
    _ ≤ ‖φ‖^2*‖StochasticCauchyExitClock.exitInput R T‖^2 := hs
    _ ≤ ‖φ‖^2*(R^2/2) := he
    _ = _ := by ring

end OperatorDerivativeRewrite.Foundation.StochasticCauchyStoppedCoefficients
