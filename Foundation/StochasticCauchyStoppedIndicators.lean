import Foundation.StochasticCauchyJointSteps
import Foundation.BochnerL2Approximation
import Foundation.GaussianQuadraticIto

/-! Bounded-horizon stopped indicators in the existing native joint-past domain. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyStoppedIndicators
open InfiniteGaussian GaussianTimeProcess GaussianBrownianQuadraticVariation
open StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyPastReconstruction StochasticCauchyPhysicalInput StochasticCauchyExponentialInput
open StochasticCauchyStoppedDomains StochasticCauchyJointSteps
attribute [local instance] StochasticCauchyParameterizedObstruction.finiteL2Exponent
  StochasticCauchyJointPastIntegral.input_complete
private abbrev μ := gaussianProduct.prod gaussianProduct
private abbrev Sample := SampleSpace × SampleSpace
variable (τ : Sample → ℝ≥0)
  (hτ : IsStoppingTime augmentedJoint (fun w => (τ w:WithTop ℝ≥0)))

include hτ in
private theorem gt_measurable (s : ℝ≥0) : MeasurableSet[augmentedJoint s] {w | s<τ w} := by
  simpa only [WithTop.coe_lt_coe] using hτ.measurableSet_gt s
include hτ in
private theorem ge_measurable (s : ℝ≥0) : MeasurableSet[augmentedJoint s] {w | s≤τ w} := by
  simpa only [WithTop.coe_le_coe] using hτ.measurableSet_ge s

def strictSurvival (s : ℝ≥0) : JointL2 :=
  indicatorConstLp 2 (augmented_joint_le s _ (gt_measurable τ hτ s)) (measure_ne_top μ _) (1:ℝ)
def survival (s : ℝ≥0) : JointL2 :=
  indicatorConstLp 2 (augmented_joint_le s _ (ge_measurable τ hτ s)) (measure_ne_top μ _) (1:ℝ)

theorem strictSurvival_actual (s : ℝ≥0) :
    strictSurvival τ hτ s =ᵐ[μ] {w | s<τ w}.indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn

theorem survival_actual (s : ℝ≥0) :
    survival τ hτ s =ᵐ[μ] {w | s≤τ w}.indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn

theorem strictSurvival_past (s : ℝ≥0) : strictSurvival τ hτ s∈jointPastL2 s := by
  apply raw_past_of_augmented
  exact (stronglyMeasurable_const.indicator (gt_measurable τ hτ s)).aestronglyMeasurable.congr
    (strictSurvival_actual τ hτ s).symm

private theorem indicator_norm (A : Set Sample) (w : Sample) :
    ‖A.indicator (fun _ => (1:ℝ)) w‖≤1 := by by_cases hw : w∈A <;> simp [hw]

theorem strictSurvival_norm (s : ℝ≥0) : ‖strictSurvival τ hτ s‖≤1 := by
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (μ := μ) (by norm_num : (0:ℝ)≤1)
    ((strictSurvival_actual τ hτ s).mono fun w hw => by rw [hw]; exact indicator_norm _ _)

theorem survival_norm (s : ℝ≥0) : ‖survival τ hτ s‖≤1 := by
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (μ := μ) (by norm_num : (0:ℝ)≤1)
    ((survival_actual τ hτ s).mono fun w hw => by rw [hw]; exact indicator_norm _ _)

/-- Left strict-survival observations converge in the TRUE joint-source L2,
including atoms at the limiting time. -/
theorem survival_from_left (s : ℕ → ℝ≥0) (t : ℝ≥0) (hst : ∀ n,s n<t)
    (ht : Tendsto s atTop (𝓝 t)) :
    Tendsto (fun n => strictSurvival τ hτ (s n)) atTop (𝓝 (survival τ hτ t)) := by
  apply BochnerL2Approximation.tendsto_of_dominated _ _ jointOne
  · intro n
    filter_upwards [strictSurvival_actual τ hτ (s n),jointOne_ae] with w hw h1
    rw [hw,h1]; simpa using indicator_norm {w | s n<τ w} w
  · filter_upwards [survival_actual τ hτ t,jointOne_ae] with w hw h1
    rw [hw,h1]; simpa using indicator_norm {w | t≤τ w} w
  · filter_upwards [ae_all_iff.mpr (fun n => strictSurvival_actual τ hτ (s n)),survival_actual τ hτ t]
      with w hn hg
    simp only [hn,hg]
    by_cases htw : t≤τ w
    · have he (n : ℕ) : s n<τ w := (hst n).trans_le htw
      simp [he,htw]
    · have he : ∀ᶠ n in atTop, τ w<s n := ht.eventually_const_lt (lt_of_not_ge htw)
      simp only [Set.indicator_of_notMem (show w∉{w | t≤τ w} from htw)]
      have hz : (fun n => {w | s n<τ w}.indicator (fun _ => (1:ℝ)) w) =ᶠ[atTop] fun _ => 0 :=
        he.mono fun n hn => by simp [not_lt.mpr hn.le]
      exact (tendsto_congr' hz).mpr tendsto_const_nhds

private def coefficient (s : ℝ≥0) : jointPastL2 s := ⟨strictSurvival τ hτ s,strictSurvival_past τ hτ s⟩

def gridInput (T : ℝ≥0) (n : ℕ) : Input T :=
  ∑ i : Fin (n+1),jointStep T (uniformTime T n i.castSucc) (uniformTime T n i.succ)
    (coefficient τ hτ (uniformTime T n i.castSucc))

private def stepValue {m : ℕ} (t : Fin (m+1) → ℝ≥0) (r : ℝ) : JointL2 :=
  ∑ i : Fin m,(Ioc (t i.castSucc:ℝ) (t i.succ:ℝ)).indicator
    (fun _ => strictSurvival τ hτ (t i.castSucc)) r

private theorem step_on {m : ℕ} (t : Fin (m+1) → ℝ≥0) (ht : Monotone t)
    (i : Fin m) (r : ℝ) (hr : r∈Ioc (t i.castSucc:ℝ) (t i.succ:ℝ)) :
    stepValue τ hτ t r=strictSurvival τ hτ (t i.castSucc) := by
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
    timeSections T (fieldEmbedding T (gridInput τ hτ T n)) =ᵐ[timeLaw T]
      stepValue τ hτ (uniformTime T n) := by
  have hb (i : Fin (n+1)) : uniformTime T n i.succ≤T := by
    simpa only [(uniformTime_endpoints T n).2] using uniformTime_monotone T n (Fin.le_last i.succ)
  simp only [gridInput,map_sum]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin (n+1) =>
      timeSections T (fieldEmbedding T (jointStep T (uniformTime T n i.castSucc)
        (uniformTime T n i.succ) (coefficient τ hτ (uniformTime T n i.castSucc))))),
    ae_all_iff.mpr (fun i : Fin (n+1) => jointStep_slices T _ _
      (uniformTime_monotone T n (Fin.castSucc_le_succ i)) (hb i)
      (coefficient τ hτ (uniformTime T n i.castSucc)))] with r hs hi
  rw [hs]
  simp only [Finset.sum_apply,stepValue]
  exact Finset.sum_congr rfl fun i _ => hi i

private theorem step_tendsto (T : ℝ≥0) (r : ℝ) (hr : r∈Ioc 0 (T:ℝ)) :
    Tendsto (fun n => stepValue τ hτ (uniformTime T n) r) atTop
      (𝓝 (survival τ hτ r.toNNReal)) := by
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
  have hc := survival_from_left τ hτ s r.toNNReal hst hnn
  convert hc using 1
  funext n
  exact step_on τ hτ _ (uniformTime_monotone T n) (i n) r (hi n)

private def sections (T : ℝ≥0) : Input T →ₗᵢ[ℝ] Lp JointL2 2 (timeLaw T) :=
  (timeSections T).comp (fieldEmbedding T)

private theorem time_inside (T : ℝ≥0) : ∀ᵐ r ∂timeLaw T,r∈Ioc 0 (T:ℝ) :=
  ae_restrict_mem measurableSet_Ioc

private theorem grid_pointwise (T : ℝ≥0) : ∀ᵐ r ∂timeLaw T,
    Tendsto (fun n => sections T (gridInput τ hτ T n) r) atTop (𝓝 (survival τ hτ r.toNNReal)) := by
  filter_upwards [ae_all_iff.mpr (fun n => grid_slices τ hτ T n),time_inside T] with r hn hr
  change Tendsto (fun n => timeSections T (fieldEmbedding T (gridInput τ hτ T n)) r) _ _
  simpa only [hn] using step_tendsto τ hτ T r hr

private theorem target_memLp (T : ℝ≥0) : MemLp (fun r : ℝ => survival τ hτ r.toNNReal) 2 (timeLaw T) :=
  MemLp.of_bound (aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => Lp.aestronglyMeasurable (sections T (gridInput τ hτ T n)))
    (grid_pointwise τ hτ T)) 1 (Eventually.of_forall fun r => survival_norm τ hτ r.toNNReal)

private def target (T : ℝ≥0) : Lp JointL2 2 (timeLaw T) := (target_memLp τ hτ T).toLp _
private theorem target_actual (T : ℝ≥0) : target τ hτ T =ᵐ[timeLaw T] fun r => survival τ hτ r.toNNReal :=
  MemLp.coeFn_toLp _

private theorem grid_sections_tendsto (T : ℝ≥0) :
    Tendsto (fun n => sections T (gridInput τ hτ T n)) atTop (𝓝 (target τ hτ T)) := by
  let b : Lp ℝ 2 (timeLaw T) := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top _ _) (1:ℝ)
  have hb : b =ᵐ[timeLaw T] fun _ => (1:ℝ) := by
    simpa only [Set.indicator_univ] using (indicatorConstLp_coeFn (p := 2) (c := (1:ℝ))
      (μ := timeLaw T) (hs := MeasurableSet.univ) (hμs := measure_ne_top _ _))
  apply BochnerL2Approximation.tendsto_of_dominated _ _ b
  · intro n
    filter_upwards [hb,grid_slices τ hτ T n,time_inside T] with r hb hs hr
    obtain ⟨i,hi⟩ := GaussianQuadraticIto.uniformTime_covers T n r hr
    change ‖timeSections T (fieldEmbedding T (gridInput τ hτ T n)) r‖≤_
    rw [hb,hs,step_on τ hτ _ (uniformTime_monotone T n) i r hi]
    simpa using strictSurvival_norm τ hτ (uniformTime T n i.castSucc)
  · filter_upwards [hb,target_actual τ hτ T] with r hb ht
    rw [hb,ht]
    simpa using survival_norm τ hτ r.toNNReal
  · filter_upwards [grid_pointwise τ hτ T,target_actual τ hτ T] with r hr ht
    rw [ht];exact hr

/-- The target stopped indicator lies in the CLOSED ORIGINAL native range. -/
theorem stoppedInput_exists (T : ℝ≥0) :
    ∃ u : Input T,sections T u=target τ hτ T := by
  have hc : IsClosed (Set.range (sections T)) :=
    (sections T).isometry.isClosedEmbedding.isClosed_range
  exact hc.mem_of_tendsto (grid_sections_tendsto τ hτ T)
    (Eventually.of_forall fun n => ⟨gridInput τ hτ T n,rfl⟩)

def stoppedInput (T : ℝ≥0) : Input T := Classical.choose (stoppedInput_exists τ hτ T)
private theorem stoppedInput_sections (T : ℝ≥0) :
    sections T (stoppedInput τ hτ T)=target τ hτ T := Classical.choose_spec (stoppedInput_exists τ hτ T)

theorem gridInput_tendsto (T : ℝ≥0) :
    Tendsto (gridInput τ hτ T) atTop (𝓝 (stoppedInput τ hτ T)) := by
  apply (sections T).isometry.tendsto_nhds_iff.mpr
  simpa only [Function.comp_def,stoppedInput_sections τ hτ T] using grid_sections_tendsto τ hτ T

theorem stoppedInput_physical (T : ℝ≥0) :
    ∀ᵐ r ∂timeLaw T,∀ᵐ w ∂μ,fieldEmbedding T (stoppedInput τ hτ T) ((r,w.1),w.2)=
      (Ioc (0:ℝ) (τ w:ℝ)).indicator (fun _ => (1:ℝ)) r := by
  filter_upwards [timeSections_ae T (fieldEmbedding T (stoppedInput τ hτ T)),
    target_actual τ hτ T,time_inside T] with r hr ht hin
  change sections T (stoppedInput τ hτ T) r =ᵐ[μ] _ at hr
  rw [stoppedInput_sections τ hτ T,ht] at hr
  filter_upwards [hr,survival_actual τ hτ r.toNNReal] with w hw hs
  rw [← hw,hs]
  have he : r.toNNReal≤τ w ↔ r≤(τ w:ℝ) := by
    rw [Real.toNNReal_le_iff_le_coe]
  simp only [Set.indicator,Set.mem_ofPred_eq,Set.mem_Ioc,hin.1,true_and,he]

open ComplexL2Isometry StochasticCauchyComplexChannels
attribute [local instance] StochasticCauchyComplexChannels.complexInput_complete

/-- Both physical Brownian coordinates, with their original native integrators. -/
def valueIntegral (T : ℝ≥0) : Input T →L[ℝ] JointComplex :=
  (ofReal μ).comp (integralX T).toContinuousLinearMap+
    Complex.I • ((ofReal μ).comp (integralY T).toContinuousLinearMap)

private theorem valueIntegral_apply (T : ℝ≥0) (u : Input T) :
    valueIntegral T u=combine μ (integralX T u) (integralY T u) := rfl

private theorem valueIntegral_step (T s t : ℝ≥0) (hst : s≤t) (htT : t≤T) (C : jointPastL2 s) :
    valueIntegral T (jointStep T s t C) =ᵐ[μ] fun w => (C.val w:ℂ)*
      (StochasticCauchyPolynomialPrediction.position t w-StochasticCauchyPolynomialPrediction.position s w) := by
  rw [valueIntegral_apply]
  filter_upwards [combine_ae μ _ _,(jointStep_integrals T s t hst htT C).1,
    (jointStep_integrals T s t hst htT C).2] with w hc hx hy
  rw [hc,hx,hy]
  apply Complex.ext <;> simp [StochasticCauchyPolynomialPrediction.position]

private def pathSum {m : ℕ} (t : Fin (m+1) → ℝ≥0) (c : ℝ≥0) (v : ℝ≥0 → ℂ) : ℂ :=
  ∑ i : Fin m,if t i.castSucc<c then v (t i.succ)-v (t i.castSucc) else 0

private theorem pathSum_cell {m : ℕ} (t : Fin (m+1) → ℝ≥0) (ht : Monotone t)
    (c : ℝ≥0) (v : ℝ≥0 → ℂ) (i : Fin m) (hi : t i.castSucc<c ∧ c≤t i.succ) :
    pathSum t c v=v (t i.succ)-v (t 0) := by
  have he (j : Fin m) : t j.castSucc<c ↔ j≤ i := by
    constructor
    · intro hj
      by_contra hji
      have hle := ht (Fin.succ_le_castSucc_iff.mpr (lt_of_not_ge hji))
      exact (not_lt_of_ge (hi.2.trans hle)) hj
    · intro hj;exact (ht (Fin.castSucc_le_castSucc_iff.mpr hj)).trans_lt hi.1
  simp only [pathSum,he]
  rw [← Finset.sum_filter]
  have hs : Finset.univ.filter (fun j : Fin m => j≤ i)=Finset.Iic i := by ext j;simp
  rw [hs]
  exact Fin.sum_Iic_sub i (fun j => v (t j))

private theorem pathSum_all (T : ℝ≥0) (n : ℕ) (c : ℝ≥0) (hc : T<c) (v : ℝ≥0 → ℂ) :
    pathSum (uniformTime T n) c v=v T-v 0 := by
  have he (i : Fin (n+1)) : uniformTime T n i.castSucc<c := by
    have hle : uniformTime T n i.castSucc≤T := by
      simpa only [(uniformTime_endpoints T n).2] using
        uniformTime_monotone T n (Fin.le_last i.castSucc)
    exact hle.trans_lt hc
  simp only [pathSum,he,ite_true]
  have hsum := Fin.sum_Iic_sub (Fin.last n) (fun j => v (uniformTime T n j))
  have hh : Finset.Iic (Fin.last n)=Finset.univ := by
    ext j;simp only [Finset.mem_Iic,Finset.mem_univ,iff_true];exact Fin.le_last _
  rw [hh,show (Fin.last n).succ=Fin.last (n+1) from rfl] at hsum
  simpa only [(uniformTime_endpoints T n).1,(uniformTime_endpoints T n).2] using hsum

/-- Pathwise convergence of actual stopped increment sums; no L2 bound on
sampled Brownian values is assumed. -/
private theorem pathSum_tendsto (T : ℝ≥0) (c : ℝ≥0) (v : ℝ≥0 → ℂ) (hv : Continuous v) :
    Tendsto (fun n => pathSum (uniformTime T n) c v) atTop (𝓝 (v (min T c)-v 0)) := by
  by_cases hc : c=0
  · subst c
    simp only [pathSum,not_lt_zero,ite_false,Finset.sum_const_zero,min_zero,sub_self]
    exact tendsto_const_nhds
  by_cases hcT : c≤T
  · have hp : 0<(c:ℝ) := by exact_mod_cast (lt_of_le_of_ne bot_le (Ne.symm hc))
    choose i hi using fun n => GaussianQuadraticIto.uniformTime_covers T n c ⟨hp,hcT⟩
    have hn (n : ℕ) : ‖(uniformTime T n (i n).succ:ℝ)-(c:ℝ)‖≤(T:ℝ)/(n+1) := by
      rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (hi n).2)]
      have hs := uniformTime_step T n (i n)
      linarith [(hi n).1]
    have hz : Tendsto (fun n : ℕ => (T:ℝ)/(n+1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have hr := tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun n => norm_nonneg _) hn hz)
    have hnn := continuous_real_toNNReal.continuousAt.tendsto.comp hr
    simp only [Function.comp_def,Real.toNNReal_coe] at hnn
    have hvv := (hv.continuousAt.tendsto.comp hnn).sub_const (v 0)
    rw [min_eq_right hcT]
    convert hvv using 1
    funext n
    have hcell : uniformTime T n (i n).castSucc<c ∧ c≤uniformTime T n (i n).succ :=
      ⟨(hi n).1,(hi n).2⟩
    simpa only [(uniformTime_endpoints T n).1,Function.comp_apply] using
      pathSum_cell (uniformTime T n) (uniformTime_monotone T n) c v (i n) hcell
  · have hTc := lt_of_not_ge hcT
    simp only [pathSum_all T _ c hTc v,min_eq_left hTc.le]
    exact tendsto_const_nhds

private theorem gridValue_actual (T : ℝ≥0) (n : ℕ) :
    valueIntegral T (gridInput τ hτ T n) =ᵐ[μ] fun w =>
      pathSum (uniformTime T n) (τ w) (fun t => StochasticCauchyBrownianRealization.value t w) := by
  have hb (i : Fin (n+1)) : uniformTime T n i.succ≤T := by
    simpa only [(uniformTime_endpoints T n).2] using uniformTime_monotone T n (Fin.le_last i.succ)
  rw [gridInput,map_sum]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin (n+1) =>
      valueIntegral T (jointStep T (uniformTime T n i.castSucc) (uniformTime T n i.succ)
        (coefficient τ hτ (uniformTime T n i.castSucc)))),
    ae_all_iff.mpr (fun i : Fin (n+1) => valueIntegral_step T _ _
      (uniformTime_monotone T n (Fin.castSucc_le_succ i)) (hb i)
      (coefficient τ hτ (uniformTime T n i.castSucc))),
    ae_all_iff.mpr (fun i : Fin (n+1) => strictSurvival_actual τ hτ (uniformTime T n i.castSucc)),
    ae_all_iff.mpr (fun i : Fin (n+2) => StochasticCauchyContinuousPolynomials.continuous_value_ae (uniformTime T n i))]
    with w hs hi hc hz
  rw [hs]
  simp only [Finset.sum_apply,pathSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hi i]
  change (strictSurvival τ hτ (uniformTime T n i.castSucc) w:ℂ)*_=_
  rw [hc i,← hz i.succ,← hz i.castSucc]
  by_cases hw : uniformTime T n i.castSucc<τ w <;> simp [hw]

/-- The ORIGINAL native integral is the ACTUAL continuous Brownian value at
the clipped stopping time, with no sampled-value L2 assumption. -/
theorem stoppedValue_actual (T : ℝ≥0) :
    valueIntegral T (stoppedInput τ hτ T) =ᵐ[μ] stopped T τ := by
  have hl := ((valueIntegral T).continuous.tendsto (stoppedInput τ hτ T)).comp (gridInput_tendsto τ hτ T)
  obtain ⟨ns,hns,hn⟩ := (tendstoInMeasure_of_tendsto_Lp hl).exists_seq_tendsto_ae
  filter_upwards [hn,ae_all_iff.mpr (fun n => gridValue_actual τ hτ T n),
    StochasticCauchyBrownianRealization.value_zero_ae] with w hn hall h0
  have hp := (pathSum_tendsto T (τ w) (fun t => StochasticCauchyBrownianRealization.value t w)
    (StochasticCauchyBrownianRealization.value_continuous w)).comp hns.tendsto_atTop
  simp only [Function.comp_apply,hall] at hn
  rw [h0,sub_zero] at hp
  exact tendsto_nhds_unique hn hp

include hτ in
theorem stoppedValue_memLp (T : ℝ≥0) : MemLp (stopped T τ) 2 μ :=
  (Lp.memLp (valueIntegral T (stoppedInput τ hτ T))).ae_eq (stoppedValue_actual τ hτ T)

/-- The physical dZ input against the ORIGINAL normalized channel. -/
def stoppedComplexInput (T : ℝ≥0) : ComplexInput T :=
  ((Real.sqrt 2:ℝ):ℂ) • combineInput T (stoppedInput τ hτ T) 0

theorem stoppedInput_parts (T : ℝ≥0) :
    realInput T (stoppedComplexInput τ hτ T)=Real.sqrt 2 • stoppedInput τ hτ T ∧
      imagInput T (stoppedComplexInput τ hτ T)=0 := by
  constructor <;>
    simp only [stoppedComplexInput,realInput_smul,imagInput_smul,realInput_combine,imagInput_combine,
      Complex.ofReal_re,Complex.ofReal_im,zero_smul,sub_zero,add_zero,smul_zero]

private theorem channel_valueIntegral (T : ℝ≥0) :
    channel T false (stoppedComplexInput τ hτ T)=valueIntegral T (stoppedInput τ hτ T) := by
  rw [stoppedComplexInput,StochasticCauchyExponentialReconstruction.normalized_channel_combine,
    map_zero,sub_zero,map_zero,zero_add,valueIntegral_apply]

theorem stopped_channel_actual (T : ℝ≥0) :
    channel T false (stoppedComplexInput τ hτ T) =ᵐ[μ] stopped T τ := by
  rw [channel_valueIntegral];exact stoppedValue_actual τ hτ T

/-- The L2 class is defined from actual stopped path evaluation. -/
def sampledClass (T : ℝ≥0) : JointComplex := (stoppedValue_memLp τ hτ T).toLp (stopped T τ)

theorem sampledClass_actual (T : ℝ≥0) : sampledClass τ hτ T =ᵐ[μ] stopped T τ := MemLp.coeFn_toLp _

theorem stopped_channel (T : ℝ≥0) :
    channel T false (stoppedComplexInput τ hτ T)=sampledClass τ hτ T :=
  Lp.ext ((stopped_channel_actual τ hτ T).trans (sampledClass_actual τ hτ T).symm)

include hτ in
theorem stopped_mean_zero (T : ℝ≥0) : (∫ w,stopped T τ w ∂μ)=0 := by
  rw [← integral_congr_ae (stopped_channel_actual τ hτ T)]
  exact StochasticCauchyMeanResidual.channel_centered T false (stoppedComplexInput τ hτ T)

/-- Uniqueness is in the original complex native input domain. -/
theorem stopped_channel_unique (T : ℝ≥0) (u : ComplexInput T)
    (hu : channel T false u =ᵐ[μ] stopped T τ) : u=stoppedComplexInput τ hτ T :=
  (channel T false).injective (Lp.ext (hu.trans (stopped_channel_actual τ hτ T).symm))

theorem stopped_canonical_inputs (T : ℝ≥0) :
    channelAdjoint T false (sampledClass τ hτ T)=stoppedComplexInput τ hτ T ∧
      channelAdjoint T true (sampledClass τ hτ T)=0 := by
  have h := channel_coefficients_recover T (stoppedComplexInput τ hτ T) 0
  simpa only [map_zero,add_zero,stopped_channel τ hτ T] using h

/-- Actual finite chronological sums on the continuous-path realization. -/
def chronologicalSum (T : ℝ≥0) (n : ℕ) (w : Sample) : ℂ :=
  pathSum (uniformTime T n) (τ w) (fun t => StochasticCauchyBrownianRealization.value t w)

theorem chronological_actual (T : ℝ≥0) (n : ℕ) :
    valueIntegral T (gridInput τ hτ T n) =ᵐ[μ] chronologicalSum τ T n := gridValue_actual τ hτ T n

theorem chronological_L2_tendsto (T : ℝ≥0) :
    Tendsto (fun n => valueIntegral T (gridInput τ hτ T n)) atTop (𝓝 (sampledClass τ hτ T)) := by
  have hl := ((valueIntegral T).continuous.tendsto (stoppedInput τ hτ T)).comp (gridInput_tendsto τ hτ T)
  have he := (channel_valueIntegral τ hτ T).symm.trans (stopped_channel τ hτ T)
  rwa [he] at hl

include hτ in
theorem chronological_mean_square (T : ℝ≥0) :
    Tendsto (fun n => ∫ w,‖chronologicalSum τ T n w-stopped T τ w‖^2 ∂μ) atTop (𝓝 0) := by
  have hl := chronological_L2_tendsto τ hτ T
  have hn : Tendsto (fun n => ‖valueIntegral T (gridInput τ hτ T n)-sampledClass τ hτ T‖^2) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)] using
      ((hl.sub_const (sampledClass τ hτ T)).norm.pow 2)
  have he (n : ℕ) : ‖valueIntegral T (gridInput τ hτ T n)-sampledClass τ hτ T‖^2=
      ∫ w,‖chronologicalSum τ T n w-stopped T τ w‖^2 ∂μ := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (valueIntegral T (gridInput τ hτ T n)) (sampledClass τ hτ T),
      chronological_actual τ hτ T n,sampledClass_actual τ hτ T] with w hs hf hg
    simp only [hs,Pi.sub_apply,hf,hg]
  simpa only [he] using hn

end OperatorDerivativeRewrite.Foundation.StochasticCauchyStoppedIndicators