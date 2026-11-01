import Foundation.StochasticCauchyExponentialPrediction
import Foundation.GaussianHermiteTimeKernel
import Foundation.BochnerL2Approximation
import Foundation.GaussianContinuousIntegrands

/-! Actual source/time fields for the exponential's chronological input.
The physical native range remains the existing closed past-step range. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyExponentialInput
open InfiniteGaussian ProductL2Curry ComplexL2Isometry
open StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyExponentialPrediction StochasticCauchyPhysicalInput
open StochasticCauchyComplexChannels
open GaussianTimeProcess GaussianTimeHilbert GaussianBrownianQuadraticVariation
attribute [local instance] StochasticCauchyJointPastIntegral.input_complete
  StochasticCauchyJointPastIntegral.swapped_complete timeHilbert_secondCountable
  StochasticCauchyParameterizedObstruction.finiteL2Exponent

abbrev timeLaw (T : ℝ≥0) : Measure ℝ := volume.restrict (Ioc 0 (T : ℝ))

private theorem unassociate_preserving (T : ℝ≥0) :
    MeasurePreserving (fun q : ℝ × (SampleSpace × SampleSpace) => ((q.1,q.2.1),q.2.2))
      ((timeLaw T).prod (gaussianProduct.prod gaussianProduct))
      ((timeMeasure T).prod gaussianProduct) := by
  rw [timeMeasure,PredictableRealL2.horizonMeasure_eq_product]
  exact (measurePreserving_prodAssoc (timeLaw T) gaussianProduct gaussianProduct).symm

/-- Actual reassociation and source sections, with the physical time retained. -/
def timeSections (T : ℝ≥0) : Field T →ₗᵢ[ℝ] Lp JointL2 2 (timeLaw T) :=
  (curryEquiv (timeLaw T) (gaussianProduct.prod gaussianProduct)).toLinearIsometry.comp
    (Lp.compMeasurePreservingₗᵢ ℝ
      (fun q : ℝ × (SampleSpace × SampleSpace) => ((q.1,q.2.1),q.2.2))
      (unassociate_preserving T))

theorem timeSections_ae (T : ℝ≥0) (F : Field T) :
    ∀ᵐ t ∂timeLaw T, timeSections T F t =ᵐ[gaussianProduct.prod gaussianProduct]
      fun w => F ((t,w.1),w.2) := by
  have ha := Lp.coeFn_compMeasurePreserving F (unassociate_preserving T)
  have hc := curryEquiv_coeFn (timeLaw T) (gaussianProduct.prod gaussianProduct)
    (Lp.compMeasurePreservingₗᵢ ℝ _ (unassociate_preserving T) F)
  filter_upwards [hc,ae_ae_of_ae_prod ha] with t hc ha
  exact hc.trans ha

def realCurve (t : ℝ≥0) : JointL2 :=
  realPart (gaussianProduct.prod gaussianProduct) (observable t)

def imagCurve (t : ℝ≥0) : JointL2 :=
  imagPart (gaussianProduct.prod gaussianProduct) (observable t)

theorem realCurve_continuous : Continuous realCurve :=
  (realPart (gaussianProduct.prod gaussianProduct)).continuous.comp observable_continuous

theorem imagCurve_continuous : Continuous imagCurve :=
  (imagPart (gaussianProduct.prod gaussianProduct)).continuous.comp observable_continuous

private theorem exp_memLp (t : ℝ≥0) : MemLp (fun w => Real.exp (process t w)) 2 gaussianProduct := by
  have he := StochasticCauchyExponential.absolute_exp_memLp
    (SeparableHilbertEmbedding.hilbertEmbedding TimeHilbert (timeVector t))
  apply he.mono' ((Real.continuous_exp.comp_stronglyMeasurable
    (process_stronglyMeasurable t)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro w
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (le_abs_self _)

private theorem cos_memLp (t : ℝ≥0) : MemLp (fun w => Real.cos (process t w)) 2 gaussianProduct :=
  (memLp_const (1:ℝ)).mono' ((Real.continuous_cos.comp_stronglyMeasurable
    (process_stronglyMeasurable t)).aestronglyMeasurable)
    (Eventually.of_forall fun w => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (process t w))

private theorem sin_memLp (t : ℝ≥0) : MemLp (fun w => Real.sin (process t w)) 2 gaussianProduct :=
  (memLp_const (1:ℝ)).mono' ((Real.continuous_sin.comp_stronglyMeasurable
    (process_stronglyMeasurable t)).aestronglyMeasurable)
    (Eventually.of_forall fun w => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (process t w))

def expClass (t : ℝ≥0) : GaussianL2 := (exp_memLp t).toLp _
def cosClass (t : ℝ≥0) : GaussianL2 := (cos_memLp t).toLp _
def sinClass (t : ℝ≥0) : GaussianL2 := (sin_memLp t).toLp _

theorem expClass_past (t : ℝ≥0) :
    AEStronglyMeasurable[naturalFiltration t] (expClass t) gaussianProduct :=
  (Real.continuous_exp.comp_stronglyMeasurable (process_stronglyAdapted t)).aestronglyMeasurable.congr
    (exp_memLp t).coeFn_toLp.symm

theorem cosClass_past (t : ℝ≥0) :
    AEStronglyMeasurable[naturalFiltration t] (cosClass t) gaussianProduct :=
  (Real.continuous_cos.comp_stronglyMeasurable (process_stronglyAdapted t)).aestronglyMeasurable.congr
    (cos_memLp t).coeFn_toLp.symm

theorem sinClass_past (t : ℝ≥0) :
    AEStronglyMeasurable[naturalFiltration t] (sinClass t) gaussianProduct :=
  (Real.continuous_sin.comp_stronglyMeasurable (process_stronglyAdapted t)).aestronglyMeasurable.congr
    (sin_memLp t).coeFn_toLp.symm

theorem realCurve_tensor (t : ℝ≥0) : realCurve t=
    productTensor gaussianProduct gaussianProduct (expClass t) (cosClass t) := by
  apply Lp.ext
  have hx := (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
    (exp_memLp t).coeFn_toLp
  have hy := (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
    (cos_memLp t).coeFn_toLp
  filter_upwards [Complex.reCLM.coeFn_compLpL (observable t),observable_ae t,hx,hy,
    productTensor_coeFn gaussianProduct gaussianProduct (expClass t) (cosClass t)] with w hr he hx hy ht
  change realCurve t w=(observable t w).re at hr
  simp only [Function.comp_apply] at hx hy
  change expClass t w.1=Real.exp (process t w.1) at hx
  change cosClass t w.2=Real.cos (process t w.2) at hy
  rw [hr,he,ht,hx,hy]
  simp [value,Complex.exp_re,smul_eq_mul]

theorem imagCurve_tensor (t : ℝ≥0) : imagCurve t=
    productTensor gaussianProduct gaussianProduct (expClass t) (sinClass t) := by
  apply Lp.ext
  have hx := (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
    (exp_memLp t).coeFn_toLp
  have hy := (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
    (sin_memLp t).coeFn_toLp
  filter_upwards [Complex.imCLM.coeFn_compLpL (observable t),observable_ae t,hx,hy,
    productTensor_coeFn gaussianProduct gaussianProduct (expClass t) (sinClass t)] with w hr he hx hy ht
  change imagCurve t w=(observable t w).im at hr
  simp only [Function.comp_apply] at hx hy
  change expClass t w.1=Real.exp (process t w.1) at hx
  change sinClass t w.2=Real.sin (process t w.2) at hy
  rw [hr,he,ht,hx,hy]
  simp [value,Complex.exp_im,smul_eq_mul]

theorem timeSections_step (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (A B : GaussianL2)
    (hA : AEStronglyMeasurable[naturalFiltration s] A gaussianProduct)
    (hB : AEStronglyMeasurable[naturalFiltration s] B gaussianProduct) :
    timeSections T (fieldEmbedding T (stepInput T s t hst htT A B hA hB))
      =ᵐ[timeLaw T] fun r => (Ioc (s : ℝ) (t : ℝ)).indicator
        (fun _ => productTensor gaussianProduct gaussianProduct A B) r := by
  have hp := (unassociate_preserving T).quasiMeasurePreserving.ae_eq_comp
    (fieldEmbedding_step_ae T s t hst htT A B hA hB)
  filter_upwards [timeSections_ae T (fieldEmbedding T
    (stepInput T s t hst htT A B hA hB)),ae_ae_of_ae_prod hp] with r hc hp
  apply Lp.ext
  by_cases hr : r ∈ Ioc (s : ℝ) (t : ℝ)
  · rw [indicator_of_mem hr]
    filter_upwards [hc,hp,productTensor_coeFn gaussianProduct gaussianProduct A B]
      with w hc hp ht
    rw [hc]
    change fieldEmbedding T (stepInput T s t hst htT A B hA hB) ((r,w.1),w.2)=_ at hp
    simpa only [Function.comp_apply,indicator_of_mem hr,ht,smul_eq_mul] using hp
  · rw [indicator_of_notMem hr]
    filter_upwards [hc,hp,Lp.coeFn_zero ℝ 2 (gaussianProduct.prod gaussianProduct)]
      with w hc hp hz
    rw [hc,hz]
    change fieldEmbedding T (stepInput T s t hst htT A B hA hB) ((r,w.1),w.2)=_ at hp
    simpa only [Function.comp_apply,indicator_of_notMem hr,Pi.zero_apply] using hp

private theorem running_memLp (v : ℝ≥0 → JointL2) (hv : Continuous v) (T : ℝ≥0) :
    MemLp (fun r : ℝ => v r.toNNReal) 2 (timeLaw T) := by
  exact (memLp_indicator_iff_restrict measurableSet_Ioc).mp
    (GaussianHermiteTimeKernel.continuous_interval_memLp
      (fun r => v r.toNNReal) (hv.comp continuous_real_toNNReal) T)

def running (v : ℝ≥0 → JointL2) (hv : Continuous v) (T : ℝ≥0) :
    Lp JointL2 2 (timeLaw T) := (running_memLp v hv T).toLp _

theorem running_ae (v : ℝ≥0 → JointL2) (hv : Continuous v) (T : ℝ≥0) :
    running v hv T =ᵐ[timeLaw T] fun r => v r.toNNReal :=
  (running_memLp v hv T).coeFn_toLp

private theorem timeLaw_finite (T : ℝ≥0) : IsFiniteMeasure (timeLaw T) :=
  ⟨by simp [timeLaw]⟩
attribute [local instance] timeLaw_finite

private def stepCurve (v : ℝ≥0 → JointL2) (T : ℝ≥0) (N : ℕ) (r : ℝ) : JointL2 :=
  ∑ i : Fin (N + 1), (Ioc (uniformTime T N i.castSucc : ℝ)
    (uniformTime T N i.succ : ℝ)).indicator (fun _ => v (uniformTime T N i.castSucc)) r

private theorem stepCurve_cell (v : ℝ≥0 → JointL2) (T : ℝ≥0) (N : ℕ)
    (i : Fin (N + 1)) (r : ℝ)
    (hr : r ∈ Ioc (uniformTime T N i.castSucc : ℝ) (uniformTime T N i.succ : ℝ)) :
    stepCurve v T N r=v (uniformTime T N i.castSucc) := by
  rw [stepCurve,Finset.sum_eq_single i,indicator_of_mem hr]
  · intro j _ hji
    apply indicator_of_notMem
    intro hj
    rcases lt_or_gt_of_ne hji with hjlt | hjgt
    · have he : (uniformTime T N j.succ:ℝ) ≤ uniformTime T N i.castSucc :=
        uniformTime_monotone T N (Fin.succ_le_castSucc_iff.mpr hjlt)
      linarith [hr.1,hj.2]
    · have he : (uniformTime T N i.succ : ℝ) ≤ uniformTime T N j.castSucc :=
        uniformTime_monotone T N (Fin.succ_le_castSucc_iff.mpr hjgt)
      linarith [hj.1,hr.2]
  · simp

private theorem stepCurve_limit (v : ℝ≥0 → JointL2) (hv : Continuous v)
    (T : ℝ≥0) (r : ℝ) (hr : r ∈ Ioc 0 (T : ℝ)) :
    Tendsto (fun N => stepCurve v T N r) atTop (𝓝 (v r.toNNReal)) := by
  choose i hi using fun N => GaussianQuadraticIto.uniformTime_covers T N r hr
  have hb (N : ℕ) : ‖(uniformTime T N (i N).castSucc:ℝ)-r‖ ≤ (T : ℝ)/(N + 1) := by
    rw [Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr (hi N).1.le)]
    linarith [(hi N).2,uniformTime_step T N (i N)]
  have hs : Tendsto (fun N : ℕ => (T : ℝ)/(N + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have ht := tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun _ => norm_nonneg _) hb hs)
  have hn := continuous_real_toNNReal.continuousAt.tendsto.comp ht
  simp only [Function.comp_def,Real.toNNReal_coe] at hn
  have hc := (hv.tendsto r.toNNReal).comp hn
  convert hc using 1
  funext N
  exact stepCurve_cell v T N (i N) r (hi N)

private theorem stepCurve_tendsto (v : ℝ≥0 → JointL2) (hv : Continuous v) (T : ℝ≥0)
    (F : ℕ → Lp JointL2 2 (timeLaw T))
    (hF : ∀ N, F N =ᵐ[timeLaw T] stepCurve v T N) :
    Tendsto F atTop (𝓝 (running v hv T)) := by
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hv.comp continuous_real_toNNReal).continuousOn (s := Icc 0 (T : ℝ))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl,T.coe_nonneg⟩)
  let B : Lp ℝ 2 (timeLaw T) := (memLp_const M).toLp (fun _ => M)
  have hB : B =ᵐ[timeLaw T] fun _ => M := (memLp_const M).coeFn_toLp
  have hm : ∀ᵐ r ∂timeLaw T, r ∈ Ioc 0 (T : ℝ) := ae_restrict_mem measurableSet_Ioc
  apply BochnerL2Approximation.tendsto_of_dominated F (running v hv T) B
  · intro N
    filter_upwards [hF N,hB,hm] with r hf hb hr
    obtain ⟨i,hi⟩ := GaussianQuadraticIto.uniformTime_covers T N r hr
    rw [hf,hb,stepCurve_cell v T N i r hi,Real.norm_eq_abs,abs_of_nonneg hM0]
    have hh := hM (uniformTime T N i.castSucc)
      ⟨(uniformTime T N i.castSucc).coe_nonneg,(hi.1.trans_le hr.2).le⟩
    simpa only [Function.comp_apply,Real.toNNReal_coe] using hh
  · filter_upwards [running_ae v hv T,hB,hm] with r hv hb hr
    rw [hv,hb,Real.norm_eq_abs,abs_of_nonneg hM0]
    exact hM r ⟨hr.1.le,hr.2⟩
  · filter_upwards [ae_all_iff.mpr hF,running_ae v hv T,hm] with r hf hvv hr
    simpa only [hf,hvv] using stepCurve_limit v hv T r hr

/-- Reuse of the existing generic grid convergence in the ORIGINAL native
domain. The hypothesis specifies actual physical time sections of actual
native steps; no predictable-space density or surrogate integral is assumed. -/
theorem running_native_of_steps (v : ℝ≥0 → JointL2) (hv : Continuous v) (T : ℝ≥0)
    (F : ℕ → Input T)
    (hF : ∀ N, timeSections T (fieldEmbedding T (F N)) =ᵐ[timeLaw T]
      fun r => ∑ i : Fin (N + 1),
        (Ioc (uniformTime T N i.castSucc : ℝ) (uniformTime T N i.succ : ℝ)).indicator
          (fun _ => v (uniformTime T N i.castSucc)) r) :
    ∃ u : Input T, timeSections T (fieldEmbedding T u) = running v hv T ∧
      Tendsto F atTop (𝓝 u) := by
  let J := (timeSections T).comp (fieldEmbedding T)
  have ht := stepCurve_tendsto v hv T (fun N => timeSections T (fieldEmbedding T (F N))) hF
  have hc : IsClosed (Set.range J) := J.isometry.isClosedEmbedding.isClosed_range
  obtain ⟨u, hu⟩ := hc.mem_of_tendsto ht (Eventually.of_forall fun N => ⟨F N, rfl⟩)
  refine ⟨u, hu, ?_⟩
  apply J.isometry.isEmbedding.tendsto_nhds_iff.mpr
  change Tendsto (fun N => J (F N)) atTop (𝓝 (J u))
  rw [hu]
  exact ht

def component (b : Bool) : ℝ≥0 → JointL2 := if b then imagCurve else realCurve
theorem component_continuous (b : Bool) : Continuous (component b) := by
  cases b
  · exact realCurve_continuous
  · exact imagCurve_continuous

def componentStep (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (b : Bool) : Input T :=
  stepInput T s t hst htT (expClass s) (if b then sinClass s else cosClass s)
    (expClass_past s) (by cases b <;> first | exact cosClass_past _ | exact sinClass_past _)

private theorem componentStep_sections (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T) (b : Bool) :
    timeSections T (fieldEmbedding T (componentStep T s t hst htT b)) =ᵐ[timeLaw T]
      fun r => (Ioc (s : ℝ) (t : ℝ)).indicator (fun _ => component b s) r := by
  cases b
  · simpa only [componentStep,component,Bool.false_eq_true,ite_false,← realCurve_tensor] using
      timeSections_step T s t hst htT (expClass s) (cosClass s)
        (expClass_past s) (cosClass_past s)
  · simpa only [componentStep,component,ite_true,← imagCurve_tensor] using
      timeSections_step T s t hst htT (expClass s) (sinClass s)
        (expClass_past s) (sinClass_past s)

private def gridStep (T : ℝ≥0) (N : ℕ) (b : Bool) (i : Fin (N + 1)) : Input T :=
  componentStep T (uniformTime T N i.castSucc) (uniformTime T N i.succ)
    (uniformTime_monotone T N (Fin.castSucc_le_succ i))
    (by simpa only [(uniformTime_endpoints T N).2] using
      uniformTime_monotone T N (Fin.le_last i.succ)) b

private theorem gridStep_sections (T : ℝ≥0) (N : ℕ) (b : Bool) (i : Fin (N + 1)) :
    timeSections T (fieldEmbedding T (gridStep T N b i)) =ᵐ[timeLaw T]
      fun r => (Ioc (uniformTime T N i.castSucc : ℝ) (uniformTime T N i.succ : ℝ)).indicator
        (fun _ => component b (uniformTime T N i.castSucc)) r :=
  componentStep_sections T _ _ _ _ b

attribute [local irreducible] timeSections fieldEmbedding componentStep gridStep

def componentSteps (T : ℝ≥0) (N : ℕ) (b : Bool) : Input T := ∑ i, gridStep T N b i

private theorem componentSteps_sections (T : ℝ≥0) (N : ℕ) (b : Bool) :
    timeSections T (fieldEmbedding T (componentSteps T N b))
      =ᵐ[timeLaw T] stepCurve (component b) T N := by
  rw [componentSteps,_root_.map_sum,_root_.map_sum]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun i : Fin (N + 1) => timeSections T (fieldEmbedding T (gridStep T N b i))),
    ae_all_iff.mpr (gridStep_sections T N b)] with r hs ht
  rw [hs]
  unfold stepCurve
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => ht i)

theorem componentSteps_tendsto (T : ℝ≥0) (b : Bool) :
    Tendsto (fun N => timeSections T (fieldEmbedding T (componentSteps T N b))) atTop
      (𝓝 (running (component b) (component_continuous b) T)) :=
  stepCurve_tendsto _ (component_continuous b) T _ (fun N => componentSteps_sections T N b)

/-- The genuine running exponential components belong to the OLD native domain. -/
theorem running_component_native (T : ℝ≥0) (b : Bool) :
    ∃ u : Input T, timeSections T (fieldEmbedding T u)=
      running (component b) (component_continuous b) T := by
  let J := (timeSections T).comp (fieldEmbedding T)
  have hc : IsClosed (Set.range J) := J.isometry.isClosedEmbedding.isClosed_range
  exact hc.mem_of_tendsto (componentSteps_tendsto T b)
    (Eventually.of_forall fun N => ⟨componentSteps T N b,rfl⟩)

def componentInput (T : ℝ≥0) (b : Bool) : Input T :=
  (running_component_native T b).choose

theorem componentInput_sections (T : ℝ≥0) (b : Bool) :
    timeSections T (fieldEmbedding T (componentInput T b))=
      running (component b) (component_continuous b) T :=
  (running_component_native T b).choose_spec

/-- Convergence holds in the actual OLD native stochastic input norm. -/
theorem componentInput_tendsto (T : ℝ≥0) (b : Bool) :
    Tendsto (fun N => componentSteps T N b) atTop (𝓝 (componentInput T b)) := by
  let J := (timeSections T).comp (fieldEmbedding T)
  have ht := componentSteps_tendsto T b
  rw [← componentInput_sections T b] at ht
  apply J.isometry.isEmbedding.tendsto_nhds_iff.mpr
  simpa only [J,LinearIsometry.coe_comp,Function.comp_def] using ht

def componentValue (b : Bool) (t : ℝ≥0) (w : SampleSpace × SampleSpace) : ℝ :=
  if b then (value t w).im else (value t w).re

theorem component_ae (b : Bool) (t : ℝ≥0) :
    component b t =ᵐ[gaussianProduct.prod gaussianProduct] componentValue b t := by
  cases b
  · filter_upwards [Complex.reCLM.coeFn_compLpL (observable t),observable_ae t] with w hr he
    change realCurve t w=(observable t w).re at hr
    change realCurve t w=(value t w).re
    rw [hr,he]
  · filter_upwards [Complex.imCLM.coeFn_compLpL (observable t),observable_ae t] with w hi he
    change imagCurve t w=(observable t w).im at hi
    change imagCurve t w=(value t w).im
    rw [hi,he]

/-- The constructed OLD native input has the actual running exponential slices.
No joint measurability of arbitrary chosen representatives was presumed. -/
theorem componentInput_slices (T : ℝ≥0) (b : Bool) :
    ∀ᵐ r ∂timeLaw T, (fun w : SampleSpace × SampleSpace =>
      fieldEmbedding T (componentInput T b) ((r,w.1),w.2))
      =ᵐ[gaussianProduct.prod gaussianProduct] componentValue b r.toNNReal := by
  have he : timeSections T (fieldEmbedding T (componentInput T b)) =ᵐ[timeLaw T]
      fun r => component b r.toNNReal := by
    rw [componentInput_sections]
    exact running_ae _ (component_continuous b) T
  filter_upwards [timeSections_ae T (fieldEmbedding T (componentInput T b)),he]
    with r hs he
  rw [he] at hs
  exact hs.symm.trans (component_ae b r.toNNReal)

attribute [local instance] StochasticCauchyParameterizedObstruction.predictableTime

/-- Candidate for the normalized dZ/sqrt2 channel; its integral value is not
asserted here. Both parts are actual completed chronological native inputs. -/
def normalizedInput (T : ℝ≥0) : ComplexInput T :=
  ((Real.sqrt 2:ℝ):ℂ) • combineInput T (componentInput T false) (componentInput T true)

def normalizedSteps (T : ℝ≥0) (N : ℕ) : ComplexInput T :=
  ((Real.sqrt 2:ℝ):ℂ) • combineInput T (componentSteps T N false) (componentSteps T N true)

theorem normalizedInput_parts (T : ℝ≥0) :
    realInput T (normalizedInput T)=Real.sqrt 2 • componentInput T false ∧
    imagInput T (normalizedInput T)=Real.sqrt 2 • componentInput T true := by
  constructor
  · simp only [normalizedInput,realInput_smul,realInput_combine,imagInput_combine,
      Complex.ofReal_re,Complex.ofReal_im,zero_smul,sub_zero]
  · simp only [normalizedInput,imagInput_smul,realInput_combine,imagInput_combine,
      Complex.ofReal_re,Complex.ofReal_im,zero_smul,add_zero]

private theorem combineInput_tendsto (T : ℝ≥0) (a b : ℕ → Input T) (u v : Input T)
    (ha : Tendsto a atTop (𝓝 u)) (hb : Tendsto b atTop (𝓝 v)) :
    Tendsto (fun N => combineInput T (a N) (b N)) atTop (𝓝 (combineInput T u v)) := by
  apply tendsto_subtype_rng.mpr
  have har := (continuous_subtype_val.tendsto u).comp ha
  have hbr := (continuous_subtype_val.tendsto v).comp hb
  change Tendsto (fun N => ofReal (nativeMeasure T) (a N).val+
      Complex.I • ofReal (nativeMeasure T) (b N).val) atTop
    (𝓝 (ofReal (nativeMeasure T) u.val+Complex.I • ofReal (nativeMeasure T) v.val))
  exact (((ofReal (nativeMeasure T)).continuous.tendsto _).comp har).add
    (tendsto_const_nhds.smul (((ofReal (nativeMeasure T)).continuous.tendsto _).comp hbr))

theorem normalizedSteps_tendsto (T : ℝ≥0) :
    Tendsto (normalizedSteps T) atTop (𝓝 (normalizedInput T)) :=
  tendsto_const_nhds.smul (combineInput_tendsto T _ _ _ _
    (componentInput_tendsto T false) (componentInput_tendsto T true))

/-- Actual existing stochastic integrals converge in the original source L2. -/
theorem normalized_integrals_tendsto (T : ℝ≥0) :
    Tendsto (fun N => channel T false (normalizedSteps T N)) atTop
      (𝓝 (channel T false (normalizedInput T))) :=
  ((channel T false).continuous.tendsto _).comp (normalizedSteps_tendsto T)

theorem componentInput_energy (T : ℝ≥0) :
    ‖componentInput T false‖^2+‖componentInput T true‖^2=
      ∫ r,Real.exp (2*(r.toNNReal:ℝ)) ∂timeLaw T := by
  have hn (b : Bool) : ‖componentInput T b‖^2=
      ‖running (component b) (component_continuous b) T‖^2 := by
    rw [← componentInput_sections,(timeSections T).norm_map,(fieldEmbedding T).norm_map]
  rw [hn false,hn true,BochnerL2Dominated.norm_sq_integral,
    BochnerL2Dominated.norm_sq_integral]
  rw [← integral_add ((Lp.memLp (running (component false) (component_continuous false) T)).norm.integrable_sq)
    ((Lp.memLp (running (component true) (component_continuous true) T)).norm.integrable_sq)]
  apply integral_congr_ae
  filter_upwards [running_ae (component false) (component_continuous false) T,
    running_ae (component true) (component_continuous true) T] with r hr hi
  rw [hr,hi]
  change ‖realPart (gaussianProduct.prod gaussianProduct) (observable r.toNNReal)‖^2+
    ‖imagPart (gaussianProduct.prod gaussianProduct) (observable r.toNNReal)‖^2=_
  rw [← norm_sq_parts,observable_energy]

private theorem exponential_time_integral (T : ℝ≥0) :
    (∫ r,Real.exp (2*(r.toNNReal:ℝ)) ∂timeLaw T)=(Real.exp (2*(T:ℝ))-1)/2 := by
  have he : (∫ r,Real.exp (2*(r.toNNReal:ℝ)) ∂timeLaw T)=
      ∫ r in (0:ℝ)..(T:ℝ),Real.exp (2*r) := by
    rw [intervalIntegral.integral_of_le T.coe_nonneg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [Real.coe_toNNReal _ hr.1.le]
  rw [he]
  have hd (r : ℝ) : HasDerivAt (fun x : ℝ => Real.exp (2*x)/2) (Real.exp (2*r)) r := by
    have hl : HasDerivAt (fun x : ℝ => 2*x) 2 r := by
      convert (hasDerivAt_id r).const_mul (2:ℝ) using 1 <;> simp only [id_eq,mul_one]
    have hx := ((Real.hasDerivAt_exp (2*r)).comp r hl).div_const 2
    simpa only [Function.comp_def,mul_div_cancel_right₀ _ (by norm_num : (2:ℝ)≠0)] using hx
  have hc : Continuous (fun r : ℝ => Real.exp (2*r)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
    (hc.intervalIntegrable _ _)]
  simp only [mul_zero,Real.exp_zero]
  ring

/-- Exact physical input energy, with the normalized-channel factor retained.
This does not identify the integral's terminal value. -/
theorem normalizedInput_energy (T : ℝ≥0) :
    ‖normalizedInput T‖^2=Real.exp (2*(T:ℝ))-1 := by
  rw [input_norm_sq,(normalizedInput_parts T).1,(normalizedInput_parts T).2,
    norm_smul,norm_smul,mul_pow,mul_pow,Real.norm_eq_abs,sq_abs,
    Real.sq_sqrt (by norm_num : (0:ℝ)≤2),← mul_add,componentInput_energy,
    exponential_time_integral]
  ring

end OperatorDerivativeRewrite.Foundation.StochasticCauchyExponentialInput
