import Foundation.IBMClockAverageCandidate
import Foundation.IBMUnmollifiedSourceDerivative
import Foundation.IBMConditionalObservable
import Foundation.ProductL2Flip
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Genuine scalar IBM time averages in source/clock L2. Clock derivative
membership is not inferred from the independently constructed candidate. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace OperatorDerivativeRewrite.Foundation.IBMTimeAveragedObservable
open InfiniteGaussian IBMRandomTimeHilbert IBMContinuousScenery IBMMollifier
open GaussianTimeProcess IBMClockOverlapEnergy
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
attribute [local irreducible] IBMConstructedSources.clockPath
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

abbrev ValueSpace := Lp GaussianL2 2 gaussianProduct

theorem mollified_hasDerivAt (n : ℕ) (r : ℝ) :
    HasDerivAt (wholeLineScenery (kernel n)) (IBMClockAverageCandidate.sourceColumn n r) r := by
  have he : IBMClockAverageCandidate.sourceColumn n r = wholeLineScenery (deriv (kernel n)) r := by
    rw [IBMJointMollifierGaussian.wholeLineScenery_eq_sourceEmbedding]
    rfl
  rw [he]
  exact wholeLineScenery_hasDerivAt (kernel_compactSupport n)
    ((kernel_smooth n).of_le (by norm_num)) r

theorem mollified_lipschitz (n : ℕ) :
    ∃ K : ℝ≥0, LipschitzWith K (wholeLineScenery (kernel n)) := by
  obtain ⟨C, hC, hb⟩ := IBMClockAverageCandidate.sourceColumn_bounded n
  refine ⟨⟨C, hC⟩, lipschitzWith_of_nnnorm_deriv_le
    (fun r => (mollified_hasDerivAt n r).differentiableAt) ?_⟩
  intro r
  rw [(mollified_hasDerivAt n r).deriv]
  exact_mod_cast hb r

theorem mollified_time_continuous (n : ℕ) : Continuous (randomMollifiedL2 n) := by
  obtain ⟨K, hK⟩ := mollified_lipschitz n
  let φ : ℝ → GaussianL2 := fun x => wholeLineScenery (kernel n) |x|
  have ha : LipschitzWith 1 (fun x : ℝ => |x|) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using abs_abs_sub_abs_le_abs_sub x y
  have hφ : LipschitzWith K φ := by simpa only [φ, Function.comp_def, mul_one] using hK.comp ha
  let ψ : ℝ → GaussianL2 := fun x => φ x - φ 0
  have hψ : LipschitzWith K ψ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [ψ, dist_eq_norm, sub_sub_sub_cancel_right] using hφ.dist_le_mul x y
  have hz : ψ 0 = 0 := sub_self _
  let G : GaussianL2 → ValueSpace := fun A => hψ.compLp hz A + Lp.const 2 gaussianProduct (φ 0)
  have hG : Continuous G := (hψ.continuous_compLp hz).add continuous_const
  have he (t : ℝ≥0) : G (wienerL2 t) = randomMollifiedL2 n t := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (hψ.compLp hz (wienerL2 t)) (Lp.const 2 gaussianProduct (φ 0)),
      hψ.coeFn_compLp hz (wienerL2 t), Lp.coeFn_const (p := 2) (μ := gaussianProduct) (c := φ 0),
      (randomMollifiedClass_memLp n t).coeFn_toLp] with ω hadd hc hconst hm
    change G (wienerL2 t) ω = randomMollifiedL2 n t ω
    rw [hadd, Pi.add_apply, hc, hconst]
    change (φ (process t ω) - φ 0) + φ 0 = randomMollifiedL2 n t ω
    rw [sub_add_cancel]
    exact hm.symm
  have hf : (fun t => G (wienerL2 t)) = randomMollifiedL2 n := funext he
  rw [← hf]
  exact hG.comp GaussianLipschitzIntegrands.wienerL2_continuous

theorem source_uniform_limit :
    TendstoUniformly randomMollifiedL2 randomSourceL2 atTop := by
  have hr : Tendsto (fun n : ℕ => Real.sqrt (bump n).rOut) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp bump_outer_tendsto_zero
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [hr.eventually (eventually_lt_nhds hε)] with n hn t
  have he := randomMollifiedL2_error_le n t
  simpa only [dist_eq_norm, norm_sub_rev] using he.trans_lt hn

theorem source_time_continuous : Continuous randomSourceL2 :=
  source_uniform_limit.continuous (Eventually.of_forall mollified_time_continuous).frequently

theorem mollified_time_integrable (n : ℕ) (T : ℝ) :
    Integrable (fun t : ℝ => randomMollifiedL2 n t.toNNReal) (window T) :=
  ((mollified_time_continuous n).comp continuous_real_toNNReal).integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem source_time_integrable (T : ℝ) :
    Integrable (fun t : ℝ => randomSourceL2 t.toNNReal) (window T) :=
  (source_time_continuous.comp continuous_real_toNNReal).integrableOn_Icc.mono_set Ioc_subset_Icc_self

def mollifiedAverage (n : ℕ) (T : ℝ) : ValueSpace :=
  ∫ t, randomMollifiedL2 n t.toNNReal ∂window T

def sourceAverage (T : ℝ) : ValueSpace := ∫ t, randomSourceL2 t.toNNReal ∂window T

/-- Actual strong L2 error after time integration, with no derivative-domain premise. -/
theorem average_error (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ‖mollifiedAverage n T - sourceAverage T‖ ≤ T * Real.sqrt (bump n).rOut := by
  rw [mollifiedAverage, sourceAverage, ← integral_sub (mollified_time_integrable n T) (source_time_integrable T)]
  have h := norm_integral_le_of_norm_le_const
    (ae_of_all (window T) fun t : ℝ => randomMollifiedL2_error_le n t.toNNReal)
  simpa [window, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal hT, mul_comm] using h

theorem average_tendsto {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun n => mollifiedAverage n T) atTop (𝓝 (sourceAverage T)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr : Tendsto (fun n : ℕ => T * Real.sqrt (bump n).rOut) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero, mul_zero] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp bump_outer_tendsto_zero).const_mul T
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => average_error n hT) hr

abbrev JointL2 := Lp ℝ 2 IBMSourceLaws.jointMeasure

/-- Restore the native (source,clock) order through the actual product isometry. -/
def jointRealization : ValueSpace →ₗᵢ[ℝ] JointL2 :=
  (ProductL2Curry.swap gaussianProduct gaussianProduct).comp
    (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm.toLinearIsometry

theorem jointRealization_ae_of_sections (u : ValueSpace)
    (f : IBMSourceLaws.JointSample → ℝ) (hm : Measurable f)
    (hf : ∀ᵐ ωY ∂gaussianProduct, u ωY =ᵐ[gaussianProduct] fun ωX => f (ωX,ωY)) :
    jointRealization u =ᵐ[IBMSourceLaws.jointMeasure] f := by
  let v := (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm u
  have hp : v =ᵐ[gaussianProduct.prod gaussianProduct] fun p => f (p.2,p.1) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (Lp.stronglyMeasurable v).measurable
      (hm.comp measurable_swap))).mpr
    filter_upwards [ProductL2Curry.curryEquiv_symm_coeFn gaussianProduct gaussianProduct u, hf]
      with ωY hc ha
    exact hc.symm.trans ha
  have hswap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp hp
  filter_upwards [ProductL2Curry.swap_coeFn gaussianProduct gaussianProduct v, hswap] with p hs ht
  exact hs.trans ht

theorem joint_point_actual_ae (t : ℝ≥0) :
    jointRealization (randomSourceL2 t) =ᵐ[IBMSourceLaws.jointMeasure] IBMConstructedSources.ibmValue t := by
  apply jointRealization_ae_of_sections _ _
    (IBMConstructedSources.ibmValue_jointly_measurable.comp (measurable_const.prodMk measurable_id))
  filter_upwards [(randomSourceClass_memLp t).coeFn_toLp,
    IBMUnmollifiedSourceDerivative.actual_section_ae t] with ωY hu ha
  change randomSourceL2 t ωY = randomSourceClass t ωY at hu
  rw [hu]
  exact ha.symm

abbrev IntrinsicSpace := IBMConditionalObservable.observableSpace
  IBMConstructedSources.sceneryPath IBMConstructedSources.clockPath

local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable IBMConstructedSources.clockPath_measurable).completeSpace_coe

theorem joint_point_intrinsic (t : ℝ≥0) : jointRealization (randomSourceL2 t) ∈ IntrinsicSpace := by
  have hm : Measurable[IBMConditionalObservable.observableSigma
      IBMConstructedSources.sceneryPath IBMConstructedSources.clockPath] (IBMConstructedSources.ibmValue t) :=
    (measurable_pi_apply t).comp (comap_measurable (fun ω s => IBMConstructedSources.ibmValue s ω))
  exact ⟨IBMConstructedSources.ibmValue t, hm.stronglyMeasurable, joint_point_actual_ae t⟩

def intrinsicCurve (t : ℝ≥0) : IntrinsicSpace :=
  ⟨jointRealization (randomSourceL2 t), joint_point_intrinsic t⟩

theorem intrinsicCurve_continuous : Continuous intrinsicCurve :=
  (jointRealization.continuous.comp source_time_continuous).subtype_mk _

theorem intrinsicCurve_integrable (T : ℝ) :
    Integrable (fun t : ℝ => intrinsicCurve t.toNNReal) (window T) :=
  (intrinsicCurve_continuous.comp continuous_real_toNNReal).integrableOn_Icc.mono_set Ioc_subset_Icc_self

def intrinsicAverage (T : ℝ) : IntrinsicSpace := ∫ t, intrinsicCurve t.toNNReal ∂window T

def nativeAverage (T : ℝ) : JointL2 := jointRealization (sourceAverage T)

theorem nativeAverage_eq_intrinsicAverage (T : ℝ) :
    nativeAverage T = (intrinsicAverage T : JointL2) := by
  change jointRealization.toContinuousLinearMap
    (∫ t : ℝ, randomSourceL2 t.toNNReal ∂window T) =
      IntrinsicSpace.subtypeL (∫ t : ℝ, intrinsicCurve t.toNNReal ∂window T)
  rw [← jointRealization.toContinuousLinearMap.integral_comp_comm (source_time_integrable T),
    ← IntrinsicSpace.subtypeL.integral_comp_comm (intrinsicCurve_integrable T)]
  rfl

/-- The time average is intrinsically IBM-observable, independently of its
still-unproved clock derivative graph. -/
theorem nativeAverage_intrinsic (T : ℝ) : nativeAverage T ∈ IntrinsicSpace := by
  rw [nativeAverage_eq_intrinsicAverage]
  exact (intrinsicAverage T).property

theorem nativeAverage_tendsto {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun n => jointRealization (mollifiedAverage n T)) atTop (𝓝 (nativeAverage T)) :=
  jointRealization.continuous.continuousAt.tendsto.comp (average_tendsto hT)

theorem nativeAverage_error (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ‖jointRealization (mollifiedAverage n T) - nativeAverage T‖ ≤ T * Real.sqrt (bump n).rOut := by
  rw [nativeAverage, ← map_sub, jointRealization.norm_map]
  exact average_error n hT

def sourceProjection : ValueSpace →L[ℝ] ValueSpace :=
  GaussianPastFirstChaos.projection.compLpL 2 gaussianProduct

def sourceGradient : ValueSpace →L[ℝ] Lp GaussianVectorL2 2 gaussianProduct :=
  GaussianBrownianSobolevField.firstChaosGradient.compLpL 2 gaussianProduct

theorem projection_embedding (h : CoefficientSpace) :
    GaussianPastFirstChaos.projection (firstChaosEmbedding h) = firstChaosEmbedding h := by
  change firstChaosEmbedding (firstChaosEmbedding.toContinuousLinearMap.adjoint (firstChaosEmbedding h)) = _
  rw [IBMQuarticSecondPrimitive.adjoint_embedding]

theorem sourceProjection_point (t : ℝ≥0) : sourceProjection (randomSourceL2 t) = randomSourceL2 t := by
  apply Lp.ext
  filter_upwards [GaussianPastFirstChaos.projection.coeFn_compLpL (randomSourceL2 t),
    (randomSourceClass_memLp t).coeFn_toLp] with ω hp hu
  change randomSourceL2 t ω = randomSourceClass t ω at hu
  change sourceProjection (randomSourceL2 t) ω = GaussianPastFirstChaos.projection (randomSourceL2 t ω) at hp
  rw [hp, hu]
  exact projection_embedding _

theorem sourceProjection_mollified_point (n : ℕ) (t : ℝ≥0) :
    sourceProjection (randomMollifiedL2 n t) = randomMollifiedL2 n t := by
  apply Lp.ext
  filter_upwards [GaussianPastFirstChaos.projection.coeFn_compLpL (randomMollifiedL2 n t),
    (randomMollifiedClass_memLp n t).coeFn_toLp] with ω hp hu
  change randomMollifiedL2 n t ω = randomMollifiedClass n t ω at hu
  change sourceProjection (randomMollifiedL2 n t) ω =
    GaussianPastFirstChaos.projection (randomMollifiedL2 n t ω) at hp
  rw [hp, hu]
  change GaussianPastFirstChaos.projection (wholeLineScenery (kernel n) |process t ω|) = _
  have he := IBMOriginalBoundaryResidual.triple_embedding n |process t ω| 0
  simp only [IBMJointMollifierGaussian.derivativeKernel, ↓reduceIte] at he
  rw [← he]
  change GaussianPastFirstChaos.projection (firstChaosEmbedding _) =
    wholeLineScenery (kernel n) |process t ω|
  rw [projection_embedding, he]

theorem projected_source_graph (u : ValueSpace) :
    (sourceProjection u, sourceGradient u) ∈
      (BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative).graph := by
  rw [BochnerClosedOperator.mem_lift_graph_iff]
  filter_upwards [GaussianPastFirstChaos.projection.coeFn_compLpL u,
    GaussianBrownianSobolevField.firstChaosGradient.coeFn_compLpL u] with ω hp hg
  change sourceProjection u ω = GaussianPastFirstChaos.projection (u ω) at hp
  change sourceGradient u ω = GaussianBrownianSobolevField.firstChaosGradient (u ω) at hg
  rw [hp, hg]
  exact GaussianPastFirstChaos.projection_closedDerivative_graph _

theorem sourceAverage_source_graph (T : ℝ) :
    (sourceAverage T, sourceGradient (sourceAverage T)) ∈
      (BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative).graph := by
  have hp : sourceProjection (sourceAverage T) = sourceAverage T := by
    unfold sourceAverage
    rw [← sourceProjection.integral_comp_comm (source_time_integrable T)]
    exact integral_congr_ae (ae_of_all _ fun t => sourceProjection_point t.toNNReal)
  simpa only [hp] using projected_source_graph (sourceAverage T)

theorem mollifiedAverage_source_graph (n : ℕ) (T : ℝ) :
    (mollifiedAverage n T, sourceGradient (mollifiedAverage n T)) ∈
      (BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative).graph := by
  have hp : sourceProjection (mollifiedAverage n T) = mollifiedAverage n T := by
    unfold mollifiedAverage
    rw [← sourceProjection.integral_comp_comm (mollified_time_integrable n T)]
    exact integral_congr_ae (ae_of_all _ fun t => sourceProjection_mollified_point n t.toNNReal)
  simpa only [hp] using projected_source_graph (mollifiedAverage n T)

theorem source_graph_tendsto {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun n => (mollifiedAverage n T, sourceGradient (mollifiedAverage n T))) atTop
      (𝓝 (sourceAverage T, sourceGradient (sourceAverage T))) :=
  (average_tendsto hT).prodMk_nhds (sourceGradient.continuous.continuousAt.tendsto.comp (average_tendsto hT))

theorem sourceAverage_eq_interval {T : ℝ} (hT : 0 ≤ T) :
    sourceAverage T = ∫ t in (0 : ℝ)..T, randomSourceL2 t.toNNReal := by
  rw [intervalIntegral.integral_of_le hT]
  rfl

/-- Ordinary time differentiation in L2 recovers each positive-time coordinate.
This is not a claim about the clock Malliavin derivative. -/
theorem sourceAverage_hasDerivAt {T : ℝ} (hT : 0 < T) :
    HasDerivAt sourceAverage (randomSourceL2 T.toNNReal) T := by
  have hc := source_time_continuous.comp continuous_real_toNNReal
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable (0 : ℝ) T) hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hT] with x hx
  exact sourceAverage_eq_interval hx.le

theorem nativeAverage_hasDerivAt {T : ℝ} (hT : 0 < T) :
    HasDerivAt nativeAverage (jointRealization (randomSourceL2 T.toNNReal)) T :=
  jointRealization.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt T (sourceAverage_hasDerivAt hT)

end OperatorDerivativeRewrite.Foundation.IBMTimeAveragedObservable
