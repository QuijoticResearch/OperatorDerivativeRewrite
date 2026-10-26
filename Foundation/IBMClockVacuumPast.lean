import Foundation.IBMClockNativeSmoothing
import Foundation.IBMJointForecastGerm
import Foundation.IBMRawIntegralSourceCalculus
import Foundation.IBMGlobalVacuum
import Foundation.IBMClockGaussianTail
import Foundation.IBMRawTemporalKernel
/-! Localization of the ACTUAL reflected-clock IBM past and a clock-vacuum
adaptedness obstruction. Native Gaussian differentiability does not imply
membership in the completed right-germ IBM past. This does not decide full
all-time intrinsic observability or finite-strength Bessel past preservation. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMLocalPastRestriction
open InfiniteGaussian IBMConstructedSources IBMTimeAveragedObservable
open IBMNaturalFiltrationObstruction IBMIntrinsicOperators IBMClippedSceneryForecast
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def confined (δ T : ℝ≥0) : Set SampleSpace := {Y | ∀ r ≤ T, |clockPath Y r| ≤ (δ:ℝ)}

theorem confined_measurable (δ T : ℝ≥0) : MeasurableSet (confined δ T) := by
  have hc : IsClosed {p : C(ℝ≥0,ℝ) | ∀ r ≤ T, |p r| ≤ (δ:ℝ)} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro r
    apply isClosed_iInter
    intro hr
    exact isClosed_le (by fun_prop) continuous_const
  exact hc.measurableSet.preimage clockPath_measurable

private theorem past_factor (T : ℝ≥0) (F : JointL2) (hF : F ∈ past T) :
    ∃ g : (Iic T → ℝ) → ℝ, Measurable g ∧
      GaussianPredictableStep.pastCoefficient ibmValue T g =ᵐ[IBMSourceLaws.jointMeasure] F := by
  change AEStronglyMeasurable[naturalFiltration T] F IBMSourceLaws.jointMeasure at hF
  obtain ⟨g,hg,he⟩ := (GaussianPredictableStep.measurable_natural_iff_exists_pastCoefficient
    (fun t => (point_stronglyMeasurable t).measurable) T (hF.mk F)).1
      hF.stronglyMeasurable_mk.measurable
  exact ⟨g,hg,(hF.ae_eq_mk.trans (EventuallyEq.of_eq he)).symm⟩

theorem past_sections_confined (δ T : ℝ≥0) (F : JointL2) (hF : F ∈ past T) :
    ∀ᵐ Y ∂gaussianProduct, Y ∈ confined δ T →
      AEStronglyMeasurable[IBMSpatialSceneryForecast.history δ] (sourceUnitary F Y) gaussianProduct := by
  obtain ⟨g,hg,hfa⟩ := past_factor T F hF
  have ha := ae_ae_of_ae_prod
    (measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp hfa)
  filter_upwards [IBMJointForecastGerm.source_sections F,ha] with Y hs hfa
  intro hY
  apply (past_functional_spatial_measurable δ T g hg Y).aestronglyMeasurable.congr
  filter_upwards [hs,hfa] with X hX hfX
  have he : GaussianPredictableStep.pastCoefficient (actualValue δ) T g (X,Y) =
      GaussianPredictableStep.pastCoefficient ibmValue T g (X,Y) :=
    congrArg g (funext fun r => actual_past_eq δ T (X,Y) hY r r.property)
  exact he.trans (hfX.trans hX.symm)

theorem exists_positive_confined_time (δ : ℝ≥0) (hδ : 0 < δ) :
    ∃ T : ℝ≥0, 0 < T ∧ gaussianProduct (confined δ T) ≠ 0 := by
  let τ := IBMIntrinsicRightApproach.approach 0
  have ht := IBMClockGermLocalization.clock_uniformly_small δ hδ τ
    (IBMIntrinsicRightApproach.approach_tendsto 0)
  obtain ⟨X,hX⟩ := (ae_ae_of_ae_prod ht).exists
  have hc : ∀ᵐ Y ∂gaussianProduct, ∀ᶠ n in atTop, Y ∈ confined δ (τ n) := hX
  have hex : ∃ n, gaussianProduct (confined δ (τ n)) ≠ 0 := by
    by_contra hn
    push Not at hn
    have ha : ∀ᵐ Y ∂gaussianProduct, ∀ n, Y ∉ confined δ (τ n) :=
      ae_all_iff.mpr (fun n => by
        rw [ae_iff]
        simpa only [not_not,Set.ofPred_mem_eq] using hn n)
    obtain ⟨Y,hy,hnY⟩ := (hc.and ha).exists
    obtain ⟨n,hn⟩ := hy.exists
    exact hnY n hn
  obtain ⟨n,hn⟩ := hex
  exact ⟨τ n,IBMIntrinsicRightApproach.approach_positive 0 n,hn⟩

theorem source_only_past_requires_history (δ T : ℝ≥0) (K : GaussianL2)
    (hp : jointRealization (Lp.const 2 gaussianProduct K) ∈ past T)
    (hE : gaussianProduct (confined δ T) ≠ 0) :
    AEStronglyMeasurable[IBMSpatialSceneryForecast.history δ] K gaussianProduct := by
  have hs := past_sections_confined δ T _ hp
  rw [IBMRawIntegralSourceCalculus.source_curry] at hs
  by_contra hK
  have ha : ∀ᵐ Y ∂gaussianProduct, Y ∉ confined δ T := by
    filter_upwards [hs,Lp.coeFn_const (p := 2) (μ := gaussianProduct) (c := K)] with Y hY hc
    intro hy
    apply hK
    simpa only [hc,Function.const_apply] using hY hy
  apply hE
  simpa only [not_not,Set.ofPred_mem_eq] using (ae_iff).1 ha

theorem future_scenery_not_history (δ r : ℝ≥0) (hδr : δ < r) :
    ¬ AEStronglyMeasurable[IBMSpatialSceneryForecast.history δ]
      (IBMContinuousScenery.sourceScenery r) gaussianProduct := by
  intro hs
  have hm := (IBMSceneryHistoryBridge.mem_generated_iff_path δ _).2 hs
  have hp := (GaussianConditionalGraph.generated (IBMSceneryGaussianGerm.history δ)).starProjection_eq_self_iff.2 hm
  change GaussianConditionalGraph.conditionalProjection (IBMSceneryGaussianGerm.history δ)
    (IBMContinuousScenery.sourceScenery r) = IBMContinuousScenery.sourceScenery r at hp
  rw [IBMSceneryHistoryBridge.projection_eq_condExpL2,IBMSpatialSceneryForecast.prediction_class,
    min_eq_right (show (δ:ℝ) ≤ r from hδr.le)] at hp
  have he := congrArg (fun v : GaussianL2 => ‖v‖^2) hp
  rw [IBMRandomTimeHilbert.sourceScenery_norm_sq,IBMRandomTimeHilbert.sourceScenery_norm_sq,
    abs_of_nonneg δ.coe_nonneg,abs_of_nonneg r.coe_nonneg] at he
  have hlt : (δ:ℝ) < r := hδr
  linarith

theorem future_scenery_not_past (δ r T : ℝ≥0) (hδr : δ < r)
    (hE : gaussianProduct (confined δ T) ≠ 0) :
    jointRealization (Lp.const 2 gaussianProduct (IBMContinuousScenery.sourceScenery r)) ∉ past T := by
  intro hp
  exact future_scenery_not_history δ r hδr (source_only_past_requires_history δ T _ hp hE)

theorem exists_actual_hidden_scenery : ∃ T : ℝ≥0, 0 < T ∧
    jointRealization (Lp.const 2 gaussianProduct (IBMContinuousScenery.sourceScenery 2)) ∉ past T := by
  obtain ⟨T,hT,hE⟩ := exists_positive_confined_time 1 (by norm_num)
  exact ⟨T,hT,future_scenery_not_past 1 2 T (by norm_num) hE⟩

end OperatorDerivativeRewrite.Foundation.IBMLocalPastRestriction

namespace OperatorDerivativeRewrite.Foundation.IBMClockVacuumPast
open InfiniteGaussian IBMTimeAveragedObservable GaussianClockValueOperators GaussianClockSpectralPowers
open IBMContinuousScenery IBMRandomTimeHilbert GaussianClockBochnerContraction IBMGlobalVacuum
open ProbabilityTheory
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

private theorem mean_flip (f : Field) :
    factorMean (ProductL2Curry.flip gaussianProduct gaussianProduct f) = contract gaussianOne f := by
  have h := contract_flip gaussianProduct (ProductL2Curry.flip gaussianProduct gaussianProduct f) gaussianOne
  rw [GaussianClockValueOperators.flip_involutive] at h
  exact h.symm

theorem clock_vacuum_const (f : Field) : project 0 f = Lp.const 2 gaussianProduct (contract gaussianOne f) := by
  change ProductL2Curry.flip gaussianProduct gaussianProduct
    ((GaussianNumberSectors.projection 0).compLpL 2 gaussianProduct
      (ProductL2Curry.flip gaussianProduct gaussianProduct f)) = _
  rw [factor_vacuum_tensor,ProductL2Curry.flip_tensor,mean_flip]
  apply Lp.ext
  filter_upwards [BochnerClosedOperator.tensor_coeFn gaussianProduct gaussianOne (contract gaussianOne f),
    gaussianOne_coeFn,Lp.coeFn_const (p := 2) (μ := gaussianProduct) (c := contract gaussianOne f)] with Y ht h1 hc
  simp only [ht,h1,hc,one_smul,Function.const_apply]

def vacuumSource (T : ℝ≥0) : GaussianL2 := contract gaussianOne (randomSourceL2 T)
def futureSource (δ : ℝ≥0) : GaussianL2 := sourceScenery ((δ:ℝ)+1)-sourceScenery δ
def overlap (δ : ℝ≥0) (x : ℝ) : ℝ := min |x| ((δ:ℝ)+1)-min |x| (δ:ℝ)

theorem overlap_bounds (δ : ℝ≥0) (x : ℝ) : 0 ≤ overlap δ x ∧ overlap δ x ≤ 1 := by
  unfold overlap
  by_cases hx : |x| ≤ (δ:ℝ)
  · rw [min_eq_left (by linarith : |x| ≤ (δ:ℝ)+1),min_eq_left hx]
    constructor <;> linarith
  · have hδx : (δ:ℝ) ≤ |x| := le_of_not_ge hx
    rw [min_eq_right hδx]
    by_cases hx1 : |x| ≤ (δ:ℝ)+1
    · rw [min_eq_left hx1]; constructor <;> linarith
    · rw [min_eq_right (le_of_not_ge hx1)]; constructor <;> linarith

theorem vacuumSource_pairing (δ T : ℝ≥0) :
    inner ℝ (futureSource δ) (vacuumSource T) =
      ∫ Y, overlap δ (GaussianTimeProcess.process T Y) ∂gaussianProduct := by
  rw [vacuumSource,contract_inner,L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [BochnerClosedOperator.tensor_coeFn gaussianProduct gaussianOne (futureSource δ),
    gaussianOne_coeFn,(randomSourceClass_memLp T).coeFn_toLp] with Y ht h1 hY
  change (randomSourceL2 T) Y = randomSourceClass T Y at hY
  rw [ht,h1,one_smul,hY]
  unfold randomSourceClass futureSource overlap
  rw [inner_sub_left,IBMRawTemporalKernel.source_inner (by positivity) (abs_nonneg _),
    IBMRawTemporalKernel.source_inner δ.coe_nonneg (abs_nonneg _)]
  simp only [min_comm]

theorem clock_tail_positive (T : ℝ≥0) (hT : 0 < T) (a : ℝ) :
    gaussianProduct {Y | a < GaussianTimeProcess.process T Y} ≠ 0 := by
  have hg : gaussianReal 0 T (Ioi a) ≠ 0 := by
    intro hz
    have hv := gaussianReal_absolutelyContinuous' 0 hT.ne' hz
    simp at hv
  have he : gaussianProduct {Y | a < GaussianTimeProcess.process T Y} = gaussianReal 0 T (Ioi a) := by
    rw [← (GaussianTimeProcess.process_hasLaw T).map_eq,
      Measure.map_apply (GaussianTimeProcess.process_stronglyMeasurable T).measurable measurableSet_Ioi]
    rfl
  exact he ▸ hg

theorem overlap_integrable (δ T : ℝ≥0) :
    Integrable (fun Y => overlap δ (GaussianTimeProcess.process T Y)) gaussianProduct := by
  have hm : Measurable (fun Y => overlap δ (GaussianTimeProcess.process T Y)) := by
    exact ((continuous_abs.measurable.comp (GaussianTimeProcess.process_stronglyMeasurable T).measurable).min measurable_const).sub ((continuous_abs.measurable.comp (GaussianTimeProcess.process_stronglyMeasurable T).measurable).min measurable_const)
  have hi : MemLp (fun Y => overlap δ (GaussianTimeProcess.process T Y)) 2 gaussianProduct :=
    MemLp.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun Y => by
      rw [Real.norm_eq_abs,abs_of_nonneg (overlap_bounds δ _).1]
      exact (overlap_bounds δ _).2)
  exact hi.integrable (by norm_num)

theorem vacuumSource_pairing_positive (δ T : ℝ≥0) (hT : 0 < T) :
    0 < inner ℝ (futureSource δ) (vacuumSource T) := by
  rw [vacuumSource_pairing]
  apply (integral_pos_iff_support_of_nonneg (fun Y => (overlap_bounds δ _).1) (overlap_integrable δ T)).2
  have hsub : {Y | (δ:ℝ)+1 < GaussianTimeProcess.process T Y} ⊆
      Function.support (fun Y => overlap δ (GaussianTimeProcess.process T Y)) := by
    intro Y hY
    have hh : (δ:ℝ)+1 ≤ |GaussianTimeProcess.process T Y| := hY.le.trans (le_abs_self _)
    change overlap δ (GaussianTimeProcess.process T Y) ≠ 0
    unfold overlap
    rw [min_eq_right hh,min_eq_right (by linarith : (δ:ℝ) ≤ |GaussianTimeProcess.process T Y|)]
    linarith
  apply lt_of_lt_of_le _ (measure_mono hsub)
  exact bot_lt_iff_ne_bot.mpr (clock_tail_positive T hT ((δ:ℝ)+1))

theorem futureSource_projection_zero (δ : ℝ≥0) :
    GaussianConditionalGraph.conditionalProjection (IBMSceneryGaussianGerm.history δ) (futureSource δ) = 0 := by
  have h1 : (condExpL2 ℝ ℝ (IBMSpatialSceneryForecast.history.le δ) (sourceScenery ((δ:ℝ)+1)) : GaussianL2) =
      sourceScenery δ := by
    simpa only [NNReal.coe_add,NNReal.coe_one,NNReal.coe_min,
      min_eq_right (by linarith : (δ:ℝ) ≤ (δ:ℝ)+1)] using IBMSpatialSceneryForecast.prediction_class δ (δ+1)
  have h0 : (condExpL2 ℝ ℝ (IBMSpatialSceneryForecast.history.le δ) (sourceScenery δ) : GaussianL2) =
      sourceScenery δ := by simpa only [min_self] using IBMSpatialSceneryForecast.prediction_class δ δ
  rw [futureSource,map_sub,IBMSceneryHistoryBridge.projection_eq_condExpL2,
    IBMSceneryHistoryBridge.projection_eq_condExpL2,h1,h0,sub_self]

theorem vacuumSource_not_history (δ T : ℝ≥0) (hT : 0 < T) :
    ¬ AEStronglyMeasurable[IBMSpatialSceneryForecast.history δ] (vacuumSource T) gaussianProduct := by
  intro hm
  have hs := (IBMSceneryHistoryBridge.mem_generated_iff_path δ _).2 hm
  have he := (GaussianConditionalGraph.generated (IBMSceneryGaussianGerm.history δ)).starProjection_eq_self_iff.2 hs
  change GaussianConditionalGraph.conditionalProjection (IBMSceneryGaussianGerm.history δ) (vacuumSource T) =
    vacuumSource T at he
  have hi := (GaussianConditionalGraph.generated (IBMSceneryGaussianGerm.history δ)).inner_starProjection_left_eq_right
    (futureSource δ) (vacuumSource T)
  change inner ℝ (GaussianConditionalGraph.conditionalProjection (IBMSceneryGaussianGerm.history δ) (futureSource δ))
      (vacuumSource T) = inner ℝ (futureSource δ)
      (GaussianConditionalGraph.conditionalProjection (IBMSceneryGaussianGerm.history δ) (vacuumSource T)) at hi
  rw [futureSource_projection_zero,he,inner_zero_left] at hi
  have hp := vacuumSource_pairing_positive δ T hT
  linarith

theorem actual_vacuum_not_past_at (δ T S : ℝ≥0) (hT : 0 < T)
    (hE : gaussianProduct (IBMLocalPastRestriction.confined δ S) ≠ 0) :
    jointRealization (project 0 (randomSourceL2 T)) ∉ IBMNaturalFiltrationObstruction.past S := by
  rw [clock_vacuum_const]
  intro hp
  exact vacuumSource_not_history δ T hT
    (IBMLocalPastRestriction.source_only_past_requires_history δ S (vacuumSource T) hp hE)

theorem exists_actual_past_projection_failure : ∃ T : ℝ≥0, 0 < T ∧
    jointRealization (project 0 (randomSourceL2 T)) ∉ IBMNaturalFiltrationObstruction.past T := by
  obtain ⟨T,hT,hE⟩ := IBMLocalPastRestriction.exists_positive_confined_time 1 (by norm_num)
  exact ⟨T,hT,actual_vacuum_not_past_at 1 T T hT hE⟩

theorem exists_actual_right_past_projection_failure : ∃ T : ℝ≥0, 0 < T ∧
    jointRealization (project 0 (randomSourceL2 T)) ∉ IBMIntrinsicRightGerm.rightPast T := by
  obtain ⟨S,hS,hE⟩ := IBMLocalPastRestriction.exists_positive_confined_time 1 (by norm_num)
  refine ⟨S/2,by positivity,?_⟩
  intro hp
  have hlt : S/2 < S := by exact div_lt_self hS (by norm_num)
  exact actual_vacuum_not_past_at 1 (S/2) S (by positivity) hE
    (IBMIntrinsicRightGerm.rightPast_le_past hlt hp)

theorem vacuum_in_native_clock_domain (f : Field) :
    jointRealization (project 0 f) ∈ IBMIntrinsicOperators.clockDerivative.domain := by
  apply (IBMClockNativeSmoothing.joint_clock_domain _).2
  exact project_mem_domain (fun n => ((n:ℝ)+1)^((1:ℝ)/2)) 0 f

theorem exists_actual_adapted_clock_projection_failure : ∃ T : ℝ≥0, 0 < T ∧
    jointRealization (randomSourceL2 T) ∈ IBMIntrinsicRightGerm.rightPast T ∧
    jointRealization (project 0 (randomSourceL2 T)) ∉ IBMIntrinsicRightGerm.rightPast T ∧
    jointRealization (project 0 (randomSourceL2 T)) ∈ IBMIntrinsicOperators.clockDerivative.domain := by
  obtain ⟨T,hT,hp⟩ := exists_actual_right_past_projection_failure
  refine ⟨T,hT,?_,hp,vacuum_in_native_clock_domain _⟩
  apply IBMIntrinsicRightGerm.past_le_rightPast T
  exact (IBMNaturalFiltrationObstruction.point_stronglyAdapted T).aestronglyMeasurable.congr
    (joint_point_actual_ae T).symm

end OperatorDerivativeRewrite.Foundation.IBMClockVacuumPast
