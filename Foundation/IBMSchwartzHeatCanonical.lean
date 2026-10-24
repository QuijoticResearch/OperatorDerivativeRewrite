import Foundation.IBMSchwartzHeatTimePairing
import Foundation.GaussianPredictableStepExt
import Foundation.GaussianFiniteHorizonAdjoint

/-! The explicit nonlinear heat-score field is the ORIGINAL scalar predictable
adjoint for every bounded source functional, proved by actual step duality. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzHeatCanonical
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProductL2 GaussianTimeProcess
open GaussianPredictableFull GaussianPredictableAdjoint GaussianPredictableCutoff
open GaussianConditionalIto GaussianFiniteHorizonAdjoint
open IBMSchwartzHalfHolderHeat IBMSchwartzHeatPredictable IBMSchwartzHeatTimePairing
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe
attribute [local irreducible] curve heatScore GaussianHalfHolderScore.score

def terminal (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) (L : GaussianL2 →L[ℝ] ℝ) : GaussianL2 :=
  L.compLpL 2 gaussianProduct (IBMSchwartzPhysicalPrimitiveClock.endpointLimit g a T)

theorem terminal_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) (L : GaussianL2 →L[ℝ] ℝ) :
    terminal g a T L =ᵐ[gaussianProduct] fun Y => L (curve g a (process T Y)) := by
  filter_upwards [L.coeFn_compLpL (IBMSchwartzPhysicalPrimitiveClock.endpointLimit g a T),
    IBMSchwartzPhysicalPrimitiveClock.endpointLimit_ae g a T,
    IBMConstructedSources.clockPath_coordinate_ae T] with Y hL he hc
  change L.compLpL 2 gaussianProduct _ Y = _
  rw [hL,he,hc]
  simp only [curve]

theorem terminal_past (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) (L : GaussianL2 →L[ℝ] ℝ) :
    terminal g a T L ∈ pastL2 T := by
  exact ((L.continuous.comp (curve_continuous g a)).stronglyMeasurable.comp_measurable
    (process_stronglyAdapted T).measurable).aestronglyMeasurable.congr (terminal_ae g a T L).symm

def finite (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) (L : GaussianL2 →L[ℝ] ℝ) :
    GaussianPredictableHorizon.PredictableDomain T :=
  ⟨L.compLpL 2 (BrownianClockWeightedEnergy.base T) (input g a T).val,
    (L.continuous.comp_aestronglyMeasurable (input g a T).property).congr
      (L.coeFn_compLpL (input g a T).val).symm⟩

theorem finite_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) (L : GaussianL2 →L[ℝ] ℝ) :
    (finite g a T L).val =ᵐ[BrownianClockWeightedEnergy.base T] fun z => L (raw g a T z) := by
  filter_upwards [L.coeFn_compLpL (input g a T).val,input_ae g a T] with z hL hi
  change L.compLpL 2 (BrownianClockWeightedEnergy.base T) _ z = _
  rw [hL,hi]

def full (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) (L : GaussianL2 →L[ℝ] ℝ) : fullPredictable :=
  extendPredictable T (finite g a T L)

theorem full_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) (L : GaussianL2 →L[ℝ] ℝ) :
    (full g a T L : TimeProbabilityL2) =ᵐ[timeProbability]
      (PredictableRealL2.horizon T).indicator (fun z => L (raw g a T z)) := by
  have hf := (ae_eq_restrict_iff_indicator_ae_eq
    (PredictableRealL2.horizon_measurable T)).mp (finite_ae g a T L)
  exact (L2ZeroExtension_coeFn (PredictableRealL2.horizon_measurable T)
    (finite g a T L).val).trans hf

theorem full_supported (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) (L : GaussianL2 →L[ℝ] ℝ) :
    predictableCut T (full g a T L) = full g a T L := cut_extended T _

attribute [local irreducible] terminal full finite

private theorem terminal_product_integrable (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (S R T : ℝ≥0) (V : GaussianL2) :
    Integrable (fun Y => (V Y*(process R Y-process S Y)) • curve g a (process T Y))
      gaussianProduct := by
  have hp : Integrable (fun Y => V Y*(process R Y-process S Y)) gaussianProduct :=
    (Lp.memLp V).integrable_mul (IBMSchwartzConditionalIncrement.increment_memLp S R)
  apply (hp.norm.mul_const (SchwartzMap.seminorm ℝ 0 0 g)).mono'
    (hp.aestronglyMeasurable.smul
      (((curve_continuous g a).stronglyMeasurable.comp_measurable
        (process_stronglyMeasurable T).measurable).aestronglyMeasurable))
  exact Filter.Eventually.of_forall fun Y => by
    change ‖(V Y*(process R Y-process S Y)) • curve g a (process T Y)‖ ≤ _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (curve_bound g a _) (norm_nonneg _)

theorem inner_step (g : SchwartzMap ℝ ℝ) (a : ℝ) (S R T : ℝ≥0)
    (hSR : S ≤ R) (hRT : R ≤ T) (L : GaussianL2 →L[ℝ] ℝ) (V : GaussianL2)
    (hV : AEStronglyMeasurable[naturalFiltration S] V gaussianProduct) :
    inner ℝ (full g a T L : TimeProbabilityL2) (productTensor (intervalVector S R) V) =
      inner ℝ (terminal g a T L)
        (itoIntegral ⟨productTensor (intervalVector S R) V,
          past_step_mem_fullPredictable S R V hV⟩) := by
  rw [L2_inner_eq_integral]
  have ht := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
    (ν := gaussianProduct)).ae_eq_comp (intervalVector_coeFn S R)
  have he : (fun z : ℝ × SampleSpace => inner ℝ
      ((full g a T L : TimeProbabilityL2) z) (productTensor (intervalVector S R) V z))
      =ᵐ[timeProbability] (Ioc (S : ℝ) R ×ˢ (univ : Set SampleSpace)).indicator
        (fun z => L (V z.2 • raw g a T z)) := by
    filter_upwards [full_ae g a T L,productTensor_coeFn (intervalVector S R) V,ht]
      with z hf hp ht
    simp only [Function.comp_def] at ht
    rw [hf,hp,ht,Real.inner_apply]
    by_cases hz : z.1 ∈ Ioc (S : ℝ) R
    · have hT : z ∈ PredictableRealL2.horizon T :=
        ⟨⟨lt_of_le_of_lt S.coe_nonneg hz.1,hz.2.trans (show (R : ℝ) ≤ T from hRT)⟩,mem_univ _⟩
      simp only [indicator_of_mem hz,indicator_of_mem hT,one_mul,
        indicator_of_mem (show z ∈ Ioc (S : ℝ) R ×ˢ (univ : Set SampleSpace) from ⟨hz,mem_univ _⟩),
        map_smul,smul_eq_mul]
      exact mul_comm _ _
    · simp [hz]
  rw [integral_congr_ae he,integral_indicator (measurableSet_Ioc.prod MeasurableSet.univ),
    ← Measure.restrict_prod_eq_prod_univ]
  rw [L.integral_comp_comm (step_integrable g a S R T hRT V),
    step_duality g a S R T hSR hRT V hV,
    ← L.integral_comp_comm (terminal_product_integrable g a S R T V),L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [terminal_ae g a T L,itoIntegral_past_step S R hSR V hV] with Y hf hi
  rw [hf,hi,Real.inner_apply,map_smul,smul_eq_mul]
  exact mul_comm _ _

theorem full_eq_adjoint (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0)
    (L : GaussianL2 →L[ℝ] ℝ) : full g a T L = predictableAdjoint (terminal g a T L) := by
  apply GaussianPredictableStepExt.ext
  intro S R hSR V hV
  change AEStronglyMeasurable[naturalFiltration S] V gaussianProduct at hV
  have hf : cut T (full g a T L : TimeProbabilityL2) = (full g a T L : TimeProbabilityL2) :=
    congrArg Subtype.val (full_supported g a T L)
  have hp : cut T (predictableAdjoint (terminal g a T L) : TimeProbabilityL2) =
      (predictableAdjoint (terminal g a T L) : TimeProbabilityL2) :=
    congrArg Subtype.val
      (GaussianConditionalClarkOcone.past_representer_supported T _ (terminal_past g a T L))
  calc
    _ = inner ℝ (full g a T L : TimeProbabilityL2)
        (cut T (productTensor (intervalVector S R) V)) := by rw [← cut_inner,hf]
    _ = inner ℝ (predictableAdjoint (terminal g a T L) : TimeProbabilityL2)
        (cut T (productTensor (intervalVector S R) V)) := by
      rw [cut_tensor,← NNReal.coe_min]
      by_cases hS : S ≤ T
      · rw [inner_step g a S (min R T) T (le_min hSR hS) (min_le_right _ _) L V hV]
        let w : fullPredictable := ⟨productTensor (intervalVector S (min R T)) V,
          past_step_mem_fullPredictable S (min R T) V hV⟩
        change _ = inner ℝ (predictableAdjoint (terminal g a T L)) w
        exact (ContinuousLinearMap.adjoint_inner_left
          itoIntegral.toContinuousLinearMap w (terminal g a T L)).symm
      · have hz := tensor_eq_zero_of_le S (min R T)
          ((min_le_right R T).trans (le_of_not_ge hS)) V
        rw [hz,inner_zero_right,inner_zero_right]
    _ = _ := by rw [← cut_inner,hp]

end OperatorDerivativeRewrite.Foundation.IBMSchwartzHeatCanonical
