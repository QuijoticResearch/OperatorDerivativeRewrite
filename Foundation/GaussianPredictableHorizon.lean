import Foundation.PredictableRealL2
import Foundation.GaussianPastStepCompletion

/-! Full finite-horizon predictable L2 embeds in the OLD completed integral domain. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianPredictableHorizon
open InfiniteGaussian GaussianTimeProcess GaussianTimeHilbert GaussianTimeProductL2
open GaussianPastStepCompletion GaussianPredictableL2Completion
open PredictableRealL2

theorem rectangle_measure_ne_top (s t : ℝ≥0) (A : Set SampleSpace) :
    timeProbability (Ioc (s : ℝ) (t : ℝ) ×ˢ A) ≠ ∞ := by
  rw [Measure.prod_prod]
  exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)

theorem rectangle_indicator_mem (s t : ℝ≥0) (A : Set SampleSpace)
    (hA : MeasurableSet[naturalFiltration s] A) :
    indicatorConstLp 2 (measurableSet_Ioc.prod (naturalFiltration.le s A hA))
      (rectangle_measure_ne_top s t A) (1 : ℝ) ∈ closedProductSteps := by
  by_cases hst : s ≤ t
  · let C : GaussianL2 :=
      indicatorConstLp 2 (naturalFiltration.le s A hA) (measure_ne_top _ _) (1 : ℝ)
    have hm : AEStronglyMeasurable[naturalFiltration s] C gaussianProduct :=
      mem_lpMeas_indicatorConstLp (𝕜 := ℝ) (naturalFiltration.le s) hA (measure_ne_top _ _)
    have he : productTensor (intervalVector s t) C =
        indicatorConstLp 2 (measurableSet_Ioc.prod (naturalFiltration.le s A hA))
          (rectangle_measure_ne_top s t A) (1 : ℝ) := by
      apply Lp.ext
      have ht := (Measure.quasiMeasurePreserving_fst
        (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae_eq_comp
          (intervalVector_coeFn s t)
      have hc := (Measure.quasiMeasurePreserving_snd
        (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae_eq_comp
          (indicatorConstLp_coeFn (p := 2) (μ := gaussianProduct)
            (hs := naturalFiltration.le s A hA) (hμs := measure_ne_top _ _) (c := (1 : ℝ)))
      filter_upwards [productTensor_coeFn (intervalVector s t) C,
        indicatorConstLp_coeFn (p := 2) (μ := timeProbability)
          (hs := measurableSet_Ioc.prod (naturalFiltration.le s A hA))
          (hμs := rectangle_measure_ne_top s t A) (c := (1 : ℝ)), ht, hc]
        with z hz hi ht hc
      simp only [Function.comp_apply] at ht hc
      change C z.2 = _ at hc
      rw [hz, hi, ht, hc]
      by_cases hx : z.1 ∈ Ioc (s : ℝ) (t : ℝ) <;>
        by_cases hω : z.2 ∈ A <;> simp [hx, hω]
    rw [← he]
    exact past_step_mem_closedProductSteps s t hst C hm
  · have he : Ioc (s : ℝ) (t : ℝ) ×ˢ A = ∅ := by
      rw [Ioc_eq_empty_of_le (show (t : ℝ) ≤ s from le_of_not_ge hst), empty_prod]
    simpa only [he, indicatorConstLp_empty] using closedProductSteps.zero_mem

/-- Zero extension preserves the full independently defined predictable domain. -/
theorem zeroExtension_mem (T : ℝ≥0) (F : Lp ℝ 2 (horizonMeasure T gaussianProduct))
    (hF : AEStronglyMeasurable[predictable naturalFiltration] F
      (horizonMeasure T gaussianProduct)) :
    L2ZeroExtension (horizon_measurable T) F ∈ closedProductSteps := by
  let E := L2ZeroExtensionIsometry (μ := timeProbability) (horizon_measurable T)
  have hc : F ∈ (generatingIndicatorSpan (horizonMeasure T gaussianProduct)
      (generators naturalFiltration)).topologicalClosure := by
    rw [indicator_density]
    exact hF
  have hle : (generatingIndicatorSpan (horizonMeasure T gaussianProduct)
      (generators naturalFiltration)).topologicalClosure ≤
        closedProductSteps.comap E.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro G ⟨s, ⟨a, ha, rfl⟩, hs, rfl⟩
      change L2ZeroExtension (horizon_measurable T) _ ∈ closedProductSteps
      rw [L2ZeroExtension_indicator]
      rcases ha with rfl | (⟨A, hA, rfl⟩ | ⟨s, A, hA, rfl⟩)
      · simpa only [preimage_univ, inter_univ, horizon, NNReal.coe_zero] using
          rectangle_indicator_mem 0 T univ MeasurableSet.univ
      · simp only [horizon_inter_zero, indicatorConstLp_empty]
        exact closedProductSteps.zero_mem
      · simpa only [horizon_inter_Ioi] using rectangle_indicator_mem s T A hA
    · exact productStepSpan.isClosed_topologicalClosure.preimage E.continuous
  exact hle hc

/-- Independently specified full predictable L2 on (0,T], using Mathlib lpMeas. -/
abbrev PredictableDomain (T : ℝ≥0) :=
  lpMeas ℝ ℝ (predictable naturalFiltration) 2 (horizonMeasure T gaussianProduct)

def horizonEmbedding (T : ℝ≥0) : PredictableDomain T →ₗᵢ[ℝ] closedProductSteps where
  toLinearMap :=
    { toFun F := ⟨L2ZeroExtension (horizon_measurable T) F.val,
        zeroExtension_mem T F.val F.property⟩
      map_add' F G :=
        Subtype.ext ((L2ZeroExtensionIsometry (horizon_measurable T)).map_add F.val G.val)
      map_smul' c F :=
        Subtype.ext ((L2ZeroExtensionIsometry (horizon_measurable T)).map_smul c F.val) }
  norm_map' F := L2ZeroExtension_norm (horizon_measurable T) F.val

/-- The old completed integral, now on the entire finite-horizon predictable domain. -/
def itoIntegral (T : ℝ≥0) : PredictableDomain T →ₗᵢ[ℝ] GaussianL2 :=
  productIntegral.comp (horizonEmbedding T)

theorem itoIntegral_norm (T : ℝ≥0) (F : PredictableDomain T) :
    ‖itoIntegral T F‖ = ‖F‖ := (itoIntegral T).norm_map F

theorem itoIntegral_centered (T : ℝ≥0) (F : PredictableDomain T) :
    (∫ ω, itoIntegral T F ω ∂gaussianProduct) = 0 :=
  productIntegral_centered (horizonEmbedding T F)

theorem itoIntegral_divergence_graph (T : ℝ≥0) (F : PredictableDomain T) :
    ((productToField (horizonEmbedding T F) : GaussianVectorL2), itoIntegral T F) ∈
      hilbertDivergence.graph := productIntegral_hilbertDivergence_graph (horizonEmbedding T F)

/-- Direct access from Mathlib's NNReal predictable L2, with no identification assumed. -/
def nonnegativeEmbedding (T : ℝ≥0) :
    lpMeas ℝ ℝ naturalFiltration.predictable 2
      ((PredictableTimeTransport.timeMeasure T).prod gaussianProduct) →ₗᵢ[ℝ]
        PredictableDomain T where
  toLinearMap :=
    { toFun F := ⟨nonnegativePullback T gaussianProduct F.val,
        nonnegativePullback_predictable naturalFiltration T gaussianProduct F.val F.property⟩
      map_add' F G := Subtype.ext ((nonnegativePullback T gaussianProduct).map_add F.val G.val)
      map_smul' c F := Subtype.ext ((nonnegativePullback T gaussianProduct).map_smul c F.val) }
  norm_map' F := (nonnegativePullback T gaussianProduct).norm_map F.val

end OperatorDerivativeRewrite.Foundation.GaussianPredictableHorizon
