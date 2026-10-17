import Foundation.MarkedUnboundedSampling
import Foundation.RootRenewalPathLaw
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-! Actual normalized finite complex measures on the constructed cadlag complex paths. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.MarkedExponentialTilt
open MarkedRootRenewalProcess (StateSample probability)
open MarkedRenewalMartingale MarkedExponentialMartingale MarkedUnboundedSampling
open RootRenewalPathLaw (Path path path_measurable)

def source (a ξ : ℝ) (τ : StateSample → ℝ≥0) : VectorMeasure StateSample ℂ :=
  probability.withDensityᵥ (fun ω => normalized a ξ (τ ω) ω)

def law (a ξ : ℝ) (τ : StateSample → ℝ≥0) : VectorMeasure Path ℂ :=
  (source a ξ τ).map (path a)

variable (a ξ : ℝ) (τ : StateSample → ℝ≥0)
  (hτ : IsStoppingTime (history a) (fun ω => (τ ω : WithTop ℝ≥0)))
  (N : ℕ) (hN : ∀ ω, τ ω ≤ N)

include hτ hN in
theorem source_apply (A : Set StateSample) (hA : MeasurableSet A) :
    source a ξ τ A = ∫ ω in A, normalized a ξ (τ ω) ω ∂probability := by
  rw [source,withDensityᵥ_apply (exponential_stopped_integrable a τ hτ N hN ξ) hA]

include hτ hN in
theorem source_mass : source a ξ τ univ = 1 := by
  rw [source_apply a ξ τ hτ N hN _ MeasurableSet.univ,Measure.restrict_univ]
  exact exponential_stopped_mean a τ hτ N hN ξ

include hτ hN in
theorem source_variation : (source a ξ τ).variation =
    probability.withDensity (fun ω => ‖normalized a ξ (τ ω) ω‖ₑ) := by
  rw [source]
  exact Measure.variation_withDensityᵥ (exponential_stopped_integrable a τ hτ N hN ξ)

include hτ hN in
theorem source_finite_variation : IsFiniteMeasure (source a ξ τ).variation := by
  have hf := exponential_stopped_integrable a τ hτ N hN ξ
  let : IsFiniteMeasure (probability.withDensity (fun ω => ‖normalized a ξ (τ ω) ω‖ₑ)) :=
    ⟨by simpa using! hf.2⟩
  rw [source_variation a ξ τ hτ N hN]
  infer_instance

include hτ hN in
theorem source_null (A : Set StateSample) (hA : MeasurableSet A) (hzero : probability A = 0) :
    source a ξ τ A = 0 := by
  rw [source_apply a ξ τ hτ N hN A hA,Measure.restrict_zero_set hzero,integral_zero_measure]

include hτ hN in
theorem source_absolutelyContinuous : source a ξ τ ≪ᵥ probability.toENNRealVectorMeasure := by
  refine VectorMeasure.AbsolutelyContinuous.mk fun A hA hzero => ?_
  rw [Measure.toENNRealVectorMeasure_apply_measurable hA] at hzero
  exact source_null a ξ τ hτ N hN A hA hzero

include hτ hN in
theorem law_apply (A : Set Path) (hA : MeasurableSet A) :
    law a ξ τ A = ∫ ω in (path a) ⁻¹' A, normalized a ξ (τ ω) ω ∂probability := by
  rw [law,VectorMeasure.map_apply _ (path_measurable a) hA,
    source_apply a ξ τ hτ N hN _ ((path_measurable a) hA)]

include hτ hN in
theorem law_mass : law a ξ τ univ = 1 := by
  rw [law,VectorMeasure.map_apply _ (path_measurable a) MeasurableSet.univ,preimage_univ]
  exact source_mass a ξ τ hτ N hN

include hτ hN in
theorem law_finite_variation : IsFiniteMeasure (law a ξ τ).variation := by
  let := source_finite_variation a ξ τ hτ N hN
  unfold law
  infer_instance

include hτ hN in
theorem law_null (A : Set Path) (hA : MeasurableSet A) (hzero : RootRenewalPathLaw.law a A = 0) :
    law a ξ τ A = 0 := by
  rw [RootRenewalPathLaw.law,Measure.map_apply (path_measurable a) hA] at hzero
  rw [law,VectorMeasure.map_apply _ (path_measurable a) hA]
  exact source_null a ξ τ hτ N hN _ ((path_measurable a) hA) hzero

include hτ hN in
theorem stopping_consistency (σ : StateSample → ℝ≥0)
    (hσ : IsStoppingTime (history a) (fun ω => (σ ω : WithTop ℝ≥0)))
    (hστ : ∀ ω, σ ω ≤ τ ω) (A : Set StateSample) (hA : MeasurableSet[hσ.measurableSpace] A) :
    source a ξ τ A = source a ξ σ A := by
  have hb : ∀ ω, σ ω ≤ N := fun ω => (hστ ω).trans (hN ω)
  have hraw : MeasurableSet A := hσ.measurableSpace_le A hA
  have hi := exponential_stopped_integrable a τ hτ N hN ξ
  have hc := RightContinuousBoundedSampling.sample_two probability (history a) (normalized a ξ)
    (normalized_martingale a ξ) (exponential_rightContinuous a ξ) τ hτ N hN σ hσ hστ
  rw [source_apply a ξ τ hτ N hN A hraw,source_apply a ξ σ hσ N hb A hraw]
  calc
    _ = ∫ ω in A, probability[fun ω => normalized a ξ (τ ω) ω | hσ.measurableSpace] ω
        ∂probability := (setIntegral_condExp hσ.measurableSpace_le hi hA).symm
    _ = _ := integral_congr_ae (ae_restrict_of_ae hc)

end OperatorDerivativeRewrite.Foundation.MarkedExponentialTilt
