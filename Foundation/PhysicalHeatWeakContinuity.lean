import Foundation.PhysicalHeatConvolution
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Weak time continuity of physical heat probability laws

Fourier character integrals are continuous in the weak topology on torus
probability measures. The explicit heat moments vary continuously in time.
Compactness of probability measures on the compact torus and Fourier
uniqueness then force the entire law family to be continuous in time.
This is weak continuity of distributions; no sample-path theorem is inferred.
-/

open OperatorDerivativeRewrite.Foundation
open FiniteFourierDifferentialTrace FourierCovarianceCriterion
open PhysicalHeatConvolution PhysicalHeatLawUnique
open MeasureTheory AddCircle Filter
open scoped NNReal BoundedContinuousFunction Topology

noncomputable section

namespace OperatorDerivativeRewrite.Foundation.PhysicalHeatWeakContinuity

theorem character_integral_continuous (k : Wave) :
    Continuous (fun μ : ProbabilityMeasure (UnitAddTorus (Fin 3)) =>
      ∫ x, UnitAddTorus.mFourier k x ∂(μ : Measure (UnitAddTorus (Fin 3)))) := by
  rw [continuous_iff_continuousAt]
  intro μ
  let f : UnitAddTorus (Fin 3) →ᵇ ℂ :=
    ContinuousMap.equivBoundedOfCompact _ _ (UnitAddTorus.mFourier k)
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1
    (tendsto_id : Tendsto (fun q : ProbabilityMeasure (UnitAddTorus (Fin 3)) => q)
      (𝓝 μ) (𝓝 μ)) f
  change Tendsto (fun q : ProbabilityMeasure (UnitAddTorus (Fin 3)) =>
    ∫ x, UnitAddTorus.mFourier k x ∂(q : Measure (UnitAddTorus (Fin 3))))
    (𝓝 μ) (𝓝 (∫ x, UnitAddTorus.mFourier k x ∂(μ : Measure (UnitAddTorus (Fin 3)))))
  simpa [f, ContinuousMap.equivBoundedOfCompact] using h

theorem heatLaw_continuous (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) : Continuous (heatLaw r hr hr0) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  change Tendsto (heatLaw r hr hr0) (𝓝 t₀) (𝓝 (heatLaw r hr hr0 t₀))
  apply isCompact_univ.tendsto_nhds_of_unique_mapClusterPt
    (by simp)
  intro μ _ hμ
  apply physical_heat_law_unique r t₀ μ (heatLaw r hr hr0 t₀)
    ?_ (heatLaw_character r hr hr0 t₀)
  intro k
  let E : ProbabilityMeasure (UnitAddTorus (Fin 3)) → ℂ :=
    fun ν => ∫ x, UnitAddTorus.mFourier (-k) x
      ∂(ν : Measure (UnitAddTorus (Fin 3)))
  have hE : Continuous E := character_integral_continuous (-k)
  have hc : MapClusterPt (E μ) (𝓝 t₀) (E ∘ heatLaw r hr hr0) :=
    hμ.continuousAt_comp hE.continuousAt
  have hlim : Tendsto (E ∘ heatLaw r hr hr0) (𝓝 t₀)
      (𝓝 (Real.exp (-((t₀ : ℝ) * (r k : ℝ))) : ℂ)) := by
    have hcont : Continuous (fun t : ℝ≥0 =>
      (Real.exp (-((t : ℝ) * (r k : ℝ))) : ℂ)) := by fun_prop
    convert hcont.tendsto t₀ using 1
    ext t
    exact heatLaw_character r hr hr0 t k
  have hpt : ClusterPt (E μ) (𝓝 (Real.exp (-((t₀ : ℝ) * (r k : ℝ))) : ℂ)) :=
    hc.clusterPt.mono hlim
  by_contra hne
  have hd : (𝓝 (E μ) ⊓ 𝓝 (Real.exp (-((t₀ : ℝ) * (r k : ℝ))) : ℂ)) = ⊥ :=
    (disjoint_nhds_nhds.mpr hne).eq_bot
  have hbot : (⊥ : Filter ℂ).NeBot := by rw [← hd]; exact hpt
  exact (not_neBot.mpr rfl) hbot

theorem heatLaw_tendsto_dirac_zero (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) :
    Tendsto (heatLaw r hr hr0) (𝓝 (0 : ℝ≥0))
      (𝓝 ((Measure.dirac (0 : UnitAddTorus (Fin 3))).toProbabilityMeasure)) := by
  have h0 : heatLaw r hr hr0 0 =
      (Measure.dirac (0 : UnitAddTorus (Fin 3))).toProbabilityMeasure := by
    apply ProbabilityMeasure.toMeasure_injective
    exact heatLaw_zero r hr hr0
  simpa only [h0] using (heatLaw_continuous r hr hr0).tendsto 0

end OperatorDerivativeRewrite.Foundation.PhysicalHeatWeakContinuity
