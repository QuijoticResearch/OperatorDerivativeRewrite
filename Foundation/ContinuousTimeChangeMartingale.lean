import Foundation.ContinuousBoundedSampling

/-! Continuous martingales sampled along increasing bounded stopping clocks.
The clock is allowed to depend on the very same noise as the martingale. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.ContinuousTimeChangeMartingale
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  (ℱ : Filtration ℝ≥0 m) (M : ℝ≥0 → Ω → ℝ)

theorem sample_two (hM : Martingale M ℱ μ) (hc : ∀ ω, Continuous (fun t => M t ω))
    (σ τ : Ω → ℝ≥0) (hσ : IsStoppingTime ℱ (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (hστ : ∀ ω, σ ω ≤ τ ω) (N : ℕ) (hN : ∀ ω, τ ω ≤ N) :
    (fun ω => M (σ ω) ω) =ᵐ[μ] μ[(fun ω => M (τ ω) ω) | hσ.measurableSpace] := by
  have hσN (ω : Ω) : σ ω ≤ N := (hστ ω).trans (hN ω)
  have h1 := ContinuousBoundedSampling.stopped_ae_condExp μ ℱ M hM hc σ hσ N hσN
  have h2 := ContinuousBoundedSampling.stopped_ae_condExp μ ℱ M hM hc τ hτ N hN
  have ht : μ[(fun ω => M (τ ω) ω) | hσ.measurableSpace] =ᵐ[μ]
      μ[M (N : ℝ≥0) | hσ.measurableSpace] :=
    (condExp_congr_ae h2).trans (condExp_condExp_of_le
      (hσ.measurableSpace_mono hτ (fun ω => WithTop.coe_le_coe.mpr (hστ ω)))
      hτ.measurableSpace_le)
  exact h1.trans ht.symm

variable (A : ℝ≥0 → Ω → ℝ≥0)
  (hA : ∀ t, IsStoppingTime ℱ (fun ω => (A t ω : WithTop ℝ≥0)))
  (hmono : ∀ ω, Monotone (fun t => A t ω))

def changedFiltration : Filtration ℝ≥0 m where
  seq t := (hA t).measurableSpace
  mono' s t hst := (hA s).measurableSpace_mono (hA t)
    (fun ω => WithTop.coe_le_coe.mpr (hmono ω hst))
  le' t := (hA t).measurableSpace_le

theorem changed_stronglyAdapted (hM : StronglyAdapted ℱ M)
    (hc : ∀ ω, Continuous (fun t => M t ω)) :
    StronglyAdapted (changedFiltration ℱ A hA hmono) (fun t ω => M (A t ω) ω) := by
  intro t
  simpa only [ContinuousBoundedSampling.stoppedValue_coe] using
    (measurable_stoppedValue (hM.isStronglyProgressive_of_continuous hc) (hA t)).stronglyMeasurable

theorem changed_martingale (hM : Martingale M ℱ μ)
    (hc : ∀ ω, Continuous (fun t => M t ω)) (hb : ∀ t ω, A t ω ≤ t) :
    Martingale (fun t ω => M (A t ω) ω) (changedFiltration ℱ A hA hmono) μ := by
  refine ⟨changed_stronglyAdapted ℱ M A hA hmono hM.stronglyAdapted hc, ?_⟩
  intro s t hst
  exact (sample_two μ ℱ M hM hc (A s) (A t) (hA s) (hA t)
    (fun ω => hmono ω hst) (Nat.ceil t)
    (fun ω => (hb t ω).trans (Nat.le_ceil t))).symm

end OperatorDerivativeRewrite.Foundation.ContinuousTimeChangeMartingale
