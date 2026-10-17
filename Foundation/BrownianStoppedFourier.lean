import Foundation.BrownianFourierMartingales
import Foundation.ContinuousTimeChangeMartingale

/-! Actual bounded stopping-time identities for Brownian Fourier martingales.
Deterministic delay of an NNReal stopping time is proved without right continuity. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianStoppedFourier
open InfiniteGaussian IBMConstructedSources BrownianMassClockStoppingTime
open BrownianFourierMartingales ContinuousTimeChangeMartingale
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath

theorem delay_isStoppingTime {Ω : Type*} [m : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 m) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) (h : ℝ≥0) :
    IsStoppingTime ℱ (fun ω => ((τ ω+h : ℝ≥0) : WithTop ℝ≥0)) := by
  intro t
  by_cases ht : h ≤ t
  · have he : {ω | ((τ ω+h : ℝ≥0) : WithTop ℝ≥0) ≤ t} =
        {ω | (τ ω : WithTop ℝ≥0) ≤ ((t-h : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      simp only [mem_ofPred_eq,WithTop.coe_le_coe]
      exact (le_tsub_iff_right ht).symm
    rw [he]
    exact ℱ.mono (show t-h ≤ t from tsub_le_self) _ (hτ (t-h))
  · have he : {ω | ((τ ω+h : ℝ≥0) : WithTop ℝ≥0) ≤ t} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq,WithTop.coe_le_coe,mem_empty_iff_false,iff_false]
      exact not_le.mpr ((lt_of_not_ge ht).trans_le (le_add_left le_rfl))
    rw [he]
    exact (ℱ t).measurableSet_empty

theorem time_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 m) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) :
    Measurable[hτ.measurableSpace] τ := by
  apply measurable_of_Iic
  intro t
  change MeasurableSet[hτ.measurableSpace] {ω | τ ω ≤ t}
  simpa only [WithTop.coe_le_coe] using hτ.measurableSet_le' t

variable (τ : SampleSpace → ℝ≥0)
  (hτ : IsStoppingTime augmentedPast (fun ω => (τ ω : WithTop ℝ≥0)))

theorem brownian_at_stop_measurable :
    Measurable[hτ.measurableSpace] (fun ω => clockPath ω (τ ω)) := by
  have hm := measurable_stoppedValue
    (BrownianAugmentedMartingales.brownian_stronglyAdapted.isStronglyProgressive_of_continuous
      (fun ω => (clockPath ω).continuous)) hτ
  simpa only [ContinuousBoundedSampling.stoppedValue_coe] using hm

include hτ in
theorem shifted_brownian_measurable (h : ℝ≥0) :
    Measurable (fun ω => clockPath ω (τ ω+h)) := by
  have ht : Measurable τ := (time_measurable augmentedPast τ hτ).mono hτ.measurableSpace_le le_rfl
  exact continuous_eval.measurable.comp (clockPath_measurable.prodMk (ht.add_const h))

theorem cosine_sampling (u : ℝ) (h : ℝ≥0) (N : ℕ) (hN : ∀ ω, τ ω ≤ N) :
    gaussianProduct[(fun ω => cosineProcess u (τ ω+h) ω) | hτ.measurableSpace]
      =ᵐ[gaussianProduct] (fun ω => cosineProcess u (τ ω) ω) := by
  exact (sample_two gaussianProduct augmentedPast (cosineProcess u) (cosine_martingale u)
    (cosine_continuous u) τ (fun ω => τ ω+h) hτ (delay_isStoppingTime _ _ hτ h)
    (fun ω => le_add_right le_rfl) (Nat.ceil ((N : ℝ≥0)+h))
    (fun ω => (add_le_add (hN ω) (le_refl h)).trans (Nat.le_ceil _))).symm

theorem sine_sampling (u : ℝ) (h : ℝ≥0) (N : ℕ) (hN : ∀ ω, τ ω ≤ N) :
    gaussianProduct[(fun ω => sineProcess u (τ ω+h) ω) | hτ.measurableSpace]
      =ᵐ[gaussianProduct] (fun ω => sineProcess u (τ ω) ω) := by
  exact (sample_two gaussianProduct augmentedPast (sineProcess u) (sine_martingale u)
    (sine_continuous u) τ (fun ω => τ ω+h) hτ (delay_isStoppingTime _ _ hτ h)
    (fun ω => le_add_right le_rfl) (Nat.ceil ((N : ℝ≥0)+h))
    (fun ω => (add_le_add (hN ω) (le_refl h)).trans (Nat.le_ceil _))).symm

end OperatorDerivativeRewrite.Foundation.BrownianStoppedFourier
