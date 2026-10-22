import Foundation.IBMGermIndicatorSupport

/-! Probability-support and right-endpoint continuity inputs for predictable extension. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMGermSupportContinuity
open IBMTimeAveragedObservable IBMObservedTerminalMartingale
open IBMIntrinsicMartingaleStep (Coefficient)
open IBMGermPredictableStep IBMGermIndicatorSupport
set_option backward.isDefEq.respectTransparency false

theorem terminal_support_energy_tendsto (F : JointL2)
    (A : ℕ → Set IBMSourceLaws.JointSample) (hA : ∀ n, MeasurableSet (A n))
    (hvanish : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ∀ᶠ n in atTop, ω ∉ A n) :
    Tendsto (fun n => ∫ ω in A n, F ω ^ 2 ∂IBMSourceLaws.jointMeasure) atTop (𝓝 0) := by
  have hl : Tendsto (fun n => ∫ ω, (A n).indicator (fun ω => F ω ^ 2) ω
      ∂IBMSourceLaws.jointMeasure) atTop (𝓝 (∫ _ : IBMSourceLaws.JointSample,
        (0 : ℝ) ∂IBMSourceLaws.jointMeasure)) := by
    apply tendsto_integral_of_dominated_convergence (fun ω => F ω ^ 2)
    · intro n
      exact ((Lp.stronglyMeasurable F).measurable.pow_const 2).indicator (hA n)
        |>.aestronglyMeasurable
    · exact (Lp.memLp F).integrable_sq
    · intro n
      exact ae_of_all _ fun ω => by
        by_cases hn : ω ∈ A n <;>
          simp [Set.indicator, hn, Real.norm_eq_abs, sq_nonneg]
    · filter_upwards [hvanish] with ω hω
      apply tendsto_const_nhds.congr'
      exact hω.mono fun n hn => (Set.indicator_of_notMem hn _).symm
  simpa only [integral_indicator (hA _), integral_zero] using hl

theorem supported_classes_tendsto_zero (F : JointL2) (J : ℕ → JointL2)
    (A : ℕ → Set IBMSourceLaws.JointSample) (hA : ∀ n, MeasurableSet (A n))
    (hvanish : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ∀ᶠ n in atTop, ω ∉ A n)
    (hb : ∀ n, ‖J n‖ ^ 2 ≤ ∫ ω in A n, F ω ^ 2 ∂IBMSourceLaws.jointMeasure) :
    Tendsto J atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hs : Tendsto (fun n => ‖J n‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun n => sq_nonneg _) hb (terminal_support_energy_tendsto F A hA hvanish)
  have hr : Tendsto (fun n => Real.sqrt (‖J n‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto 0).comp hs
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hr

theorem finite_indicator_integrals_tendsto_zero {ι : ℕ → Type*} (F : JointL2)
    (I : ∀ n, Finset (ι n)) (s t : ∀ n, ι n → ℝ≥0)
    (a : ∀ n i, Coefficient (s n i))
    (hst : ∀ n i, i ∈ I n → s n i ≤ t n i)
    (hd : ∀ n i, i ∈ I n → ∀ j, j ∈ I n → i ≠ j → t n i ≤ s n j ∨ t n j ≤ s n i)
    (ha : ∀ n i, i ∈ I n → ∀ᵐ ω ∂IBMSourceLaws.jointMeasure,
      (a n i).function ω ^ 2 = (a n i).function ω)
    (A : ℕ → Set IBMSourceLaws.JointSample) (hA : ∀ n, MeasurableSet (A n))
    (hH : ∀ n r, ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ω ∉ A n →
      (∑ i ∈ I n, IBMIntrinsicPredictableProcess.timeStep (s n i) (t n i) (a n i) r ω) = 0)
    (hvanish : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ∀ᶠ n in atTop, ω ∉ A n) :
    Tendsto (fun n => sumClass F (I n) (s n) (t n) (a n)) atTop (𝓝 0) :=
  supported_classes_tendsto_zero F _ A hA hvanish fun n =>
    energy_support_bound F (I n) (s n) (t n) (a n) (hst n) (hd n) (ha n) (A n) (hA n) (hH n)

theorem right_trim_tendsto_zero (F : JointL2) (s : ℝ≥0) (a : Coefficient s)
    (τ : ℕ → ℝ≥0) (hst : ∀ n, s ≤ τ n) (hlim : Tendsto τ atTop (𝓝 s)) :
    Tendsto (fun n => stepClass F s (τ n) a) atTop (𝓝 0) := by
  have hw : Tendsto τ atTop (𝓝[Ici s] s) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hst⟩
  have hc := (channel_right_continuous
    (IBMWeightedTerminalEnergy.weightedTerminal F s a) s).tendsto.comp hw
  simpa only [stepClass, sub_self, Function.comp_def] using hc.sub
    (tendsto_const_nhds (x := channelClass (IBMWeightedTerminalEnergy.weightedTerminal F s a) s))

end OperatorDerivativeRewrite.Foundation.IBMGermSupportContinuity
