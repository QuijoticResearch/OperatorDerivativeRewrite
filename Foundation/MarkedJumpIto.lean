import Foundation.MarkedDynkinSampling

/-! Exact finite-activity jump Ito sums and their genuine compensated martingales. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.MarkedJumpIto
open MarkedRootRenewalProcess (StateSample probability MarkSample position)
open MarkedRenewalMartingale MarkedTimeIntegral
open ComplexRootTransitionOperator (Test)

theorem position_successor (a : ℝ) (n : ℕ) (η : MarkSample) :
    position a (n+1) η = position a n η + ComplexFourthRootNoise.noise a (η n) := by
  simp [position, Finset.sum_range_succ]

def jumpSum (a : ℝ) (f : ℂ → ℂ) (t : ℝ≥0) (ω : StateSample) : ℂ :=
  ∑ j ∈ Finset.range (ExponentialRenewalCount.count t ω.1),
    (f (position a j ω.2 + ComplexFourthRootNoise.noise a (ω.2 j)) - f (position a j ω.2))

theorem jump_formula (a : ℝ) (f : ℂ → ℂ) (t : ℝ≥0) (ω : StateSample) :
    jumpSum a f t ω = f (process a t ω)-f 0 := by
  unfold jumpSum
  simp_rw [← position_successor]
  exact Finset.sum_range_sub (fun j => f (position a j ω.2))
    (ExponentialRenewalCount.count t ω.1)

theorem actual_clock_formula (a : ℝ) (f : ℂ → ℂ) (t : ℝ≥0) (ω : StateSample)
    (hω : ExponentialNonexplosiveClock.Good ω.1) :
    jumpSum a f t ω = ∑ j ∈ Finset.range (ExponentialRenewalCount.count t ω.1),
      (f (MarkedRootRenewalProcess.process a (ExponentialNonexplosiveClock.clock (j+1) ω.1) ω) -
        f (MarkedRootRenewalProcess.process a (ExponentialNonexplosiveClock.clock j ω.1) ω)) := by
  unfold jumpSum
  apply Finset.sum_congr rfl
  intro j _
  rw [MarkedRootRenewalProcess.process_at_clock a ω hω (j+1),
    MarkedRootRenewalProcess.process_at_clock a ω hω j, position_successor]

theorem count_before_jump (ω : ExponentialHoldingSequence.Sample)
    (hω : ExponentialNonexplosiveClock.Good ω) (n : ℕ) :
    (fun u : ℝ => ExponentialRenewalCount.count u ω) =ᶠ[
      𝓝[<] (ExponentialNonexplosiveClock.clock (n+1) ω)] (fun _ => n) := by
  have hm := ExponentialNonexplosiveClock.good_strictMono hω (Nat.lt_succ_self n)
  have hlo : ∀ᶠ u : ℝ in 𝓝[<] (ExponentialNonexplosiveClock.clock (n+1) ω),
      ExponentialNonexplosiveClock.clock n ω < u :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hm)
  filter_upwards [hlo, self_mem_nhdsWithin] with u hu hut
  have hl : n ≤ ExponentialRenewalCount.count u ω := by
    rw [← ExponentialRenewalCount.count_at_clock hω n]
    exact ExponentialRenewalCount.count_monotone ω hu.le
  have hr := ExponentialRenewalCount.firstAbove_le hω u (n+1) hut
  unfold ExponentialRenewalCount.count at hl ⊢
  omega

theorem process_before_jump (a : ℝ) (ω : StateSample)
    (hω : ExponentialNonexplosiveClock.Good ω.1) (n : ℕ) :
    Tendsto (fun u : ℝ => MarkedRootRenewalProcess.process a u ω)
      (𝓝[<] (ExponentialNonexplosiveClock.clock (n+1) ω.1))
      (𝓝 (position a n ω.2)) := by
  have he : (fun u : ℝ => MarkedRootRenewalProcess.process a u ω) =ᶠ[
      𝓝[<] (ExponentialNonexplosiveClock.clock (n+1) ω.1)] (fun _ => position a n ω.2) := by
    filter_upwards [count_before_jump ω.1 hω n] with u hu
    rw [MarkedRootRenewalProcess.process, hu]
  exact tendsto_const_nhds.congr' he.symm

theorem process_leftLim (a : ℝ) (ω : StateSample)
    (hω : ExponentialNonexplosiveClock.Good ω.1) (n : ℕ) :
    Function.leftLim (fun u : ℝ => MarkedRootRenewalProcess.process a u ω)
      (ExponentialNonexplosiveClock.clock (n+1) ω.1) = position a n ω.2 :=
  leftLim_eq_of_tendsto (process_before_jump a ω hω n)

theorem actual_jump (a : ℝ) (ω : StateSample)
    (hω : ExponentialNonexplosiveClock.Good ω.1) (n : ℕ) :
    MarkedRootRenewalProcess.process a (ExponentialNonexplosiveClock.clock (n+1) ω.1) ω -
      Function.leftLim (fun u : ℝ => MarkedRootRenewalProcess.process a u ω)
        (ExponentialNonexplosiveClock.clock (n+1) ω.1) =
      ComplexFourthRootNoise.noise a (ω.2 n) := by
  rw [MarkedRootRenewalProcess.process_at_clock a ω hω (n+1), process_leftLim a ω hω n,
    position_successor]
  abel

theorem ito_leftLim_formula (a : ℝ) (f : ℂ → ℂ) (t : ℝ≥0) (ω : StateSample)
    (hω : ExponentialNonexplosiveClock.Good ω.1) :
    f (process a t ω)-f 0 = ∑ j ∈ Finset.range (ExponentialRenewalCount.count t ω.1),
      (f (MarkedRootRenewalProcess.process a (ExponentialNonexplosiveClock.clock (j+1) ω.1) ω) -
        f (Function.leftLim (fun u : ℝ => MarkedRootRenewalProcess.process a u ω)
          (ExponentialNonexplosiveClock.clock (j+1) ω.1))) := by
  rw [← jump_formula]
  unfold jumpSum
  apply Finset.sum_congr rfl
  intro j _
  rw [MarkedRootRenewalProcess.process_at_clock a ω hω (j+1), process_leftLim a ω hω j,
    position_successor]

theorem jumpSum_adapted (a : ℝ) (f : Test) : StronglyAdapted (history a) (jumpSum a f) := by
  intro t
  have he : jumpSum a f t = (fun ω => f (process a t ω)-f 0) := funext (jump_formula a f t)
  rw [he]
  exact (f.continuous.measurable.comp (process_adapted a t).measurable).stronglyMeasurable.sub
    stronglyMeasurable_const

theorem jumpSum_integrable (a : ℝ) (f : Test) (t : ℝ≥0) :
    Integrable (jumpSum a f t) probability := by
  have he : jumpSum a f t = (fun ω => f (process a t ω)-f 0) := funext (jump_formula a f t)
  rw [he]
  exact (MarkedOperatorConditional.observable_integrable a t f).sub (integrable_const _)

def compensated (a : ℝ) (f : Test) (t : ℝ≥0) (ω : StateSample) : ℂ :=
  jumpSum a f t ω - primitive a (ComplexRootTransitionOperator.generator 1 a f) t ω

theorem compensated_eq_dynkin (a : ℝ) (f : Test) :
    compensated a f = MarkedDynkinMartingale.dynkin a f := by
  funext t ω
  rw [compensated, jump_formula]
  rfl

theorem compensated_martingale (a : ℝ) (f : Test) :
    Martingale (compensated a f) (history a) probability := by
  rw [compensated_eq_dynkin]
  exact MarkedDynkinMartingale.dynkin_martingale a f

theorem stopped_jump_integrable (a : ℝ) (f : Test) (τ : StateSample → ℝ≥0)
    (hτ : IsStoppingTime (history a) (fun ω => (τ ω : WithTop ℝ≥0))) :
    Integrable (fun ω => jumpSum a f (τ ω) ω) probability := by
  have he : (fun ω => jumpSum a f (τ ω) ω) =
      (fun ω => f (process a (τ ω) ω)-f 0) := funext fun ω => jump_formula a f (τ ω) ω
  rw [he]
  exact (MarkedDynkinSampling.stopped_observable_integrable a f τ hτ).sub
    (integrable_const _)

theorem stopped_jump_compensator (a : ℝ) (f : Test) (τ : StateSample → ℝ≥0)
    (hτ : IsStoppingTime (history a) (fun ω => (τ ω : WithTop ℝ≥0)))
    (N : ℕ) (hN : ∀ ω, τ ω ≤ N) :
    (∫ ω, jumpSum a f (τ ω) ω ∂probability) =
      ∫ ω, primitive a (ComplexRootTransitionOperator.generator 1 a f) (τ ω) ω ∂probability := by
  have he : (fun ω => jumpSum a f (τ ω) ω) =
      (fun ω => f (process a (τ ω) ω)-f 0) := funext fun ω => jump_formula a f (τ ω) ω
  rw [he, integral_sub (MarkedDynkinSampling.stopped_observable_integrable a f τ hτ)
    (integrable_const _)]
  simpa using MarkedDynkinSampling.stopped_dynkin_identity a f τ hτ N hN

end OperatorDerivativeRewrite.Foundation.MarkedJumpIto
