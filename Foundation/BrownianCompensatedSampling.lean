import Foundation.BrownianComplexSampling
import Foundation.BrownianStoppedTrigConditional

/-! Actual normalized compensated Brownian phase products at two bounded stopping times. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianCompensatedSampling
open InfiniteGaussian IBMConstructedSources BrownianMassClockStoppingTime
open BrownianComplexSampling BrownianFourierMartingales BrownianStoppedTrigConditional
open BrownianMassRandomTimeChange
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath

theorem phase_norm (u : ℝ) (t : ℝ≥0) (w : SampleSpace) : ‖phase u t w‖=weight u t := by
  rw [phase_eq,norm_mul,IBMOneTimeFourier.observable_norm,mul_one]
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (weight_positive u t)]

theorem phase_nonzero (u : ℝ) (t : ℝ≥0) (w : SampleSpace) : phase u t w ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [phase_norm]
  exact ne_of_gt (weight_positive u t)

theorem phase_norm_one_le (u : ℝ) (t : ℝ≥0) (w : SampleSpace) : 1 ≤ ‖phase u t w‖ := by
  rw [phase_norm,weight]
  exact Real.one_le_exp (by positivity)

variable (τ : SampleSpace → ℝ≥0)
  (hτ : IsStoppingTime augmentedPast (fun w => (τ w : WithTop ℝ≥0)))
  (σ : SampleSpace → ℝ≥0)
  (hσ : IsStoppingTime augmentedPast (fun w => (σ w : WithTop ℝ≥0)))

include hτ in
theorem bounded_weighted_sampling (u : ℝ) (hστ : ∀ w, σ w ≤ τ w)
    (N : ℕ) (hN : ∀ w, τ w ≤ N) (F : SampleSpace → ℂ)
    (hF : StronglyMeasurable[hσ.measurableSpace] F) (C : ℝ) (hC : ∀ w, ‖F w‖ ≤ C) :
    (∫ w, F w*phase u (τ w) w ∂gaussianProduct)=
      ∫ w, F w*phase u (σ w) w ∂gaussianProduct := by
  have hma := (hF.measurable.mono hσ.measurableSpace_le le_rfl).mul
    ((phase_at_stop_measurable τ hτ u).mono hτ.measurableSpace_le le_rfl)
  apply weighted_sampling τ hτ σ hσ u hστ N hN F hF
  apply Integrable.of_bound hma.aestronglyMeasurable (C*weight u N)
  exact Eventually.of_forall fun w => by
    change ‖F w*phase u (τ w) w‖ ≤ C*weight u N
    rw [norm_mul,phase_norm]
    apply mul_le_mul (hC w) (weight_monotone u (by exact_mod_cast hN w))
      (le_of_lt (weight_positive _ _))
    exact (norm_nonneg (F w)).trans (hC w)

def phaseRatio (a b : ℝ) (σ : SampleSpace → ℝ≥0) (w : SampleSpace) : ℂ :=
  phase a (σ w) w/phase b (σ w) w

theorem ratio_measurable (a b : ℝ) : Measurable[hσ.measurableSpace] (phaseRatio a b σ) :=
  (phase_at_stop_measurable σ hσ a).div (phase_at_stop_measurable σ hσ b)

theorem ratio_bound (a b : ℝ) (N : ℕ) (hN : ∀ w, σ w ≤ N) (w : SampleSpace) :
    ‖phaseRatio a b σ w‖ ≤ weight a N := by
  rw [phaseRatio,norm_div]
  apply (div_le_self (norm_nonneg _) (phase_norm_one_le b (σ w) w)).trans
  rw [phase_norm]
  exact weight_monotone a (by exact_mod_cast hN w)

include hτ hσ in
theorem two_phase_mean (a b : ℝ) (hστ : ∀ w, σ w ≤ τ w)
    (N : ℕ) (hN : ∀ w, τ w ≤ N) :
    (∫ w, phaseRatio a b σ w*phase b (τ w) w ∂gaussianProduct)=1 := by
  have hσN (w : SampleSpace) : σ w ≤ N := (hστ w).trans (hN w)
  rw [bounded_weighted_sampling τ hτ σ hσ b hστ N hN (phaseRatio a b σ)
    (ratio_measurable σ hσ a b).stronglyMeasurable (weight a N) (ratio_bound σ a b N hσN)]
  have he (w : SampleSpace) : phaseRatio a b σ w*phase b (σ w) w=phase a (σ w) w :=
    div_mul_cancel₀ _ (phase_nonzero b (σ w) w)
  simp_rw [he]
  exact phase_mean σ hσ a N hσN

theorem inverse_two_phase_mean (κ s t : ℝ≥0) (hst : s ≤ t) (a b : ℝ) :
    (∫ w, phaseRatio a b (fun w => inverse κ w s) w*
      phase b (inverse κ w t) w ∂gaussianProduct)=1 := by
  apply two_phase_mean (fun w => inverse κ w t) (inverse_isStoppingTime κ t)
    (fun w => inverse κ w s) (inverse_isStoppingTime κ s) a b
    (fun w => inverse_monotone κ w hst) (Nat.ceil t)
  intro w
  exact (inverse_le κ w t).trans (Nat.le_ceil t)

end OperatorDerivativeRewrite.Foundation.BrownianCompensatedSampling
