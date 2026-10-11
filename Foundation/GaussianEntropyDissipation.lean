/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Copyright (c) 2026 OperatorDerivativeRewrite contributors.
The dominated-convergence argument for the entropy limit is adapted from
Gaussian1D.ouSemigroup_entropy_sq_ergodic in
MarkovSemigroups/Instances/WorkInProgress/Euclidean.lean, commit
acf649108ea2222f4a8544a2782f448cb502492a, Apache License 2.0.
See LICENSES/Apache-2.0.txt. This module does not yet prove entropy dissipation.
-/
import Foundation.GaussianEntropy
import Foundation.GaussianFisherDecay

/-! Centered Gaussian density entropy: finiteness, trajectory continuity and limits.
Time differentiation and the Gaussian integration-by-parts step remain separate obligations. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianEntropyDissipation

abbrev γ : Measure ℝ := GaussianMehler.γ

/-- Centered density entropy. The theorems below establish genuine integrability
on bounded measurable functions. It is interpreted as entropy for nonnegative densities. -/
def entropyDensity (g : ℝ → ℝ) : ℝ :=
  (∫ x, g x * Real.log (g x) ∂γ) -
    (∫ x, g x ∂γ) * Real.log (∫ x, g x ∂γ)

/-- The actual centered entropy of the existing Mehler evolution. -/
def entropyTrajectory (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  entropyDensity (GaussianMehler.mehler t g)

/-- Density entropy agrees exactly with M1 square entropy of the square root. -/
theorem entropyDensity_eq_entropySq_sqrt {g : ℝ → ℝ} (hg : ∀ x, 0 ≤ g x) :
    entropyDensity g = entropySq γ (fun x => Real.sqrt (g x)) := by
  have hs : ∀ x, (Real.sqrt (g x)) ^ 2 = g x := fun x => Real.sq_sqrt (hg x)
  simp only [entropyDensity, entropySq, hs]

/-- Compactness bounds the zero-compatible continuous function r log r. -/
theorem exists_mul_log_bound (M : ℝ) :
    ∃ B : ℝ, ∀ r : ℝ, ‖r‖ ≤ M → ‖r * Real.log r‖ ≤ B := by
  have hc : IsCompact ((fun r : ℝ => ‖r * Real.log r‖) '' Set.Icc (-M) M) :=
    isCompact_Icc.image Real.continuous_mul_log.norm
  obtain ⟨B, hB⟩ := hc.bddAbove
  refine ⟨B, fun r hr => hB ⟨r, ?_, rfl⟩⟩
  exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hr)

/-- Both terms defining centered entropy have their intended finite integral meaning. -/
theorem entropyDensity_integrable {g : ℝ → ℝ} (hg : Measurable g)
    {M : ℝ} (hgb : ∀ x, ‖g x‖ ≤ M) :
    Integrable g γ ∧ Integrable (fun x => g x * Real.log (g x)) γ := by
  obtain ⟨B, hB⟩ := exists_mul_log_bound M
  constructor
  · exact GaussianMehler.integrable_comp_of_bounded hg hgb measurable_id
  · refine Integrable.mono' (integrable_const B)
      (Real.continuous_mul_log.measurable.comp hg).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun x => hB (g x) (hgb x))

/-- Jensen proves nonnegative centered entropy after establishing both integrals. -/
theorem entropyDensity_nonneg {g : ℝ → ℝ} (hg : Measurable g)
    {M : ℝ} (hgb : ∀ x, ‖g x‖ ≤ M) (hpos : ∀ x, 0 ≤ g x) :
    0 ≤ entropyDensity g := by
  obtain ⟨hi, hlogi⟩ := entropyDensity_integrable hg hgb
  have hj := Real.convexOn_mul_log.map_integral_le
    Real.continuous_mul_log.continuousOn isClosed_Ici
    (Filter.Eventually.of_forall hpos) hi hlogi
  exact sub_nonneg.mpr hj

/-- Continuity in time follows from dominated convergence on the actual kernel.
The square-root coefficient is continuous even at time zero. -/
theorem mehler_time_continuous {g : ℝ → ℝ} (hg : Continuous g)
    {M : ℝ} (hgb : ∀ x, ‖g x‖ ≤ M) (x : ℝ) :
    Continuous (fun t => GaussianMehler.mehler t g x) := by
  change Continuous (fun t => ∫ y, g (Real.exp (-t) * x +
    Real.sqrt (1 - Real.exp (-2 * t)) * y) ∂γ)
  apply continuous_of_dominated (bound := fun _ => M)
  · intro t
    exact (GaussianMehler.kernel_integrable hg hgb t x).1
  · intro t
    exact Filter.Eventually.of_forall (fun y => hgb _)
  · exact integrable_const M
  · apply Filter.Eventually.of_forall
    intro y
    exact hg.comp (by fun_prop)

/-- Genuine integrability of the evolved density and entropy integrand, at every time. -/
theorem entropyTrajectory_integrable {g : ℝ → ℝ} (hg : Continuous g)
    {M : ℝ} (hgb : ∀ x, ‖g x‖ ≤ M) (t : ℝ) :
    Integrable (GaussianMehler.mehler t g) γ ∧
      Integrable (fun x => GaussianMehler.mehler t g x *
        Real.log (GaussianMehler.mehler t g x)) γ :=
  entropyDensity_integrable (GaussianMehler.mehler_continuous hg hgb t).measurable
    (fun x => GaussianMehler.mehler_norm_le hgb t x)

/-- Nonnegative inputs give genuine nonnegative entropy along the actual trajectory. -/
theorem entropyTrajectory_nonneg {g : ℝ → ℝ} (hg : Continuous g)
    {M : ℝ} (hgb : ∀ x, ‖g x‖ ≤ M) (hpos : ∀ x, 0 ≤ g x) (t : ℝ) :
    0 ≤ entropyTrajectory g t := by
  exact entropyDensity_nonneg (GaussianMehler.mehler_continuous hg hgb t).measurable
    (fun x => GaussianMehler.mehler_norm_le hgb t x)
    (fun x => GaussianMehler.mehler_nonneg hg hgb hpos t x)
/-- Centered entropy is continuous in time, with integrable constant domination
for both spatial integrals. No time derivative at zero is asserted. -/
theorem entropyTrajectory_continuous {g : ℝ → ℝ} (hg : Continuous g)
    {M : ℝ} (hgb : ∀ x, ‖g x‖ ≤ M) : Continuous (entropyTrajectory g) := by
  obtain ⟨B, hB⟩ := exists_mul_log_bound M
  have hmass : Continuous (fun t => ∫ x, GaussianMehler.mehler t g x ∂γ) := by
    apply continuous_of_dominated (bound := fun _ => M)
    · intro t
      exact (GaussianMehler.mehler_integrable hg hgb t).1
    · intro t
      exact Filter.Eventually.of_forall (fun x => GaussianMehler.mehler_norm_le hgb t x)
    · exact integrable_const M
    · exact Filter.Eventually.of_forall (fun x => mehler_time_continuous hg hgb x)
  have hlog : Continuous (fun t => ∫ x, GaussianMehler.mehler t g x *
      Real.log (GaussianMehler.mehler t g x) ∂γ) := by
    apply continuous_of_dominated (bound := fun _ => B)
    · intro t
      exact (entropyTrajectory_integrable hg hgb t).2.1
    · intro t
      exact Filter.Eventually.of_forall (fun x =>
        hB _ (GaussianMehler.mehler_norm_le hgb t x))
    · exact integrable_const B
    · exact Filter.Eventually.of_forall (fun x =>
        Real.continuous_mul_log.comp (mehler_time_continuous hg hgb x))
  exact hlog.sub (Real.continuous_mul_log.comp hmass)

@[simp]
theorem entropyTrajectory_zero (g : ℝ → ℝ) :
    entropyTrajectory g 0 = entropyDensity g := by
  simp only [entropyTrajectory, GaussianMehler.mehler_zero]

/-- In particular the limit at zero, including the right-hand limit, is the input entropy. -/
theorem entropyTrajectory_tendsto_zero_time {g : ℝ → ℝ} (hg : Continuous g)
    {M : ℝ} (hgb : ∀ x, ‖g x‖ ≤ M) :
    Tendsto (entropyTrajectory g) (𝓝 0) (𝓝 (entropyDensity g)) := by
  simpa only [entropyTrajectory_zero] using (entropyTrajectory_continuous hg hgb).tendsto 0

/-- Invariance removes only the centered mean term, with integrability proved separately. -/
theorem entropyTrajectory_eq_invariant_mean {g : ℝ → ℝ} (hg : Continuous g)
    {M : ℝ} (hgb : ∀ x, ‖g x‖ ≤ M) (t : ℝ) (ht : 0 ≤ t) :
    entropyTrajectory g t =
      (∫ x, GaussianMehler.mehler t g x * Real.log (GaussianMehler.mehler t g x) ∂γ) -
        (∫ x, g x ∂γ) * Real.log (∫ x, g x ∂γ) := by
  unfold entropyTrajectory entropyDensity
  rw [GaussianMehler.integral_mehler hg hgb t ht]

/-- The centered entropy tends to zero: outer dominated convergence applied
separately to the density and its r log r integrand. -/
theorem entropyTrajectory_tendsto_atTop {g : ℝ → ℝ} (hg : Continuous g)
    {M : ℝ} (hgb : ∀ x, ‖g x‖ ≤ M) :
    Tendsto (entropyTrajectory g) atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := exists_mul_log_bound M
  have hmass : Tendsto (fun t => ∫ x, GaussianMehler.mehler t g x ∂γ) atTop
      (𝓝 (∫ x, g x ∂γ)) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := γ) (fun _ => M)
      (Filter.Eventually.of_forall (fun t => (GaussianMehler.mehler_integrable hg hgb t).1))
      (Filter.Eventually.of_forall (fun t => Filter.Eventually.of_forall
        (fun x => GaussianMehler.mehler_norm_le hgb t x))) (integrable_const M)
      (Filter.Eventually.of_forall (fun x => GaussianMehler.mehler_tendsto_mean hg hgb x))
    simpa using h
  have hlog : Tendsto (fun t => ∫ x, GaussianMehler.mehler t g x *
      Real.log (GaussianMehler.mehler t g x) ∂γ) atTop
      (𝓝 ((∫ x, g x ∂γ) * Real.log (∫ x, g x ∂γ))) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := γ) (fun _ => B)
      (Filter.Eventually.of_forall (fun t => (entropyTrajectory_integrable hg hgb t).2.1))
      (Filter.Eventually.of_forall (fun t => Filter.Eventually.of_forall
        (fun x => hB _ (GaussianMehler.mehler_norm_le hgb t x)))) (integrable_const B)
      (Filter.Eventually.of_forall (fun x => Real.continuous_mul_log.continuousAt.tendsto.comp
        (GaussianMehler.mehler_tendsto_mean hg hgb x)))
    simpa using h
  change Tendsto (fun t => entropyDensity (GaussianMehler.mehler t g)) atTop (𝓝 0)
  simpa [entropyDensity, Function.comp_def] using
    hlog.sub (Real.continuous_mul_log.continuousAt.tendsto.comp hmass)

end OperatorDerivativeRewrite.Foundation.GaussianEntropyDissipation
