import Foundation.SPDEModulatedResponse

/-! Exact covariance and forcing-multiplier sensitivity for scalar stochastic evolution. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace OperatorDerivativeRewrite.Foundation.SPDEModulatedSensitivity
open SPDEModulatedResponse FractionalForcingKernel
open GaussianTimeHilbert InfiniteGaussian GaussianHilbertProcess
attribute [local instance] timeHilbert_secondCountable

theorem modulated_cross_moment (α : ℝ) (hα : 1 / 2 < α)
    (t : ℝ≥0) (g h : ℝ → ℝ) (hg : Measurable g) (hh : Measurable h)
    (Mg Mh : ℝ) (hgM : ∀ s, |g s| ≤ Mg) (hhM : ∀ s, |h s| ≤ Mh) :
    (∫ ω, isonormal TimeHilbert (modulatedVector α hα t g hg Mg hgM) ω *
      isonormal TimeHilbert (modulatedVector α hα t h hh Mh hhM) ω ∂gaussianProduct) =
      ∫ s, modulatedResponse α t g s * modulatedResponse α t h s := by
  rw [isonormal_product_integral, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [modulatedVector_coeFn α hα t g hg Mg hgM,
    modulatedVector_coeFn α hα t h hh Mh hhM] with s hgs hhs
  simp [hgs, hhs, mul_comm]

theorem modulatedVector_sub (α : ℝ) (hα : 1 / 2 < α)
    (t : ℝ≥0) (g h : ℝ → ℝ) (hg : Measurable g) (hh : Measurable h)
    (Mg Mh δ : ℝ) (hgM : ∀ s, |g s| ≤ Mg) (hhM : ∀ s, |h s| ≤ Mh)
    (hdiff : ∀ s, |g s - h s| ≤ δ) :
    modulatedVector α hα t g hg Mg hgM -
      modulatedVector α hα t h hh Mh hhM =
      modulatedVector α hα t (g - h) (hg.sub hh) δ hdiff := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (modulatedVector α hα t g hg Mg hgM)
      (modulatedVector α hα t h hh Mh hhM),
    modulatedVector_coeFn α hα t g hg Mg hgM,
    modulatedVector_coeFn α hα t h hh Mh hhM,
    modulatedVector_coeFn α hα t (g - h) (hg.sub hh) δ hdiff] with s hs hgs hhs hdiffs
  rw [hs]
  simp only [Pi.sub_apply]
  rw [hgs, hhs, hdiffs]
  simp only [modulatedResponse, Pi.sub_apply]
  ring

theorem stochasticModulatedResponse_sub (α : ℝ) (hα : 1 / 2 < α)
    (t : ℝ≥0) (g h : ℝ → ℝ) (hg : Measurable g) (hh : Measurable h)
    (Mg Mh δ : ℝ) (hgM : ∀ s, |g s| ≤ Mg) (hhM : ∀ s, |h s| ≤ Mh)
    (hdiff : ∀ s, |g s - h s| ≤ δ) :
    stochasticModulatedResponse α hα t g hg Mg hgM -
      stochasticModulatedResponse α hα t h hh Mh hhM =
      stochasticModulatedResponse α hα t (g - h) (hg.sub hh) δ hdiff := by
  change isonormalEmbedding TimeHilbert _ - isonormalEmbedding TimeHilbert _ = _
  rw [← map_sub, modulatedVector_sub α hα t g h hg hh Mg Mh δ hgM hhM hdiff]
  rfl

theorem stochasticModulatedResponse_error_sq (α : ℝ) (hα : 1 / 2 < α)
    (t : ℝ≥0) (g h : ℝ → ℝ) (hg : Measurable g) (hh : Measurable h)
    (Mg Mh δ : ℝ) (hgM : ∀ s, |g s| ≤ Mg) (hhM : ∀ s, |h s| ≤ Mh)
    (hdiff : ∀ s, |g s - h s| ≤ δ) :
    ‖stochasticModulatedResponse α hα t g hg Mg hgM -
      stochasticModulatedResponse α hα t h hh Mh hhM‖ ^ 2 =
      ∫ s, ((g s - h s) * response α t s)^2 := by
  rw [stochasticModulatedResponse_sub α hα t g h hg hh Mg Mh δ hgM hhM hdiff,
    stochasticModulatedResponse_energy]
  rfl

theorem stochasticModulatedResponse_error_le (α : ℝ) (hα : 1 / 2 < α)
    (t : ℝ≥0) (g h : ℝ → ℝ) (hg : Measurable g) (hh : Measurable h)
    (Mg Mh δ : ℝ) (hgM : ∀ s, |g s| ≤ Mg) (hhM : ∀ s, |h s| ≤ Mh)
    (hdiff : ∀ s, |g s - h s| ≤ δ) :
    ‖stochasticModulatedResponse α hα t g hg Mg hgM -
      stochasticModulatedResponse α hα t h hh Mh hhM‖ ^ 2 ≤
      δ^2 * ((t : ℝ)^(2 * α - 1) / ((Real.Gamma α)^2 * (2 * α - 1))) := by
  rw [stochasticModulatedResponse_sub α hα t g h hg hh Mg Mh δ hgM hhM hdiff]
  exact stochasticModulatedResponse_energy_le α hα t (g - h) (hg.sub hh) δ hdiff

/-- Uniform approximation of deterministic response multipliers transfers to
mean-square convergence of their actual Brownian stochastic integrals. -/
theorem stochasticModulatedResponse_tendsto
    (α : ℝ) (hα : 1 / 2 < α) (t : ℝ≥0)
    (g : ℕ → ℝ → ℝ) (h : ℝ → ℝ)
    (hg : ∀ n, Measurable (g n)) (hh : Measurable h)
    (Mg : ℕ → ℝ) (Mh : ℝ)
    (hgM : ∀ n s, |g n s| ≤ Mg n) (hhM : ∀ s, |h s| ≤ Mh)
    (δ : ℕ → ℝ)
    (hdiff : ∀ n s, |g n s - h s| ≤ δ n)
    (hδ : Filter.Tendsto δ Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => stochasticModulatedResponse α hα t (g n) (hg n) (Mg n) (hgM n))
      Filter.atTop
      (nhds (stochasticModulatedResponse α hα t h hh Mh hhM)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  let C := (t : ℝ)^(2 * α - 1) / ((Real.Gamma α)^2 * (2 * α - 1))
  have hbound (n : ℕ) :
      ‖stochasticModulatedResponse α hα t (g n) (hg n) (Mg n) (hgM n) -
        stochasticModulatedResponse α hα t h hh Mh hhM‖ ^ 2 ≤
        (δ n)^2 * C :=
    stochasticModulatedResponse_error_le α hα t (g n) h (hg n) hh
      (Mg n) Mh (δ n) (hgM n) hhM (hdiff n)
  have hlim : Filter.Tendsto (fun n => (δ n)^2 * C) Filter.atTop (nhds 0) := by
    simpa using (hδ.pow 2).mul_const C
  have hsq : Filter.Tendsto
      (fun n => ‖stochasticModulatedResponse α hα t (g n) (hg n) (Mg n) (hgM n) -
        stochasticModulatedResponse α hα t h hh Mh hhM‖ ^ 2)
      Filter.atTop (nhds 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => sq_nonneg _) hbound
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)] using hroot

end OperatorDerivativeRewrite.Foundation.SPDEModulatedSensitivity
