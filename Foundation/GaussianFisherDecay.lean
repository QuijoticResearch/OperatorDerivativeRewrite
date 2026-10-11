/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Copyright (c) 2026 OperatorDerivativeRewrite contributors.
Portions adapted from MarkovSemigroups/Instances/WorkInProgress/Euclidean.lean
and MarkovSemigroups/General/OUEntropyDecomposition.lean, namespace Gaussian1D,
by Michael R. Douglas and contributors, commit
acf649108ea2222f4a8544a2782f448cb502492a (Apache License 2.0).
See LICENSES/Apache-2.0.txt and MATHEMATICAL_AUDIT.md for attribution and scope.
-/
import Foundation.GaussianMehler

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Fisher information decay for the concrete one-dimensional Mehler kernel. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter Set Real ProbabilityTheory Topology
open scoped ContDiff ENNReal

namespace OperatorDerivativeRewrite.Foundation.GaussianFisher

abbrev γ : Measure ℝ := GaussianMehler.γ

/-- Fisher information of a positive density. Its integrability is established
below under explicit C¹ and uniform bound hypotheses. -/
def fisherInformation (g : ℝ → ℝ) : ℝ :=
  ∫ y, (deriv g y) ^ 2 / g y ∂γ

/-- The Fisher integrand is genuinely integrable under a positive lower
bound and a uniform derivative bound. -/
theorem fisherInformation_integrable {g : ℝ → ℝ} {ε M : ℝ}
    (hε : 0 < ε) (hg : Measurable g) (hdg : Measurable (deriv g))
    (hlo : ∀ x, ε ≤ g x) (hdb : ∀ x, |deriv g x| ≤ M) :
    Integrable (fun x => (deriv g x) ^ 2 / g x) γ := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hdb 0)
  have hbound : ∀ x, ‖(deriv g x) ^ 2 / g x‖ ≤ M ^ 2 / ε := by
    intro x
    have hpos : 0 < g x := lt_of_lt_of_le hε (hlo x)
    have hs : (deriv g x) ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs (deriv g x)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hdb x) 2
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hpos.le)]
    exact (div_le_div_of_nonneg_left (sq_nonneg _) hε (hlo x)).trans
      (div_le_div_of_nonneg_right hs hε.le)
  exact GaussianMehler.integrable_comp_of_bounded
    ((hdg.pow_const 2).div hg) hbound measurable_id

/-- Differentiate the actual Mehler integral for a C¹ function with bounded
function and derivative. -/
theorem hasDerivAt_mehler_C1 (t : ℝ) {f : ℝ → ℝ}
    (hf_C1 : ContDiff ℝ 1 f) {M : ℝ}
    (hf_bd : ∀ x, ‖f x‖ ≤ M) (hf'_bd : ∀ x, ‖deriv f x‖ ≤ M)
    (x₀ : ℝ) :
    HasDerivAt (GaussianMehler.mehler t f)
      (Real.exp (-t) * GaussianMehler.mehler t (deriv f) x₀) x₀ := by
  set a := Real.exp (-t)
  set b := Real.sqrt (1 - Real.exp (-2 * t))
  set F : ℝ → ℝ → ℝ := fun x y => f (a * x + b * y)
  set F' : ℝ → ℝ → ℝ := fun x y => a * deriv f (a * x + b * y)
  set bound : ℝ → ℝ := fun _ => |a| * M
  have hs : Set.Ioo (x₀ - 1) (x₀ + 1) ∈ nhds x₀ :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hf_meas : Measurable f := hf_C1.continuous.measurable
  have hF_meas : ∀ x, AEStronglyMeasurable (F x) γ := by
    intro x
    refine (hf_meas.comp ?_).aestronglyMeasurable
    exact measurable_const.add (measurable_const.mul measurable_id)
  have hF_int : Integrable (F x₀) γ := by
    refine Integrable.mono' (integrable_const M) (hF_meas x₀) ?_
    filter_upwards with y; exact hf_bd (a * x₀ + b * y)
  have hf'_meas : Measurable (deriv f) :=
    (hf_C1.continuous_deriv (by simp)).measurable
  have hF'_meas : AEStronglyMeasurable (F' x₀) γ := by
    refine (measurable_const.mul ?_).aestronglyMeasurable
    exact hf'_meas.comp (measurable_const.add (measurable_const.mul measurable_id))
  have h_bound : ∀ᵐ y ∂γ, ∀ x ∈ Set.Ioo (x₀ - 1) (x₀ + 1),
      ‖F' x y‖ ≤ bound y := by
    filter_upwards with y x _
    change ‖a * deriv f (a * x + b * y)‖ ≤ |a| * M
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |deriv f (a * x + b * y)| ≤ M := by
      rw [← Real.norm_eq_abs]; exact hf'_bd _
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg a)
  have h_bound_int : Integrable bound γ := integrable_const _
  have h_diff : ∀ᵐ y ∂γ, ∀ x ∈ Set.Ioo (x₀ - 1) (x₀ + 1),
      HasDerivAt (F · y) (F' x y) x := by
    filter_upwards with y x _
    change HasDerivAt (fun x => f (a * x + b * y)) (a * deriv f (a * x + b * y)) x
    have h_inner : HasDerivAt (fun x => a * x + b * y) a x := by
      simpa using ((hasDerivAt_id x).const_mul a).add_const (b * y)
    have h_f : HasDerivAt f (deriv f (a * x + b * y)) (a * x + b * y) :=
      (hf_C1.differentiable (by simp)).differentiableAt.hasDerivAt
    have := h_f.comp x h_inner
    simpa only [Function.comp_def, mul_comm] using this
  obtain ⟨_, h_deriv⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
      (Filter.Eventually.of_forall hF_meas) hF_int hF'_meas h_bound h_bound_int h_diff
  have h_lhs_eq : (fun x => ∫ y, F x y ∂γ) = GaussianMehler.mehler t f := rfl
  have h_rhs_eq : ∫ y, F' x₀ y ∂γ = Real.exp (-t) * GaussianMehler.mehler t (deriv f) x₀ := by
    change ∫ y, a * deriv f (a * x₀ + b * y) ∂γ = a * GaussianMehler.mehler t (deriv f) x₀
    rw [integral_const_mul]; rfl
  rw [← h_lhs_eq, ← h_rhs_eq]
  exact h_deriv


/-- The derivative of the Mehler evolution is the contracted Mehler
average of the actual derivative. -/
theorem deriv_mehler_C1 (t : ℝ) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) {M : ℝ}
    (hgb : ∀ x, ‖g x‖ ≤ M) (hdgb : ∀ x, ‖deriv g x‖ ≤ M) (x : ℝ) :
    deriv (GaussianMehler.mehler t g) x =
      Real.exp (-t) * GaussianMehler.mehler t (deriv g) x :=
  (hasDerivAt_mehler_C1 t hg hgb hdgb x).deriv

/-- A positive lower bound survives the Mehler averaging. -/
theorem mehler_lower_bound {g : ℝ → ℝ} (hg : Continuous g)
    {ε M : ℝ} (hε : 0 < ε) (hgb : ∀ x, ‖g x‖ ≤ M)
    (hlo : ∀ x, ε ≤ g x) (t x : ℝ) :
    ε ≤ GaussianMehler.mehler t g x := by
  have hconst : ∀ z : ℝ, ‖(fun _ : ℝ => ε) z‖ ≤ ε := by
    intro z
    simp [Real.norm_eq_abs, abs_of_pos hε]
  have h := GaussianMehler.mehler_mono continuous_const hg hconst hgb hlo t x
  simpa [GaussianMehler.mehler_const] using h

/-- Gaussian Cauchy–Schwarz with explicit integrability of every moment. -/
lemma cauchy_schwarz_gamma (A B : ℝ → ℝ)
    (hAB : Integrable (fun y => A y * B y) γ)
    (hA2 : Integrable (fun y => A y ^ 2) γ)
    (hB2 : Integrable (fun y => B y ^ 2) γ) :
    (∫ y, A y * B y ∂γ) ^ 2 ≤ (∫ y, A y ^ 2 ∂γ) * (∫ y, B y ^ 2 ∂γ) := by
  set IA := ∫ y, A y ^ 2 ∂γ with hIA
  set IB := ∫ y, B y ^ 2 ∂γ with hIB
  set IAB := ∫ y, A y * B y ∂γ with hIAB
  have hIA_nn : 0 ≤ IA :=
    integral_nonneg (fun y => sq_nonneg _)
  have hIB_nn : 0 ≤ IB :=
    integral_nonneg (fun y => sq_nonneg _)
  by_cases hIB0 : IB = 0
  · -- If ∫B² = 0, then B = 0 a.e., so ∫A·B = 0.
    have hB_ae : (fun y => B y ^ 2) =ᵐ[γ] 0 := by
      have h_nn_ae : ∀ᵐ y ∂γ, 0 ≤ B y ^ 2 :=
        Filter.Eventually.of_forall (fun y => sq_nonneg _)
      exact (integral_eq_zero_iff_of_nonneg_ae h_nn_ae hB2).mp hIB0
    have hAB_ae : (fun y => A y * B y) =ᵐ[γ] 0 := by
      filter_upwards [hB_ae] with y hy
      have : B y = 0 := sq_eq_zero_iff.mp hy
      simp [this]
    have hIAB0 : IAB = 0 := by
      rw [hIAB]; exact integral_eq_zero_of_ae hAB_ae
    rw [hIAB0, hIB0]; simp
  · have hIB_pos : 0 < IB := lt_of_le_of_ne hIB_nn (Ne.symm hIB0)
    -- Optimal λ := IAB / IB makes ∫(A - λB)² = IA - IAB²/IB ≥ 0.
    set lam : ℝ := IAB / IB with h_lam_def
    have h_expand : ∫ y, (A y - lam * B y) ^ 2 ∂γ
        = IA - 2 * lam * IAB + lam ^ 2 * IB := by
      have h_eq : ∀ y, (A y - lam * B y) ^ 2
          = A y ^ 2 - 2 * lam * (A y * B y) + lam ^ 2 * B y ^ 2 := fun y => by ring
      have h_sum_int :
          Integrable (fun y => A y ^ 2 - 2 * lam * (A y * B y) + lam ^ 2 * B y ^ 2) γ :=
        (hA2.sub (hAB.const_mul (2 * lam))).add (hB2.const_mul (lam ^ 2))
      calc ∫ y, (A y - lam * B y) ^ 2 ∂γ
          = ∫ y, A y ^ 2 - 2 * lam * (A y * B y) + lam ^ 2 * B y ^ 2 ∂γ :=
            integral_congr_ae (Filter.Eventually.of_forall h_eq)
        _ = (∫ y, A y ^ 2 - 2 * lam * (A y * B y) ∂γ) + ∫ y, lam ^ 2 * B y ^ 2 ∂γ :=
            integral_add (hA2.sub (hAB.const_mul (2 * lam))) (hB2.const_mul (lam ^ 2))
        _ = ((∫ y, A y ^ 2 ∂γ) - ∫ y, 2 * lam * (A y * B y) ∂γ)
            + ∫ y, lam ^ 2 * B y ^ 2 ∂γ := by
            rw [integral_sub hA2 (hAB.const_mul (2 * lam))]
        _ = IA - 2 * lam * IAB + lam ^ 2 * IB := by
            rw [integral_const_mul, integral_const_mul]
    have h_nn : 0 ≤ ∫ y, (A y - lam * B y) ^ 2 ∂γ :=
      integral_nonneg (fun y => sq_nonneg _)
    rw [h_expand] at h_nn
    -- Rewrite h_nn entirely in terms of IAB²/IB.
    have h_nn' : 0 ≤ IA - IAB ^ 2 / IB := by
      have h_alg : IA - 2 * lam * IAB + lam ^ 2 * IB = IA - IAB ^ 2 / IB := by
        rw [h_lam_def]; field_simp; ring
      linarith [h_alg ▸ h_nn]
    have h_step : IAB ^ 2 / IB ≤ IA := by linarith
    have := mul_le_mul_of_nonneg_right h_step hIB_nn
    rwa [div_mul_cancel₀ _ hIB0] at this


/-- Weighted Cauchy–Schwarz for the Mehler probability kernel. All
kernel integrals have bounded measurable integrands and the denominator is
strictly positive. -/
theorem weighted_cauchy_schwarz_mehler
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    {ε M : ℝ} (hε : 0 < ε)
    (hg_lo : ∀ x, ε ≤ g x) (hg_hi : ∀ x, g x ≤ M)
    (hg'_bd : ∀ x, |deriv g x| ≤ M)
    (t : ℝ) (_ht : 0 ≤ t) (x : ℝ) :
    (GaussianMehler.mehler t (deriv g) x) ^ 2 / GaussianMehler.mehler t g x ≤
      GaussianMehler.mehler t (fun y => (deriv g y) ^ 2 / g y) x := by
  -- Notation
  set a := Real.exp (-t) with ha_def
  set b := Real.sqrt (1 - Real.exp (-2 * t)) with hb_def
  -- Basic facts
  have hε_nn : 0 ≤ ε := hε.le
  have h_gpos : ∀ x, 0 < g x := fun x => lt_of_lt_of_le hε (hg_lo x)
  have h_gabs : ∀ x, |g x| ≤ M := fun x => by
    rw [abs_of_pos (h_gpos x)]; exact hg_hi x
  have hg_norm : ∀ x, ‖g x‖ ≤ M := fun x => by
    rw [Real.norm_eq_abs]; exact h_gabs x
  have hg'_norm : ∀ x, ‖deriv g x‖ ≤ M := fun x => by
    rw [Real.norm_eq_abs]; exact hg'_bd x
  -- Measurability
  have hg_meas : Measurable g := hg.continuous.measurable
  have hg'_meas : Measurable (deriv g) :=
    (hg.continuous_deriv le_rfl).measurable
  -- Linear inner map (a*x + b*y), measurable in y for fixed x.
  -- Set the integrand functions for each fixed x.
  -- P_t g x ≥ ε.
  have h_Ptg_lo : ∀ x, ε ≤ GaussianMehler.mehler t g x := by
    intro x
    change ε ≤ ∫ y, g (a * x + b * y) ∂γ
    have h_int : Integrable (fun y => g (a * x + b * y)) γ := by
      refine Integrable.mono' (integrable_const M) ?_ ?_
      · exact (hg_meas.comp
          (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable
      · filter_upwards with y; exact hg_norm _
    have h_le : ∀ y, (ε : ℝ) ≤ g (a * x + b * y) := fun y => hg_lo _
    calc (ε : ℝ) = ∫ _, ε ∂γ := by simp
      _ ≤ ∫ y, g (a * x + b * y) ∂γ :=
            integral_mono (integrable_const _) h_int h_le
  have h_Ptg_pos : ∀ x, 0 < GaussianMehler.mehler t g x := fun x =>
    lt_of_lt_of_le hε (h_Ptg_lo x)
  -- Integrability of (g')²/g composed with kernel, over γ.prod γ.
  -- Bound: |g'|² / g ≤ M² / ε since |g'| ≤ M, g ≥ ε.
  have h_qsq_over_r_bd : ∀ x, (deriv g x) ^ 2 / g x ≤ M ^ 2 / ε := by
    intro x
    have h1 : (deriv g x) ^ 2 ≤ M ^ 2 := by
      have hxabs : |deriv g x| ≤ M := hg'_bd x
      have : (deriv g x) ^ 2 = |deriv g x| ^ 2 := by rw [sq_abs]
      rw [this]
      exact pow_le_pow_left₀ (abs_nonneg _) hxabs 2
    have h2 : (deriv g x) ^ 2 / g x ≤ (deriv g x) ^ 2 / ε :=
      div_le_div_of_nonneg_left (sq_nonneg _) hε (hg_lo x)
    have h3 : (deriv g x) ^ 2 / ε ≤ M ^ 2 / ε :=
      div_le_div_of_nonneg_right h1 hε_nn
    linarith
  have h_qsq_over_r_nn : ∀ x, 0 ≤ (deriv g x) ^ 2 / g x := fun x =>
    div_nonneg (sq_nonneg _) (h_gpos x).le
  -- Measurability of (deriv g y)² / g y.
  have h_qsq_over_r_meas : Measurable (fun y => (deriv g y) ^ 2 / g y) :=
    (hg'_meas.pow_const 2).div hg_meas
  -- The pointwise Cauchy-Schwarz bound:
  -- (∫ Q dγ)² ≤ (∫ Q²/R dγ) · (∫ R dγ)
  -- where Q(y) := g'(a*x + b*y), R(y) := g(a*x + b*y).
  -- Apply with A := Q/√R, B := √R; then A·B = Q, A² = Q²/R, B² = R.
  -- We need integrability of these functions.
  have h_cauchy : ∀ x,
      (GaussianMehler.mehler t (deriv g) x) ^ 2 ≤
        GaussianMehler.mehler t (fun y => (deriv g y) ^ 2 / g y) x *
          GaussianMehler.mehler t g x := by
    intro x
    -- Define A(y) := g'(a*x+b*y) / √(g(a*x+b*y)), B(y) := √(g(a*x+b*y))
    -- and apply cauchy_schwarz_gamma.
    set A : ℝ → ℝ := fun y => deriv g (a * x + b * y) / Real.sqrt (g (a * x + b * y))
    set B : ℝ → ℝ := fun y => Real.sqrt (g (a * x + b * y))
    have h_compose_pos : ∀ y, 0 < g (a * x + b * y) := fun y => h_gpos _
    have h_sqrt_pos : ∀ y, 0 < Real.sqrt (g (a * x + b * y)) := fun y =>
      Real.sqrt_pos.mpr (h_compose_pos y)
    have h_sqrt_sq : ∀ y, (Real.sqrt (g (a * x + b * y))) ^ 2 = g (a * x + b * y) := fun y =>
      Real.sq_sqrt (h_compose_pos y).le
    have h_AB : ∀ y, A y * B y = deriv g (a * x + b * y) := by
      intro y
      change (deriv g (a * x + b * y) / Real.sqrt (g (a * x + b * y))) *
          Real.sqrt (g (a * x + b * y)) = deriv g (a * x + b * y)
      have hsqrt_ne : Real.sqrt (g (a * x + b * y)) ≠ 0 := (h_sqrt_pos y).ne'
      field_simp
    have h_A2 : ∀ y, A y ^ 2 = (deriv g (a * x + b * y)) ^ 2 / g (a * x + b * y) := by
      intro y
      change (deriv g (a * x + b * y) / Real.sqrt (g (a * x + b * y))) ^ 2
          = (deriv g (a * x + b * y)) ^ 2 / g (a * x + b * y)
      rw [div_pow, h_sqrt_sq]
    have h_B2 : ∀ y, B y ^ 2 = g (a * x + b * y) := h_sqrt_sq
    -- Measurability of A, B.
    have h_kernel_meas : Measurable (fun y => a * x + b * y) :=
      measurable_const.add (measurable_const.mul measurable_id)
    have h_sqrt_meas : Measurable Real.sqrt := Real.continuous_sqrt.measurable
    have hA_meas : Measurable A :=
      (hg'_meas.comp h_kernel_meas).div (h_sqrt_meas.comp (hg_meas.comp h_kernel_meas))
    have hB_meas : Measurable B :=
      h_sqrt_meas.comp (hg_meas.comp h_kernel_meas)
    -- Integrability.
    have h_AB_int : Integrable (fun y => A y * B y) γ := by
      refine Integrable.mono' (integrable_const M)
        (hA_meas.mul hB_meas).aestronglyMeasurable ?_
      filter_upwards with y
      rw [h_AB]
      exact hg'_norm _
    have h_A2_int : Integrable (fun y => A y ^ 2) γ := by
      refine Integrable.mono' (integrable_const (M ^ 2 / ε)) ?_ ?_
      · exact (hA_meas.pow_const 2).aestronglyMeasurable
      · filter_upwards with y
        rw [Real.norm_eq_abs, abs_of_nonneg (by rw [h_A2]; exact h_qsq_over_r_nn _)]
        rw [h_A2]
        exact h_qsq_over_r_bd _
    have h_B2_int : Integrable (fun y => B y ^ 2) γ := by
      refine Integrable.mono' (integrable_const M) ?_ ?_
      · exact (hB_meas.pow_const 2).aestronglyMeasurable
      · filter_upwards with y
        rw [h_B2, Real.norm_eq_abs]
        exact h_gabs _
    have hCS := cauchy_schwarz_gamma A B h_AB_int h_A2_int h_B2_int
    -- Rewrite using h_AB, h_A2, h_B2.
    have h_lhs : (∫ y, A y * B y ∂γ) ^ 2 = (GaussianMehler.mehler t (deriv g) x) ^ 2 := by
      congr 1
      change ∫ y, A y * B y ∂γ = ∫ y, deriv g (a * x + b * y) ∂γ
      exact integral_congr_ae (Filter.Eventually.of_forall h_AB)
    have h_rhs_A2 : ∫ y, A y ^ 2 ∂γ
        = GaussianMehler.mehler t (fun y => (deriv g y) ^ 2 / g y) x := by
      change ∫ y, A y ^ 2 ∂γ = ∫ y, (deriv g (a * x + b * y)) ^ 2 / g (a * x + b * y) ∂γ
      exact integral_congr_ae (Filter.Eventually.of_forall h_A2)
    have h_rhs_B2 : ∫ y, B y ^ 2 ∂γ = GaussianMehler.mehler t g x := by
      change ∫ y, B y ^ 2 ∂γ = ∫ y, g (a * x + b * y) ∂γ
      exact integral_congr_ae (Filter.Eventually.of_forall h_B2)
    rw [h_lhs, h_rhs_A2, h_rhs_B2] at hCS
    exact hCS
  exact (div_le_iff₀ (h_Ptg_pos x)).2 (h_cauchy x)

/-- The Fisher integrand of the Mehler evolution is integrable. -/
theorem fisherInformation_mehler_integrable
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    {ε M : ℝ} (hε : 0 < ε)
    (hg_lo : ∀ x, ε ≤ g x) (hg_hi : ∀ x, g x ≤ M)
    (hg'_bd : ∀ x, |deriv g x| ≤ M)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun x => (deriv (GaussianMehler.mehler t g) x) ^ 2 /
      GaussianMehler.mehler t g x) γ := by
  have hM : 0 ≤ M := le_trans hε.le ((hg_lo 0).trans (hg_hi 0))
  have hg_norm : ∀ x, ‖g x‖ ≤ M := by
    intro x
    rw [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hε (hg_lo x))]
    exact hg_hi x
  have hdg_norm : ∀ x, ‖deriv g x‖ ≤ M := by
    intro x
    simpa [Real.norm_eq_abs] using hg'_bd x
  have hPlo : ∀ x, ε ≤ GaussianMehler.mehler t g x :=
    fun x => mehler_lower_bound hg.continuous hε hg_norm hg_lo t x
  have hPmeas : Measurable (GaussianMehler.mehler t g) :=
    (GaussianMehler.mehler_continuous hg.continuous hg_norm t).measurable
  have hdgcont : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hPdmeas : Measurable (GaussianMehler.mehler t (deriv g)) :=
    (GaussianMehler.mehler_continuous hdgcont hdg_norm t).measurable
  have hdPeq : ∀ x, deriv (GaussianMehler.mehler t g) x =
      Real.exp (-t) * GaussianMehler.mehler t (deriv g) x :=
    fun x => (hasDerivAt_mehler_C1 t hg hg_norm hdg_norm x).deriv
  have hdPmeas : Measurable (deriv (GaussianMehler.mehler t g)) := by
    have heq : deriv (GaussianMehler.mehler t g) =
        fun x => Real.exp (-t) * GaussianMehler.mehler t (deriv g) x :=
      funext hdPeq
    rw [heq]
    exact measurable_const.mul hPdmeas
  have ha_nn : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have ha_le : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hdPbound : ∀ x, |deriv (GaussianMehler.mehler t g) x| ≤ M := by
    intro x
    rw [hdPeq x, abs_mul, abs_of_nonneg ha_nn]
    have h := GaussianMehler.mehler_norm_le hdg_norm t x
    rw [Real.norm_eq_abs] at h
    nlinarith
  exact fisherInformation_integrable hε hPmeas hdPmeas hPlo hdPbound

/-- Fisher information contracts at the Ornstein–Uhlenbeck rate. -/
theorem fisherInformation_decay
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    {ε M : ℝ} (hε : 0 < ε)
    (hg_lo : ∀ x, ε ≤ g x) (hg_hi : ∀ x, g x ≤ M)
    (hg'_bd : ∀ x, |deriv g x| ≤ M)
    (t : ℝ) (ht : 0 ≤ t) :
    fisherInformation (GaussianMehler.mehler t g) ≤
      Real.exp (-2 * t) * fisherInformation g := by
  have hM : 0 ≤ M := le_trans hε.le ((hg_lo 0).trans (hg_hi 0))
  have hg_norm : ∀ x, ‖g x‖ ≤ M := by
    intro x
    rw [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hε (hg_lo x))]
    exact hg_hi x
  have hdg_norm : ∀ x, ‖deriv g x‖ ≤ M := by
    intro x
    simpa [Real.norm_eq_abs] using hg'_bd x
  let φ : ℝ → ℝ := fun x => (deriv g x) ^ 2 / g x
  have hφcont : Continuous φ := by
    change Continuous (fun x => (deriv g x) ^ 2 / g x)
    exact ((hg.continuous_deriv le_rfl).pow 2).div hg.continuous
      (fun x => (lt_of_lt_of_le hε (hg_lo x)).ne')
  have hφnorm : ∀ x, ‖φ x‖ ≤ M ^ 2 / ε := by
    intro x
    have hpos : 0 < g x := lt_of_lt_of_le hε (hg_lo x)
    have hs : (deriv g x) ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs (deriv g x)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hg'_bd x) 2
    change ‖(deriv g x) ^ 2 / g x‖ ≤ M ^ 2 / ε
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hpos.le)]
    exact (div_le_div_of_nonneg_left (sq_nonneg _) hε (hg_lo x)).trans
      (div_le_div_of_nonneg_right hs hε.le)
  have hφint : Integrable φ γ :=
    fisherInformation_integrable hε hg.continuous.measurable
      (hg.continuous_deriv le_rfl).measurable hg_lo hg'_bd
  have hPtφint : Integrable (GaussianMehler.mehler t φ) γ :=
    GaussianMehler.mehler_integrable hφcont hφnorm t
  have hInv := GaussianMehler.integral_mehler hφcont hφnorm t ht
  have hPint := fisherInformation_mehler_integrable g hg hε hg_lo hg_hi hg'_bd t ht
  have hpoint : ∀ x, (deriv (GaussianMehler.mehler t g) x) ^ 2 /
      GaussianMehler.mehler t g x ≤ Real.exp (-t) ^ 2 * GaussianMehler.mehler t φ x := by
    intro x
    have hd := (hasDerivAt_mehler_C1 t hg hg_norm hdg_norm x).deriv
    have hc := weighted_cauchy_schwarz_mehler g hg hε hg_lo hg_hi hg'_bd t ht x
    rw [hd]
    calc (Real.exp (-t) * GaussianMehler.mehler t (deriv g) x) ^ 2 /
          GaussianMehler.mehler t g x =
          Real.exp (-t) ^ 2 * ((GaussianMehler.mehler t (deriv g) x) ^ 2 /
            GaussianMehler.mehler t g x) := by ring
      _ ≤ Real.exp (-t) ^ 2 * GaussianMehler.mehler t φ x :=
        mul_le_mul_of_nonneg_left hc (sq_nonneg _)
  have ha_sq : Real.exp (-t) ^ 2 = Real.exp (-2 * t) := by
    rw [show (-2 * t : ℝ) = -t + -t by ring, Real.exp_add]
    ring
  unfold fisherInformation
  calc ∫ x, (deriv (GaussianMehler.mehler t g) x) ^ 2 /
        GaussianMehler.mehler t g x ∂γ
      ≤ ∫ x, Real.exp (-t) ^ 2 * GaussianMehler.mehler t φ x ∂γ :=
        integral_mono hPint (hPtφint.const_mul _) hpoint
    _ = Real.exp (-t) ^ 2 * ∫ x, GaussianMehler.mehler t φ x ∂γ := by
        rw [integral_const_mul]
    _ = Real.exp (-t) ^ 2 * ∫ x, φ x ∂γ := by rw [hInv]
    _ = Real.exp (-2 * t) * ∫ x, (deriv g x) ^ 2 / g x ∂γ := by
        rw [ha_sq]


end OperatorDerivativeRewrite.Foundation.GaussianFisher
