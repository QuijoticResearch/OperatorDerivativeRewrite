import Foundation.GaussianLocalSobolev
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.VectorMeasure.Integral

/-! Smooth Gaussian cutoffs and simultaneous value/derivative L² convergence. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace OperatorDerivativeRewrite.Foundation.GaussianSobolevCutoffs
abbrev γ : Measure ℝ := GaussianCore.γ
private def bump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
def cutoff (n : ℕ) (x : ℝ) : ℝ := bump (x / ((n : ℝ) + 1))
def truncated (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ := cutoff n x * f x
private theorem scale_pos (n : ℕ) : (0 : ℝ) < (n : ℝ) + 1 := by positivity
theorem cutoff_contDiff (n : ℕ) : ContDiff ℝ ∞ (cutoff n) := by
  change ContDiff ℝ ∞ ((bump : ℝ → ℝ) ∘ fun x : ℝ => x / ((n : ℝ) + 1))
  exact bump.contDiff.comp (by fun_prop)
theorem cutoff_compact (n : ℕ) : HasCompactSupport (cutoff n) := by
  have hb := bump.hasCompactSupport
  have hs := hb.comp_smul (show ((n : ℝ) + 1)⁻¹ ≠ 0 by positivity)
  convert hs using 1
  ext x
  simp [cutoff, smul_eq_mul, div_eq_mul_inv, mul_comm]
theorem truncated_compact (f : ℝ → ℝ) (n : ℕ) : HasCompactSupport (truncated f n) := by
  change HasCompactSupport (cutoff n * f)
  exact (cutoff_compact n).mul_right
theorem cutoff_bounds (n : ℕ) (x : ℝ) : 0 ≤ cutoff n x ∧ cutoff n x ≤ 1 := by
  exact ⟨bump.nonneg, bump.le_one⟩
private theorem cutoff_deriv_bound_exists : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |deriv (bump : ℝ → ℝ) x| ≤ C := by
  have hb : ContDiff ℝ ∞ (bump : ℝ → ℝ) := bump.contDiff
  have hc : Continuous (deriv (bump : ℝ → ℝ)) := hb.continuous_deriv (by norm_num)
  have hs : HasCompactSupport (deriv (bump : ℝ → ℝ)) := bump.hasCompactSupport.deriv
  obtain ⟨C, hC⟩ := hc.abs.bddAbove_range_of_hasCompactSupport hs.abs
  refine ⟨max C 0, le_max_right .., ?_⟩
  intro x
  exact (hC (mem_range_self x)).trans (le_max_left ..)


private theorem hasDerivAt_cutoff (n : ℕ) (x : ℝ) :
    HasDerivAt (cutoff n) (deriv (bump : ℝ → ℝ) (x / ((n : ℝ) + 1)) / ((n : ℝ) + 1)) x := by
  have hcont : ContDiff ℝ 1 (bump : ℝ → ℝ) := bump.contDiff
  have hb : HasDerivAt (bump : ℝ → ℝ) (deriv (bump : ℝ → ℝ) (x / ((n : ℝ) + 1)))
      (x / ((n : ℝ) + 1)) := (hcont.differentiable (by norm_num) _).hasDerivAt
  have hi : HasDerivAt (fun x : ℝ => x / ((n : ℝ) + 1)) (1 / ((n : ℝ) + 1)) x :=
    (hasDerivAt_id x).div_const _
  have hc := hb.comp x hi
  change HasDerivAt ((bump : ℝ → ℝ) ∘ fun y : ℝ => y / ((n : ℝ) + 1)) _ x
  simpa only [one_div, div_eq_mul_inv, one_mul] using hc
theorem hasDerivAt_truncated {f h : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (h x) x)
    (n : ℕ) (x : ℝ) :
    HasDerivAt (truncated f n)
      (cutoff n x * h x + deriv (cutoff n) x * f x) x := by
  have hc : HasDerivAt (cutoff n) (deriv (cutoff n) x) x :=
    ((cutoff_contDiff n).differentiable (by norm_num) x).hasDerivAt
  change HasDerivAt (cutoff n * f) _ x
  convert hc.mul (hd x) using 1; ring
theorem deriv_truncated {f h : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (h x) x)
    (n : ℕ) (x : ℝ) :
    deriv (truncated f n) x = cutoff n x * h x + deriv (cutoff n) x * f x :=
  (hasDerivAt_truncated hd n x).deriv
theorem cutoff_derivative_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n x,
      |deriv (cutoff n) x| ≤ C / ((n : ℝ) + 1) := by
  obtain ⟨C, hC, hbound⟩ := cutoff_deriv_bound_exists
  refine ⟨C, hC, ?_⟩
  intro n x
  rw [(hasDerivAt_cutoff n x).deriv, abs_div, abs_of_pos (scale_pos n)]
  exact div_le_div_of_nonneg_right (hbound _) (scale_pos n).le



private theorem scale_tendsto_zero (x : ℝ) :
    Tendsto (fun n : ℕ => x / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  simpa only [mul_zero, div_eq_mul_inv, one_mul] using
    ((tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))) :
      Tendsto (fun n : ℕ => x * (1 / ((n : ℝ) + 1))) atTop (𝓝 (x * 0)))
private theorem cutoff_tendsto_one (x : ℝ) : Tendsto (fun n : ℕ => cutoff n x) atTop (𝓝 1) := by
  have hb0 : bump (0 : ℝ) = 1 := bump.one_of_mem_closedBall (by simp [bump])
  have ht := bump.continuous.continuousAt.tendsto.comp (scale_tendsto_zero x)
  simpa only [Function.comp_def, ← hb0, cutoff] using ht
private theorem cutoff_deriv_tendsto_zero (x : ℝ) :
    Tendsto (fun n : ℕ => deriv (cutoff n) x) atTop (𝓝 0) := by
  have hcont : ContDiff ℝ 1 (bump : ℝ → ℝ) := bump.contDiff
  have hb := (hcont.continuous_deriv (by norm_num)).continuousAt.tendsto.comp (scale_tendsto_zero x)
  have hi := hb.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa [(hasDerivAt_cutoff _ _).deriv, div_eq_mul_inv] using hi


private theorem cutoff_error_sq_le (n : ℕ) (x v : ℝ) :
    ((cutoff n x - 1) * v) ^ 2 ≤ v ^ 2 := by
  obtain ⟨h0, h1⟩ := cutoff_bounds n x
  nlinarith [sq_nonneg v, sq_nonneg ((cutoff n x) * v),
    mul_nonneg (show 0 ≤ cutoff n x by exact h0) (sq_nonneg v)]
private theorem cutoff_error_sq_tendsto (v : ℝ → ℝ) (hv : Measurable v)
    (hi : Integrable (fun x => v x ^ 2) γ) :
    Tendsto (fun n : ℕ => ∫ x, ((cutoff n x - 1) * v x) ^ 2 ∂γ) atTop (𝓝 0) := by
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun x => ((cutoff n x - 1) * v x) ^ 2) γ := by
    have hm : Measurable (fun x => (cutoff n x - 1) * v x) :=
      ((cutoff_contDiff n).continuous.measurable.sub measurable_const).mul hv
    exact (hm.pow_const 2).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ x ∂γ, ‖((cutoff n x - 1) * v x) ^ 2‖ ≤ v x ^ 2 := by
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact cutoff_error_sq_le n x (v x)
  have hlim (x : ℝ) : Tendsto (fun n : ℕ => ((cutoff n x - 1) * v x) ^ 2) atTop (𝓝 0) := by
    have hsub : Tendsto (fun n : ℕ => cutoff n x - 1) atTop (𝓝 0) := by
      simpa using (cutoff_tendsto_one x).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
    have hmul := hsub.mul_const (v x)
    simpa using hmul.pow 2
  convert tendsto_integral_filter_of_dominated_convergence (fun x => v x ^ 2)
      (Filter.Eventually.of_forall hmeas) (Filter.Eventually.of_forall hbound) hi
      (Filter.Eventually.of_forall hlim) using 1; simp


private theorem derivative_cutoff_abs_le (C : ℝ)
    (hC : 0 ≤ C) (hb : ∀ x, |deriv (bump : ℝ → ℝ) x| ≤ C)
    (n : ℕ) (x : ℝ) : |deriv (cutoff n) x| ≤ C := by
  rw [(hasDerivAt_cutoff n x).deriv, abs_div, abs_of_pos (scale_pos n)]
  have hden : 1 ≤ (n : ℝ) + 1 := by have := Nat.zero_le n; exact_mod_cast (show 1 ≤ n + 1 by omega)
  have h := div_le_div_of_nonneg_right (hb (x / ((n : ℝ) + 1))) (scale_pos n).le
  exact h.trans (div_le_self hC hden)
private theorem derivative_extra_sq_le (C : ℝ)
    (hC : 0 ≤ C) (hb : ∀ x, |deriv (bump : ℝ → ℝ) x| ≤ C)
    (n : ℕ) (x v : ℝ) :
    (deriv (cutoff n) x * v) ^ 2 ≤ C ^ 2 * v ^ 2 := by
  have hh := derivative_cutoff_abs_le C hC hb n x
  have hv : 0 ≤ v ^ 2 := sq_nonneg v
  have hs : (deriv (cutoff n) x) ^ 2 ≤ C ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).2 hh
  nlinarith [mul_le_mul_of_nonneg_right hs hv]

theorem simultaneous_sq_error_tendsto {f h : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (h x) x)
    (hf_sq : Integrable (fun x => f x ^ 2) γ)
    (hh_sq : Integrable (fun x => h x ^ 2) γ) :
    (Tendsto (fun n : ℕ => ∫ x, (truncated f n x - f x) ^ 2 ∂γ) atTop (𝓝 0)) ∧
    (Tendsto (fun n : ℕ => ∫ x, (deriv (truncated f n) x - h x) ^ 2 ∂γ)
      atTop (𝓝 0)) := by
  have hfcont : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hh_meas : Measurable h := by
    rw [GaussianLocalSobolev.derivative_eq_deriv hd]
    exact measurable_deriv f
  constructor
  · have ht := cutoff_error_sq_tendsto f hfcont.measurable hf_sq
    convert ht using 1
    funext n
    congr 1
    funext x
    simp [truncated]
    ring
  · obtain ⟨C, hC, hb⟩ := cutoff_deriv_bound_exists
    let majorant : ℝ → ℝ := fun x => 2 * h x ^ 2 + 2 * C ^ 2 * f x ^ 2
    have himaj : Integrable majorant γ := by
      exact (hh_sq.const_mul 2).add (hf_sq.const_mul (2 * C ^ 2))
    have hmeas (n : ℕ) : AEStronglyMeasurable
        (fun x => (deriv (truncated f n) x - h x) ^ 2) γ := by
      have hc : Continuous (deriv (cutoff n)) :=
        (cutoff_contDiff n).continuous_deriv (by norm_num)
      have hm : Measurable (fun x => deriv (truncated f n) x) := by
        simp_rw [deriv_truncated hd n]
        exact ((cutoff_contDiff n).continuous.measurable.mul hh_meas).add
          (hc.measurable.mul hfcont.measurable)
      exact ((hm.sub hh_meas).pow_const 2).aestronglyMeasurable
    have hbound (n : ℕ) : ∀ᵐ x ∂γ,
        ‖(deriv (truncated f n) x - h x) ^ 2‖ ≤ majorant x := by
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), deriv_truncated hd]
      have h1 := cutoff_error_sq_le n x (h x)
      have h2 := derivative_extra_sq_le C hC hb n x (f x)
      dsimp [majorant]
      nlinarith [sq_nonneg ((cutoff n x - 1) * h x -
        (deriv (cutoff n) x) * f x)]
    have hlim (x : ℝ) : Tendsto (fun n : ℕ =>
        (deriv (truncated f n) x - h x) ^ 2) atTop (𝓝 0) := by
      have hprod := (cutoff_tendsto_one x).mul_const (h x)
      have hextra := (cutoff_deriv_tendsto_zero x).mul_const (f x)
      have hadd := hprod.add hextra
      have hsub := hadd.sub_const (h x)
      have hsq := hsub.pow 2
      simpa [deriv_truncated hd] using hsq
    convert tendsto_integral_filter_of_dominated_convergence majorant
      (Filter.Eventually.of_forall hmeas) (Filter.Eventually.of_forall hbound) himaj
      (Filter.Eventually.of_forall hlim) using 1; simp


/-- The cutoff derivative contributes at most `C/(n+1)` times the original
Gaussian `L²` norm. This is the quantitative error term in the graph estimate. -/
theorem derivative_cutoff_extra_sq_integral_bound
    (f : ℝ → ℝ) (hf : Measurable f)
    (hf_sq : Integrable (fun x => f x ^ 2) γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      (∫ x, (deriv (cutoff n) x * f x) ^ 2 ∂γ) ≤
        (C / ((n : ℝ) + 1)) ^ 2 * (∫ x, f x ^ 2 ∂γ) := by
  obtain ⟨C, hC, hbound⟩ := cutoff_deriv_bound_exists
  refine ⟨C, hC, ?_⟩
  intro n
  have hderiv : ∀ x, |deriv (cutoff n) x| ≤ C / ((n : ℝ) + 1) := by
    intro x
    rw [(hasDerivAt_cutoff n x).deriv, abs_div, abs_of_pos (scale_pos n)]
    exact div_le_div_of_nonneg_right (hbound _) (scale_pos n).le
  have hpoint (x : ℝ) : (deriv (cutoff n) x * f x) ^ 2 ≤
      (C / ((n : ℝ) + 1)) ^ 2 * f x ^ 2 := by
    have hcpos : 0 ≤ C / ((n : ℝ) + 1) := div_nonneg hC (scale_pos n).le
    have hs : (deriv (cutoff n) x) ^ 2 ≤ (C / ((n : ℝ) + 1)) ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hcpos).2 (hderiv x)
    nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg (f x))]
  have hmeas : Measurable (fun x => (deriv (cutoff n) x * f x) ^ 2) := by
    exact (((cutoff_contDiff n).continuous_deriv (by norm_num)).measurable.mul hf).pow_const 2
  have hi : Integrable (fun x => (deriv (cutoff n) x * f x) ^ 2) γ := by
    apply Integrable.mono' (hf_sq.const_mul ((C / ((n : ℝ) + 1)) ^ 2))
      hmeas.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint x
  calc
    _ ≤ ∫ x, (C / ((n : ℝ) + 1)) ^ 2 * f x ^ 2 ∂γ := by
      exact integral_mono hi (hf_sq.const_mul _) hpoint
    _ = (C / ((n : ℝ) + 1)) ^ 2 * (∫ x, f x ^ 2 ∂γ) := by rw [integral_const_mul]

end OperatorDerivativeRewrite.Foundation.GaussianSobolevCutoffs
