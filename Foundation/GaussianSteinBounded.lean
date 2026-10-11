/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Copyright (c) 2026 OperatorDerivativeRewrite contributors.
Inspired by Gaussian1D.stein_identity_standard in
MarkovSemigroups/Instances/WorkInProgress/EuclideanStein.lean, commit
acf649108ea2222f4a8544a2782f448cb502492a, Apache License 2.0.
See LICENSES/Apache-2.0.txt. The proof reuses the local density derivative
and Mathlib improper integration by parts instead of duplicating PDF tail lemmas.
-/
import Foundation.GaussianCore

/-! Gaussian Stein integration by parts for bounded C¹ functions.
Every derivative is Mathlib's actual `deriv`; integrability and both boundary
limits are proved before applying whole-line integration by parts. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianSteinBounded
open GaussianCore

/-- A bounded measurable real function is Gaussian-integrable. -/
theorem integrable_of_bounded {h : ℝ → ℝ} (hm : Measurable h)
    {A : ℝ} (hb : ∀ x, |h x| ≤ A) : Integrable h γ := by
  refine Integrable.mono' (integrable_const A) hm.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs] using hb x)

/-- Multiplication by the coordinate remains integrable for bounded measurable h. -/
theorem integrable_coordinate_mul_of_bounded {h : ℝ → ℝ} (hm : Measurable h)
    {A : ℝ} (hb : ∀ x, |h x| ≤ A) : Integrable (fun x => x * h x) γ := by
  have hi : Integrable (fun x : ℝ => x) γ :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)
  refine Integrable.mono' (hi.abs.const_mul A)
    (measurable_id.mul hm).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_mul]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hb x) (abs_nonneg x))

/-- All Gaussian integrals used by Stein have their genuine finite meaning. -/
theorem stein_integrable {h : ℝ → ℝ} (hc : ContDiff ℝ 1 h)
    {A B : ℝ} (hb : ∀ x, |h x| ≤ A) (hdb : ∀ x, |deriv h x| ≤ B) :
    Integrable h γ ∧ Integrable (deriv h) γ ∧ Integrable (fun x => x * h x) γ := by
  exact ⟨integrable_of_bounded hc.continuous.measurable hb,
    integrable_of_bounded (hc.continuous_deriv le_rfl).measurable hdb,
    integrable_coordinate_mul_of_bounded hc.continuous.measurable hb⟩

/-- The Gaussian-weighted function and both product-rule terms are Lebesgue-integrable. -/
theorem density_products_integrable {h : ℝ → ℝ} (hc : ContDiff ℝ 1 h)
    {A B : ℝ} (hb : ∀ x, |h x| ≤ A) (hdb : ∀ x, |deriv h x| ≤ B) :
    Integrable (fun x => h x * gaussianPDFReal 0 1 x) ∧
      Integrable (fun x => deriv h x * gaussianPDFReal 0 1 x) ∧
      Integrable (fun x => h x * (-x * gaussianPDFReal 0 1 x)) := by
  obtain ⟨hi, hdi, hxi⟩ := stein_integrable hc hb hdb
  constructor
  · simpa [mul_comm] using integrable_density_mul hi
  constructor
  · simpa [mul_comm] using integrable_density_mul hdi
  · convert (integrable_density_mul hxi).neg using 1
    funext x
    simp only [Pi.neg_apply]
    ring

/-- Actual product differentiation using the already verified Gaussian PDF derivative. -/
theorem density_product_hasDerivAt {h : ℝ → ℝ} (hc : ContDiff ℝ 1 h) (x : ℝ) :
    HasDerivAt (fun y => h y * gaussianPDFReal 0 1 y)
      (deriv h x * gaussianPDFReal 0 1 x + h x * (-x * gaussianPDFReal 0 1 x)) x := by
  exact ((hc.differentiable (by simp)).differentiableAt.hasDerivAt).mul
    (density_hasDerivAt x)

/-- Both boundary terms vanish, derived from actual derivative and function integrability. -/
theorem density_product_tendsto_zero {h : ℝ → ℝ} (hc : ContDiff ℝ 1 h)
    {A B : ℝ} (hb : ∀ x, |h x| ≤ A) (hdb : ∀ x, |deriv h x| ≤ B) :
    Tendsto (fun x => h x * gaussianPDFReal 0 1 x) atBot (𝓝 0) ∧
      Tendsto (fun x => h x * gaussianPDFReal 0 1 x) atTop (𝓝 0) := by
  obtain ⟨hi, hdi, hni⟩ := density_products_integrable hc hb hdb
  exact ⟨tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0)
      (fun x _ => density_product_hasDerivAt hc x) (hdi.add hni).integrableOn hi.integrableOn,
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0)
      (fun x _ => density_product_hasDerivAt hc x) (hdi.add hni).integrableOn hi.integrableOn⟩

/-- Bounded C¹ Gaussian Stein identity with separate bounds on h and its actual derivative. -/
theorem stein_identity {h : ℝ → ℝ} (hc : ContDiff ℝ 1 h)
    {A B : ℝ} (hb : ∀ x, |h x| ≤ A) (hdb : ∀ x, |deriv h x| ≤ B) :
    (∫ x, deriv h x ∂γ) = ∫ x, x * h x ∂γ := by
  obtain ⟨_, hdi, hni⟩ := density_products_integrable hc hb hdb
  obtain ⟨hbot, htop⟩ := density_product_tendsto_zero hc hb hdb
  have hibp := integral_mul_deriv_eq_deriv_mul
    (fun x _ => (hc.differentiable (by simp)).differentiableAt.hasDerivAt)
    (fun x _ => density_hasDerivAt x) hni hdi hbot htop
  have hs : (∫ x, x * h x ∂γ) = ∫ x, deriv h x ∂γ := by
    rw [integral_gaussianReal_eq_integral_smul (by norm_num),
      integral_gaussianReal_eq_integral_smul (by norm_num)]
    simp only [smul_eq_mul]
    have he : (fun x => gaussianPDFReal 0 1 x * (x * h x)) =
        -(fun x => h x * (-x * gaussianPDFReal 0 1 x)) := by
      funext x
      simp only [Pi.neg_apply]
      ring
    rw [he]
    change (∫ x, -(h x * (-x * gaussianPDFReal 0 1 x))) = _
    rw [integral_neg, hibp]
    simp only [sub_self, zero_sub, neg_neg]
    congr 1
    funext x
    ring
  exact hs.symm

end OperatorDerivativeRewrite.Foundation.GaussianSteinBounded
