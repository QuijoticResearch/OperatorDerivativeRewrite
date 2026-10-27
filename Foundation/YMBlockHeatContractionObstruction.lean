import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The fixed-boundary heat reference loses uniform contraction at weak coupling

The block-transfer manuscripts use a reference factor
`exp(-gap / (curvatureScale * beta))` with fixed positive gap and
curvature scale, then seek a contraction uniformly below one as
`beta → ∞`. This module proves the reference factor tends to one and
that adding nonnegative perturbation allowances cannot produce such a
uniform bound. It tests exactly that stated heat-reference mechanism.
It does not rule out scale-dependent spectral gaps, geometric rescaling,
or a different nonlinear transfer estimate; those require new hypotheses.
-/

open Filter
open scoped Topology

noncomputable section

namespace OperatorDerivativeRewrite.Foundation.YMBlockHeatContractionObstruction

def referenceFactor (gap curvatureScale beta : ℝ) : ℝ :=
  Real.exp (-(gap / (curvatureScale * beta)))

theorem referenceFactor_lt_one (gap curvatureScale beta : ℝ)
    (hgap : 0 < gap) (hc : 0 < curvatureScale) (hb : 0 < beta) :
    referenceFactor gap curvatureScale beta < 1 := by
  unfold referenceFactor
  apply Real.exp_lt_one_iff.mpr
  have hp : 0 < gap / (curvatureScale * beta) :=
    div_pos hgap (mul_pos hc hb)
  linarith

theorem referenceFactor_tendsto_one (gap curvatureScale : ℝ)
    (_hc : curvatureScale ≠ 0) :
    Tendsto (fun beta : ℝ => referenceFactor gap curvatureScale beta)
      atTop (𝓝 1) := by
  have hi : Tendsto (fun beta : ℝ => beta⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hzero : Tendsto (fun beta : ℝ =>
      (-(gap / curvatureScale)) * beta⁻¹) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℝ => -(gap / curvatureScale))
        atTop (𝓝 (-(gap / curvatureScale))) := tendsto_const_nhds
    simpa only [mul_zero] using hconst.mul hi
  have he := Real.tendsto_exp_nhds_zero_nhds_one.comp hzero
  convert he using 1
  ext beta
  unfold referenceFactor
  congr 1
  field_simp

theorem no_uniform_reference_contraction (gap curvatureScale : ℝ)
    (hc : curvatureScale ≠ 0) :
    ¬ ∃ q : ℝ, q < 1 ∧ ∀ beta : ℝ, 1 ≤ beta →
      referenceFactor gap curvatureScale beta ≤ q := by
  rintro ⟨q, hq, hb⟩
  have he : ∀ᶠ beta : ℝ in atTop,
      referenceFactor gap curvatureScale beta ≤ q := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with beta hbeta
    exact hb beta hbeta
  have hle : (1 : ℝ) ≤ q :=
    le_of_tendsto (referenceFactor_tendsto_one gap curvatureScale hc) he
  linarith

theorem no_uniform_contraction_with_nonnegative_errors
    (gap curvatureScale : ℝ) (hc : curvatureScale ≠ 0)
    (errorA errorB : ℝ → ℝ)
    (hA : ∀ beta, 1 ≤ beta → 0 ≤ errorA beta)
    (hB : ∀ beta, 1 ≤ beta → 0 ≤ errorB beta) :
    ¬ ∃ q : ℝ, q < 1 ∧ ∀ beta : ℝ, 1 ≤ beta →
      referenceFactor gap curvatureScale beta + errorA beta +
        errorB beta ≤ q := by
  intro h
  apply no_uniform_reference_contraction gap curvatureScale hc
  obtain ⟨q, hq, hb⟩ := h
  refine ⟨q, hq, ?_⟩
  intro beta hbeta
  have ha := hA beta hbeta
  have hb' := hB beta hbeta
  have hq' := hb beta hbeta
  linarith

/-! The heat reference leaves at most an inverse-coupling-sized budget for
all additive comparison errors. This is a pointwise bound, stronger than the
nonuniformity conclusion above. -/

theorem reference_loss_le_inverse_beta (gap curvatureScale beta : ℝ) :
    1 - referenceFactor gap curvatureScale beta ≤
      gap / (curvatureScale * beta) := by
  unfold referenceFactor
  have h := Real.add_one_le_exp (-(gap / (curvatureScale * beta)))
  linarith

theorem necessary_error_budget (gap curvatureScale beta error : ℝ)
    (h : referenceFactor gap curvatureScale beta + error < 1) :
    error < gap / (curvatureScale * beta) := by
  have hl := reference_loss_le_inverse_beta gap curvatureScale beta
  linarith

theorem no_contraction_if_error_at_least_inverse_beta
    (gap curvatureScale beta error : ℝ)
    (he : gap / (curvatureScale * beta) ≤ error) :
    1 ≤ referenceFactor gap curvatureScale beta + error := by
  have hl := reference_loss_le_inverse_beta gap curvatureScale beta
  linarith

end OperatorDerivativeRewrite.Foundation.YMBlockHeatContractionObstruction
