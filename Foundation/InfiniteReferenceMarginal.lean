import Foundation.DiagonalAmbientNullity
import Mathlib.MeasureTheory.Measure.Regular

/-! Infinite product fibers obstruct probability-style coordinate consistency of line references. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.InfiniteReferenceMarginal
open DiagonalAmbientNullity
set_option backward.isDefEq.respectTransparency false

theorem product_first_interval : Measure.map Prod.fst plane (Set.Icc (0:ℝ) 1) = ∞ := by
  rw [plane, Measure.map_fst_prod, Measure.smul_apply]
  simp

theorem scaled_product_first_interval (c : ℝ≥0∞) (hc : c ≠ 0) :
    Measure.map Prod.fst (c • plane) (Set.Icc (0:ℝ) 1) = ∞ := by
  rw [Measure.map_smul _ measurable_fst.aemeasurable, Measure.smul_apply, product_first_interval]
  exact ENNReal.mul_top hc

theorem dominating_first_interval (ρ : Measure (ℝ × ℝ))
    (c : ℝ≥0∞) (hc : c ≠ 0) (hρ : c • plane ≤ ρ) :
    Measure.map Prod.fst ρ (Set.Icc (0:ℝ) 1) = ∞ := by
  have h := Measure.map_mono hρ measurable_fst (Set.Icc (0:ℝ) 1)
  rw [scaled_product_first_interval c hc] at h
  exact top_le_iff.mp h

theorem no_lebesgue_marginal (ρ : Measure (ℝ × ℝ))
    (c : ℝ≥0∞) (hc : c ≠ 0) (hρ : c • plane ≤ ρ) :
    Measure.map Prod.fst ρ ≠ (volume : Measure ℝ) := by
  intro h
  have hi := dominating_first_interval ρ c hc hρ
  rw [h] at hi
  norm_num at hi

theorem marginal_not_locallyFinite (ρ : Measure (ℝ × ℝ))
    (c : ℝ≥0∞) (hc : c ≠ 0) (hρ : c • plane ≤ ρ) :
    ¬ IsLocallyFiniteMeasure (Measure.map Prod.fst ρ) := by
  intro h
  have : IsLocallyFiniteMeasure (Measure.map Prod.fst ρ) := h
  have hfinite := (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) 1)).measure_lt_top
    (μ := Measure.map Prod.fst ρ)
  rw [dominating_first_interval ρ c hc hρ] at hfinite
  exact lt_irrefl _ hfinite

theorem adding_diagonal_does_not_repair (ν : Measure (ℝ × ℝ))
    (c : ℝ≥0∞) (hc : c ≠ 0) :
    Measure.map Prod.fst (c • plane + ν) ≠ (volume : Measure ℝ) :=
  no_lebesgue_marginal _ c hc (Measure.le_add_right le_rfl)

end OperatorDerivativeRewrite.Foundation.InfiniteReferenceMarginal
