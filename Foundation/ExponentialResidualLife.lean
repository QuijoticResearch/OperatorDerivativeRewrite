import Foundation.ExponentialRenewalSurvival
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! Exponential memorylessness as a genuine residual-life measure identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace OperatorDerivativeRewrite.Foundation.ExponentialResidualLife
open ExponentialHoldingSequence

def residual (s : ℝ) : Measure ℝ := (base.restrict (Ioi s)).map (fun x => x-s)

instance residual_finite (s : ℝ) : IsFiniteMeasure (residual s) := by
  unfold residual
  infer_instance

theorem residual_cdf (s : ℝ) (hs : 0 ≤ s) (x : ℝ) :
    (residual s).real (Iic x) = Real.exp (-s) * base.real (Iic x) := by
  have hm : Measurable (fun y : ℝ => y-s) := by fun_prop
  rw [residual, map_measureReal_apply_of_aemeasurable
    hm.aemeasurable measurableSet_Iic,
    measureReal_restrict_apply (hm measurableSet_Iic)]
  by_cases hx : 0 ≤ x
  · have he : (fun y : ℝ => y-s) ⁻¹' Iic x ∩ Ioi s = Iic (s+x) \ Iic s := by
      ext y
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioi, Set.mem_sdiff, not_le]
      constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
    rw [he, measureReal_sdiff (Iic_subset_Iic.mpr (by linarith)) measurableSet_Iic]
    simp only [base_cdf, ite_eq_left hs, ite_eq_left hx, ite_eq_left (add_nonneg hs hx),
      neg_add, Real.exp_add]
    ring
  · have he : (fun y : ℝ => y-s) ⁻¹' Iic x ∩ Ioi s = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false]
      intro h
      linarith [h.1,h.2]
    rw [he, measureReal_empty, base_cdf, ite_eq_right hx, mul_zero]

theorem residual_law (s : ℝ) (hs : 0 ≤ s) :
    residual s = ENNReal.ofReal (Real.exp (-s)) • base := by
  apply Measure.ext_of_Iic
  intro x
  apply (measureReal_eq_measureReal_iff (h₁ := measure_ne_top _ _) (h₂ := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))).mp
  rw [measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  exact residual_cdf s hs x

def conditional (s : ℝ) : Measure ℝ :=
  ENNReal.ofReal (Real.exp s) • base.restrict (Ioi s)

theorem conditional_residual_law (s : ℝ) (hs : 0 ≤ s) :
    (conditional s).map (fun x => x-s) = base := by
  have hm : Measurable (fun y : ℝ => y-s) := by fun_prop
  rw [conditional, Measure.map_smul _ hm.aemeasurable,
    ← residual, residual_law s hs, smul_smul]
  have he : ENNReal.ofReal (Real.exp s) * ENNReal.ofReal (Real.exp (-s)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, ENNReal.ofReal_one]
  rw [he, one_smul]

theorem conditional_probability (s : ℝ) (hs : 0 ≤ s) : IsProbabilityMeasure (conditional s) := by
  have : IsProbabilityMeasure ((conditional s).map (fun x : ℝ => x-s)) := by
    rw [conditional_residual_law s hs]
    infer_instance
  have hm : Measurable (fun y : ℝ => y-s) := by fun_prop
  exact Measure.isProbabilityMeasure_of_map hm.aemeasurable

end OperatorDerivativeRewrite.Foundation.ExponentialResidualLife
