import Foundation.ExponentialResidualLife
import Mathlib.MeasureTheory.Measure.WithDensity

/-! A threshold chosen from the actual past leaves a fresh exponential residual. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.AdaptiveExponentialResidual
open ExponentialHoldingSequence
variable {A : Type*} [MeasurableSpace A]

def survive (r : A → ℝ) : Set (A × ℝ) := {p | r p.1 < p.2}
def shift (r : A → ℝ) (p : A × ℝ) : A × ℝ := (p.1,p.2-r p.1)
def weight (r : A → ℝ) (a : A) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-r a))
def past (μ : Measure A) (r : A → ℝ) : Measure A := μ.withDensity (weight r)

theorem survive_measurable {r : A → ℝ} (hr : Measurable r) : MeasurableSet (survive r) :=
  measurableSet_lt (hr.comp measurable_fst) measurable_snd

theorem shift_measurable {r : A → ℝ} (hr : Measurable r) : Measurable (shift r) :=
  measurable_fst.prodMk (measurable_snd.sub (hr.comp measurable_fst))

theorem weight_measurable {r : A → ℝ} (hr : Measurable r) : Measurable (weight r) :=
  hr.neg.exp.ennreal_ofReal

theorem residual_section (s : ℝ) (hs : 0 ≤ s) (B : Set ℝ) (hB : MeasurableSet B) :
    base ((fun x : ℝ => x-s) ⁻¹' B ∩ Ioi s) = ENNReal.ofReal (Real.exp (-s)) * base B := by
  have hm : Measurable (fun x : ℝ => x-s) := by fun_prop
  have he := congrArg (fun ν : Measure ℝ => ν B) (ExponentialResidualLife.residual_law s hs)
  simpa only [ExponentialResidualLife.residual, Measure.map_apply hm hB,
    Measure.restrict_apply (hm hB), Measure.smul_apply, smul_eq_mul] using he

theorem joint_law (μ : Measure A) [IsFiniteMeasure μ] (r : A → ℝ)
    (hr : Measurable r) (hn : ∀ a, 0 ≤ r a) :
    ((μ.prod base).restrict (survive r)).map (shift r) = (past μ r).prod base := by
  apply Measure.ext_prod
  intro S B hS hB
  rw [Measure.map_apply (shift_measurable hr) (hS.prod hB),
    Measure.restrict_apply ((shift_measurable hr) (hS.prod hB)),
    Measure.prod_apply (((shift_measurable hr) (hS.prod hB)).inter (survive_measurable hr)),
    Measure.prod_prod, past, withDensity_apply _ hS]
  rw [← lintegral_indicator hS, ← lintegral_mul_const (base B)
    ((weight_measurable hr).indicator hS)]
  apply lintegral_congr
  intro a
  by_cases ha : a ∈ S
  · have he : Prod.mk a ⁻¹' ((shift r) ⁻¹' (S ×ˢ B) ∩ survive r) =
        (fun x : ℝ => x-r a) ⁻¹' B ∩ Ioi (r a) := by
      ext x
      simp [shift, survive, ha]
    rw [he, residual_section (r a) (hn a) B hB, indicator_of_mem ha]
    rfl
  · have he : Prod.mk a ⁻¹' ((shift r) ⁻¹' (S ×ˢ B) ∩ survive r) = ∅ := by
      ext x
      simp [shift, survive, ha]
    rw [he, measure_empty, indicator_of_notMem ha, zero_mul]

end OperatorDerivativeRewrite.Foundation.AdaptiveExponentialResidual
