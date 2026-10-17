import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.ConditionalProbability

/-! Actual normalized restrictions and their finite relative entropy. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter InformationTheory
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.ConditioningRelativeEntropy
variable {P : Type*} [MeasurableSpace P]
variable (μ : Measure P) [IsProbabilityMeasure μ] (s : Set P)

theorem llr_restrict_zero (hs : MeasurableSet s) :
    llr (μ.restrict s) μ =ᵐ[μ.restrict s] fun _ => 0 := by
  filter_upwards [ae_restrict_of_ae (Measure.rnDeriv_restrict_self μ hs),
    ae_restrict_mem hs] with x hx hxs
  simp [llr, hx, Set.indicator_of_mem hxs]

theorem llr_cond_constant (hs : MeasurableSet s) (hp : μ s ≠ 0) :
    llr (cond μ s) μ =ᵐ[cond μ s] fun _ => Real.log ((μ s)⁻¹).toReal := by
  have h := llr_smul_left (Measure.absolutelyContinuous_restrict (μ := μ) (s := s)) ((μ s)⁻¹)
    (ENNReal.inv_ne_zero.mpr (measure_ne_top μ s)) (ENNReal.inv_ne_top.mpr hp)
  have he : llr (cond μ s) μ =ᵐ[μ.restrict s] fun _ => Real.log ((μ s)⁻¹).toReal := by
    filter_upwards [h, llr_restrict_zero μ s hs] with x hx hz
    simpa only [ProbabilityTheory.cond, hz, zero_add] using hx
  exact (Measure.smul_absolutelyContinuous (μ := μ.restrict s)).ae_le he

theorem llr_cond_integrable (hs : MeasurableSet s) (hp : μ s ≠ 0) :
    Integrable (llr (cond μ s) μ) (cond μ s) := by
  let _ := cond_isProbabilityMeasure hp
  exact (integrable_const _).congr (llr_cond_constant μ s hs hp).symm

theorem entropy_cond_finite (hs : MeasurableSet s) (hp : μ s ≠ 0) :
    klDiv (cond μ s) μ ≠ ⊤ :=
  klDiv_ne_top cond_absolutelyContinuous (llr_cond_integrable μ s hs hp)

theorem entropy_cond_exact (hs : MeasurableSet s) (hp : μ s ≠ 0) :
    (klDiv (cond μ s) μ).toReal = Real.log ((μ s)⁻¹).toReal := by
  let _ := cond_isProbabilityMeasure hp
  rw [toReal_klDiv cond_absolutelyContinuous (llr_cond_integrable μ s hs hp),
    integral_congr_ae (llr_cond_constant μ s hs hp)]
  simp

theorem cond_ne_self (hp : μ s ≠ 0) (hlt : μ s < 1) : cond μ s ≠ μ := by
  intro h
  have hh := congrArg (fun ν : Measure P => ν s) h
  rw [cond_apply_self hp (measure_ne_top μ s)] at hh
  exact (ne_of_lt hlt) hh.symm

theorem entropy_cond_positive (hs : MeasurableSet s) (hp : μ s ≠ 0)
    (hlt : μ s < 1) : 0 < (klDiv (cond μ s) μ).toReal := by
  let _ := cond_isProbabilityMeasure hp
  apply ENNReal.toReal_pos _ (entropy_cond_finite μ s hs hp)
  exact fun h => cond_ne_self μ s hp hlt (klDiv_eq_zero_iff.mp h)

end OperatorDerivativeRewrite.Foundation.ConditioningRelativeEntropy
