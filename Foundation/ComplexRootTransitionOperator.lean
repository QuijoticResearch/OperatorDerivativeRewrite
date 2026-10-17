import Foundation.ComplexRootOneStepCalculus
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! The actual four-point complex probability transition as a bounded contraction. -/
noncomputable section
open MeasureTheory Filter
open scoped BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.ComplexRootTransitionOperator
open ComplexFourthRootNoise

abbrev Test := ℂ →ᵇ ℂ

def shift (z : ℂ) : Test →L[ℂ] Test :=
  BoundedContinuousFunction.compContinuousCLM ℂ ℂ
    ⟨fun x => x+z, continuous_id.add continuous_const⟩

def step (a : ℝ) : Test →L[ℂ] Test := (1/4 : ℂ) • ∑ k : Fin 4, shift (noise a k)

theorem step_apply (a : ℝ) (f : Test) (z : ℂ) :
    step a f z = (1/4 : ℂ) * ∑ k : Fin 4, f (z+noise a k) := by
  simp [step, shift, smul_eq_mul]

theorem step_integral (a : ℝ) (f : Test) (z : ℂ) :
    step a f z = ∫ k, f (z+noise a k) ∂probability := by
  rw [step_apply, integral_formula]
  norm_num [Fin.sum_univ_succ]
  ring

theorem step_bound (a : ℝ) (f : Test) : ‖step a f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro z
  rw [step_integral]
  calc
    _ ≤ ∫ k, ‖f (z+noise a k)‖ ∂probability := norm_integral_le_integral_norm _
    _ ≤ ∫ _ : Fin 4, ‖f‖ ∂probability :=
      integral_mono_ae Integrable.of_finite (integrable_const _)
        (Eventually.of_forall (fun k => f.norm_coe_le_norm _))
    _ = _ := by simp

theorem step_norm (a : ℝ) : ‖step a‖ ≤ 1 := by
  apply (step a).opNorm_le_bound zero_le_one
  intro f
  simpa only [one_mul] using step_bound a f

theorem step_constant (a : ℝ) (c : ℂ) :
    step a (BoundedContinuousFunction.const ℂ c) = BoundedContinuousFunction.const ℂ c := by
  ext z
  rw [step_integral]
  simp

theorem step_positive_realPart (a : ℝ) (f : Test) (hf : ∀ z, 0 ≤ (f z).re) (z : ℂ) :
    0 ≤ (step a f z).re := by
  rw [step_integral]
  have he := integral_re (μ := probability) (f := fun k => f (z+noise a k)) Integrable.of_finite
  simp only [RCLike.re_eq_complex_re] at he
  rw [← he]
  exact integral_nonneg (fun k => hf _)

def generator (rate a : ℝ) : Test →L[ℂ] Test :=
  (rate : ℂ) • (step a - ContinuousLinearMap.id ℂ Test)

theorem generator_apply (rate a : ℝ) (f : Test) (z : ℂ) :
    generator rate a f z = (rate : ℂ) * (step a f z - f z) := by
  simp [generator, smul_eq_mul]

end OperatorDerivativeRewrite.Foundation.ComplexRootTransitionOperator
