import Foundation.MixedAtomicNonclosability
import Mathlib.Algebra.Module.Submodule.Equiv

/-! An actual well-defined partial linear smooth derivative with a nonclosable graph. -/
noncomputable section
open MeasureTheory Filter
namespace OperatorDerivativeRewrite.Foundation.MixedAtomicDerivativeOperator
open MixedAtomicGradient MixedAtomicNonclosability
set_option backward.isDefEq.respectTransparency false

def inputLinear : Core →ₗ[ℝ] Lp ℝ 2 μ where
  toFun := input
  map_add' f g := MemLp.toLp_add (core_memLp f 2) (core_memLp g 2)
  map_smul' r f := MemLp.toLp_const_smul r (core_memLp f 2)

theorem output_add (f g : Core) : output (f + g) = output f + output g := by
  have h : output (f + g) =
      ((derivative_memLp f 2).add (derivative_memLp g 2)).toLp (deriv f.val + deriv g.val) := by
    apply (MemLp.toLp_eq_toLp_iff _ _).mpr
    filter_upwards [] with x
    change deriv (f.val + g.val) x = deriv f.val x + deriv g.val x
    exact deriv_add (f.property.1.differentiable (by norm_num) x)
      (g.property.1.differentiable (by norm_num) x)
  rw [MemLp.toLp_add] at h
  exact h

theorem output_smul (r : ℝ) (f : Core) : output (r • f) = r • output f := by
  have h : output (r • f) =
      ((derivative_memLp f 2).const_smul r).toLp (r • deriv f.val) := by
    apply (MemLp.toLp_eq_toLp_iff _ _).mpr
    filter_upwards [] with x
    change deriv (r • f.val) x = r • deriv f.val x
    exact deriv_const_smul r (f.property.1.differentiable (by norm_num) x)
  rw [MemLp.toLp_const_smul] at h
  exact h

def outputLinear : Core →ₗ[ℝ] Lp ℝ 2 μ where
  toFun := output
  map_add' := output_add
  map_smul' r f := output_smul r f

def coreToRange : Core ≃ₗ[ℝ] LinearMap.range inputLinear :=
  LinearEquiv.ofInjective inputLinear input_injective

def derivativeOperator : Lp ℝ 2 μ →ₗ.[ℝ] Lp ℝ 2 μ where
  domain := LinearMap.range inputLinear
  toFun := outputLinear.comp coreToRange.symm.toLinearMap

theorem operator_domain (f : Core) : input f ∈ derivativeOperator.domain := ⟨f,rfl⟩

theorem operator_agrees (f : Core) : derivativeOperator ⟨input f,operator_domain f⟩ = output f := by
  change outputLinear (coreToRange.symm ⟨input f,operator_domain f⟩) = output f
  have he : coreToRange f = ⟨input f,operator_domain f⟩ := Subtype.ext rfl
  rw [← he, coreToRange.symm_apply_apply]
  rfl

theorem derivativeOperator_not_closable : ¬ derivativeOperator.IsClosable := by
  intro h
  exact no_closable_extension ⟨derivativeOperator,operator_domain,h,operator_agrees⟩

end OperatorDerivativeRewrite.Foundation.MixedAtomicDerivativeOperator
