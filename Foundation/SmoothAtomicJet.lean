import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! A genuinely smooth compactly supported function with value zero and derivative one at zero. -/
noncomputable section
open scoped ContDiff
namespace OperatorDerivativeRewrite.Foundation.SmoothAtomicJet
set_option backward.isDefEq.respectTransparency false

def bump : ContDiffBump (0 : ℝ) := ⟨1,2,by norm_num,by norm_num⟩

def witness (x : ℝ) : ℝ := x * bump x

theorem witness_smooth : ContDiff ℝ ∞ witness :=
  contDiff_id.mul bump.contDiff

theorem witness_compact : HasCompactSupport witness :=
  bump.hasCompactSupport.mul_left

theorem witness_zero : witness 0 = 0 := by simp [witness]

theorem witness_near_zero : witness =ᶠ[nhds (0 : ℝ)] (fun x => x) := by
  filter_upwards [bump.eventuallyEq_one] with x hx
  simp [witness, hx]

theorem witness_hasDerivAt : HasDerivAt witness 1 0 :=
  (hasDerivAt_id (0 : ℝ)).congr_of_eventuallyEq witness_near_zero

theorem witness_deriv : deriv witness 0 = 1 := witness_hasDerivAt.deriv

theorem witness_nonzero : witness ≠ 0 := by
  intro h
  have hd := witness_deriv
  rw [h] at hd
  norm_num at hd

end OperatorDerivativeRewrite.Foundation.SmoothAtomicJet
