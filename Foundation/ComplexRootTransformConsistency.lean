import Foundation.ComplexRootWalkSecondMoment
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Genuine fourth-order local consistency of the complex root-walk exponential transform. -/
noncomputable section
open Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.ComplexRootTransformConsistency

def factor (x : ℝ) : ℝ := Real.cos x * Real.cosh x
def d1 (x : ℝ) : ℝ := -Real.sin x * Real.cosh x + Real.cos x * Real.sinh x
def d2 (x : ℝ) : ℝ := -2 * Real.sin x * Real.sinh x
def d3 (x : ℝ) : ℝ := -2 * Real.cos x * Real.sinh x - 2 * Real.sin x * Real.cosh x
def d4 (x : ℝ) : ℝ := -4 * Real.cos x * Real.cosh x

theorem deriv_factor : deriv factor = d1 := by
  funext x
  exact ((Real.hasDerivAt_cos x).mul (Real.hasDerivAt_cosh x)).deriv

theorem deriv_d1 : deriv d1 = d2 := by
  funext x
  have hd := (((Real.hasDerivAt_sin x).neg).mul (Real.hasDerivAt_cosh x)).add
    ((Real.hasDerivAt_cos x).mul (Real.hasDerivAt_sinh x))
  have hf : d1 = -Real.sin * Real.cosh + Real.cos * Real.sinh := by funext y; rfl
  rw [hf, hd.deriv]
  simp only [d2, Pi.neg_apply]
  ring

theorem deriv_d2 : deriv d2 = d3 := by
  funext x
  have hd := (((Real.hasDerivAt_sin x).const_mul (-2)).mul (Real.hasDerivAt_sinh x))
  have hf : d2 = (fun y => -2 * Real.sin y) * Real.sinh := by funext y; rfl
  rw [hf, hd.deriv]
  simp only [d3]
  ring

theorem deriv_d3 : deriv d3 = d4 := by
  funext x
  have hd := ((((Real.hasDerivAt_cos x).const_mul (-2)).mul (Real.hasDerivAt_sinh x))).sub
    (((Real.hasDerivAt_sin x).const_mul 2).mul (Real.hasDerivAt_cosh x))
  have hf : d3 = (fun y => -2 * Real.cos y) * Real.sinh -
      (fun y => 2 * Real.sin y) * Real.cosh := by funext y; rfl
  rw [hf, hd.deriv]
  simp only [d4]
  ring

theorem taylor_four (x : ℝ) : taylorWithinEval factor 4 univ 0 x = 1-x^4/6 := by
  have h0 : iteratedDeriv 0 factor = factor := iteratedDeriv_zero
  have h1 : iteratedDeriv 1 factor = d1 := by rw [iteratedDeriv_succ, h0, deriv_factor]
  have h2 : iteratedDeriv 2 factor = d2 := by rw [iteratedDeriv_succ, h1, deriv_d1]
  have h3 : iteratedDeriv 3 factor = d3 := by rw [iteratedDeriv_succ, h2, deriv_d2]
  have h4 : iteratedDeriv 4 factor = d4 := by rw [iteratedDeriv_succ, h3, deriv_d3]
  norm_num [taylorWithinEval_succ, taylor_within_zero_eval, iteratedDerivWithin_univ,
    h0, h1, h2, h3, h4, factor, d1, d2, d3, d4]
  ring

theorem fourth_order_remainder :
    (fun x : ℝ => factor x - (1-x^4/6)) =o[𝓝 0] (fun x => x^4) := by
  have hc : ContDiff ℝ 4 factor := by unfold factor; fun_prop
  have he := taylor_isLittleO_univ (x₀ := (0 : ℝ)) hc
  simpa only [taylor_four, sub_zero] using he

end OperatorDerivativeRewrite.Foundation.ComplexRootTransformConsistency
