import Foundation.FractionalCurvatureSubordinationObstruction
import Mathlib.Analysis.SpecialFunctions.Exp

/-! The Cauchy curvature eigenvalue three does not give a semigroup decay
rate six for its energy component. Everything is in the original two-point
Brownian covariance forms and the two exact Fourier multipliers. -/
noncomputable section
open Matrix
namespace OperatorDerivativeRewrite.Foundation.BrownianCurvatureModeDecayObstruction
open FractionalCurvatureSubordinationObstruction

def firstMode : Fin 2 → ℝ := ![1, 0]
def thirdCurvatureMode : Fin 2 → ℝ := ![-1, 1]

theorem thirdMode_is_original_innovation : thirdCurvatureMode =
    BrownianCovariancePowers.differenceVector (1 : Fin 2) := by
  ext i
  fin_cases i <;> norm_num [thirdCurvatureMode, BrownianCovariancePowers.differenceVector,
    BrownianCovariancePowers.predecessor, Pi.single_apply]

theorem thirdMode_eigenpair : P (1 / 2) *ᵥ thirdCurvatureMode =
    3 • (R (1 / 2) *ᵥ thirdCurvatureMode) := by
  rw [R_half, P_half]
  ext i
  fin_cases i <;> norm_num [Matrix.mulVec, Fin.sum_univ_two, thirdCurvatureMode]

theorem mode_decomposition (v : Fin 2 → ℝ) :
    v = (v 0 + v 1) • firstMode + v 1 • thirdCurvatureMode := by
  ext i
  fin_cases i <;> simp [firstMode, thirdCurvatureMode]

theorem modes_orthogonal : dotProduct firstMode (R (1 / 2) *ᵥ thirdCurvatureMode) = 0 := by
  rw [R_half]
  norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_two, firstMode, thirdCurvatureMode]

def componentThree (v : Fin 2 → ℝ) : Fin 2 → ℝ := v 1 • thirdCurvatureMode

def componentEnergy (v : Fin 2 → ℝ) : ℝ :=
  dotProduct (componentThree v) (R (1 / 2) *ᵥ componentThree v)

theorem componentEnergy_eq (v : Fin 2 → ℝ) : componentEnergy v = (v 1)^2 := by
  rw [componentEnergy, R_half]
  norm_num [componentThree, thirdCurvatureMode, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

/-- Exact coefficient action exp(-t|n|) on frequencies one and two. -/
def fourierFlow (t : ℝ) (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![Real.exp (-t) * v 0, Real.exp (-2*t) * v 1]

theorem fourierFlow_add (s t : ℝ) (v : Fin 2 → ℝ) :
    fourierFlow (s+t) v = fourierFlow s (fourierFlow t v) := by
  ext i
  fin_cases i
  · change Real.exp (-(s+t)) * v 0 = Real.exp (-s) * (Real.exp (-t) * v 0)
    rw [neg_add, Real.exp_add]
    ring
  · change Real.exp (-2*(s+t)) * v 1 = Real.exp (-2*s) * (Real.exp (-2*t) * v 1)
    rw [mul_add, Real.exp_add]
    ring

theorem componentEnergy_flow (t : ℝ) (v : Fin 2 → ℝ) :
    componentEnergy (fourierFlow t v) = Real.exp (-4*t) * componentEnergy v := by
  rw [componentEnergy_eq, componentEnergy_eq]
  change (Real.exp (-2*t) * v 1)^2 = _
  rw [mul_pow, pow_two (Real.exp (-2*t)), ← Real.exp_add]
  have he : -2*t + -2*t = -4*t := by ring
  rw [he]

theorem false_rate_on_second_frequency {t : ℝ} (ht : 0 < t) :
    ¬ componentEnergy (fourierFlow t ![0, 1]) ≤
      Real.exp (-6*t) * componentEnergy ![0, 1] := by
  rw [componentEnergy_flow, componentEnergy_eq]
  change ¬ Real.exp (-4*t) * (1:ℝ)^2 ≤ Real.exp (-6*t) * (1:ℝ)^2
  norm_num only [one_pow, mul_one]
  have h : Real.exp (-6*t) < Real.exp (-4*t) := Real.exp_lt_exp.mpr (by linarith)
  exact not_le.mpr h

end OperatorDerivativeRewrite.Foundation.BrownianCurvatureModeDecayObstruction
