import Foundation.IBMGraphSmoothing
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Covariance differentiation identities for smooth Gaussian L2 scenery. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace OperatorDerivativeRewrite.Foundation.IBMContinuousScenery
open InfiniteGaussian

def wholeLineVariance (ρ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ‖wholeLineScenery ρ x‖ ^ 2

theorem wholeLineVariance_deriv (ρ : ℝ → ℝ)
    (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ) (x : ℝ) :
    deriv (wholeLineVariance ρ) x =
      2 * inner ℝ (wholeLineScenery ρ x) (wholeLineScenery (deriv ρ) x) := by
  exact (wholeLineScenery_hasDerivAt hρc hρ x).norm_sq.deriv

theorem wholeLineVariance_second_deriv (ρ : ℝ → ℝ)
    (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) (x : ℝ) :
    deriv (fun y => deriv (wholeLineVariance ρ) y) x =
      2 * (‖wholeLineScenery (deriv ρ) x‖ ^ 2 +
        inner ℝ (wholeLineScenery ρ x)
          (wholeLineScenery (deriv (deriv ρ)) x)) := by
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by norm_num)
  have hρ' : ContDiff ℝ 1 (deriv ρ) :=
    (contDiff_succ_iff_deriv.mp hρ).2.2
  have hfirst : (fun y => deriv (wholeLineVariance ρ) y) =
      fun y => 2 * inner ℝ (wholeLineScenery ρ y)
        (wholeLineScenery (deriv ρ) y) := by
    funext y
    exact wholeLineVariance_deriv ρ hρc hρ1 y
  rw [hfirst]
  have hu := wholeLineScenery_hasDerivAt hρc hρ1 x
  have hv := wholeLineScenery_hasDerivAt hρc.deriv hρ' x
  have hd := ((hu.inner ℝ hv).const_mul 2).deriv
  simpa only [wholeLineScenery, real_inner_self_eq_norm_sq, add_comm] using hd

/-- The bulk covariance cancellation is exactly the vanishing of the
second spatial derivative of the mollified Gaussian variance. -/
theorem wholeLine_covariance_cancellation (ρ : ℝ → ℝ)
    (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) (x : ℝ)
    (hflat : deriv (fun y => deriv (wholeLineVariance ρ) y) x = 0) :
    ‖wholeLineScenery (deriv ρ) x‖ ^ 2 +
      inner ℝ (wholeLineScenery ρ x)
        (wholeLineScenery (deriv (deriv ρ)) x) = 0 := by
  rw [wholeLineVariance_second_deriv ρ hρc hρ x] at hflat
  linarith

/-- The other bulk covariance constant is equivalently a unit slope
of the mollified Gaussian variance. -/
theorem wholeLine_cross_covariance_half (ρ : ℝ → ℝ)
    (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ) (x : ℝ)
    (hslope : deriv (wholeLineVariance ρ) x = 1) :
    inner ℝ (wholeLineScenery ρ x) (wholeLineScenery (deriv ρ) x) = 1 / 2 := by
  rw [wholeLineVariance_deriv ρ hρc hρ x] at hslope
  linarith

end OperatorDerivativeRewrite.Foundation.IBMContinuousScenery
