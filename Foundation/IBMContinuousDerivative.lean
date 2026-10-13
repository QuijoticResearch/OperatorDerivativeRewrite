import Foundation.IBMContinuousRadius
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! Whole-line smooth convolution of the verified Gaussian L² scenery. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Convolution

namespace OperatorDerivativeRewrite.Foundation.IBMContinuousScenery
open InfiniteGaussian FractionalSpectralKernel

def wholeLineScenery (ρ : ℝ → ℝ) (x : ℝ) : GaussianL2 :=
  (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] sourceScenery) x

/-- The whole-line convolution is literally the Bochner integral of the
verified Gaussian L² scenery field. -/
theorem wholeLineScenery_eq_integral (ρ : ℝ → ℝ) (x : ℝ) :
    wholeLineScenery ρ x = ∫ r, ρ (x - r) • sourceScenery r := by
  exact convolution_lsmul_swap

theorem sourceScenery_locallyIntegrable :
    LocallyIntegrable sourceScenery volume :=
  sourceScenery_continuous.locallyIntegrable

/-- Differentiation of the genuine whole-line Gaussian L² convolution
with a compactly supported C¹ spatial kernel. -/
theorem wholeLineScenery_hasDerivAt
    {ρ : ℝ → ℝ} (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ) (x : ℝ) :
    HasDerivAt
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] sourceScenery)
      ((deriv ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] sourceScenery) x) x :=
  hρc.hasDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    hρ sourceScenery_locallyIntegrable x

theorem wholeLineScenery_deriv (ρ : ℝ → ℝ)
    (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ) (x : ℝ) :
    deriv (wholeLineScenery ρ) x = wholeLineScenery (deriv ρ) x := by
  exact (wholeLineScenery_hasDerivAt hρc hρ x).deriv

theorem wholeLineScenery_deriv_integral (ρ : ℝ → ℝ)
    (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ) (x : ℝ) :
    deriv (wholeLineScenery ρ) x =
      ∫ r, deriv ρ (x - r) • sourceScenery r := by
  rw [wholeLineScenery_deriv ρ hρc hρ x,
    wholeLineScenery_eq_integral]

/-- The second spatial derivative exists in Gaussian L² for a compactly
supported C² kernel and is convolution with its second derivative. -/
theorem wholeLineScenery_second_deriv (ρ : ℝ → ℝ)
    (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) (x : ℝ) :
    deriv (fun y => deriv (wholeLineScenery ρ) y) x =
      wholeLineScenery (deriv (deriv ρ)) x := by
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by norm_num)
  have hρ' : ContDiff ℝ 1 (deriv ρ) := by
    exact (contDiff_succ_iff_deriv.mp hρ).2.2
  have hfirst : (fun y => deriv (wholeLineScenery ρ) y) =
      wholeLineScenery (deriv ρ) := by
    funext y
    exact wholeLineScenery_deriv ρ hρc hρ1 y
  rw [hfirst]
  exact wholeLineScenery_deriv (deriv ρ) hρc.deriv hρ' x

theorem wholeLineScenery_second_deriv_integral (ρ : ℝ → ℝ)
    (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) (x : ℝ) :
    deriv (fun y => deriv (wholeLineScenery ρ) y) x =
      ∫ r, deriv (deriv ρ) (x - r) • sourceScenery r := by
  rw [wholeLineScenery_second_deriv ρ hρc hρ x,
    wholeLineScenery_eq_integral]

end OperatorDerivativeRewrite.Foundation.IBMContinuousScenery
