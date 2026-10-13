import Foundation.IBMMollifiedChainRule
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support

/-! Spatial convolution and actual first and second derivatives of a
continuous scenery path by a compactly supported C² kernel. -/
noncomputable section
open MeasureTheory
open scoped Convolution
namespace OperatorDerivativeRewrite.Foundation.IBMMollifiedScenery

variable (ρ X : ℝ → ℝ)

/-- The spatially mollified scenery of a supplied continuous path. -/
def U : ℝ → ℝ := ρ ⋆ X

/-- First spatial derivative field, represented by the derivative kernel. -/
def V : ℝ → ℝ := (deriv ρ) ⋆ X

/-- Second spatial derivative field, represented by the second derivative kernel. -/
def W : ℝ → ℝ := (deriv (deriv ρ)) ⋆ X

/-- The convolution has the derivative-kernel representation at every point. -/
theorem U_hasDerivAt (hρs : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ) (hX : Continuous X) (r : ℝ) :
    HasDerivAt (U ρ X) (V ρ X r) r := by
  exact hρs.hasDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (hρ.of_le (by norm_num)) hX.locallyIntegrable r

/-- The second convolution field is the actual derivative of the first. -/
theorem V_hasDerivAt (hρs : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ) (hX : Continuous X) (r : ℝ) :
    HasDerivAt (V ρ X) (W ρ X r) r := by
  have hρ' : ContDiff ℝ 1 (deriv ρ) := by
    simpa using (hρ.deriv' (n := 1))
  exact hρs.deriv.hasDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    hρ' hX.locallyIntegrable r

theorem deriv_U (hρs : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ) (hX : Continuous X) (r : ℝ) :
    deriv (U ρ X) r = V ρ X r :=
  (U_hasDerivAt ρ X hρs hρ hX r).deriv

theorem deriv_V (hρs : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ) (hX : Continuous X) (r : ℝ) :
    deriv (V ρ X) r = W ρ X r :=
  (V_hasDerivAt ρ X hρs hρ hX r).deriv

/-- The manuscript's exact second spatial chain rule is now instantiated
with genuine convolution derivative fields of a continuous path. -/
theorem second_chain_rule (hρs : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ) (hX : Continuous X)
    (f f₁ f₂ : ℝ → ℝ) (x r : ℝ)
    (hf : ∀ z, HasDerivAt f (f₁ z) z)
    (hf₁ : ∀ z, HasDerivAt f₁ (f₂ z) z) :
    deriv (deriv (fun q => f (x + U ρ X q))) r =
      f₂ (x + U ρ X r) * (V ρ X r) ^ 2 +
        f₁ (x + U ρ X r) * W ρ X r := by
  change deriv (deriv (IBMMollifiedChainRule.g f (U ρ X) x)) r = _
  exact IBMMollifiedChainRule.deriv_deriv_g f f₁ f₂ (U ρ X) (V ρ X) (W ρ X)
    x (U_hasDerivAt ρ X hρs hρ hX)
    (V_hasDerivAt ρ X hρs hρ hX) hf hf₁ r

end OperatorDerivativeRewrite.Foundation.IBMMollifiedScenery
