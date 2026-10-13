import Foundation.IBMContinuousComposition
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Exact second spatial chain rule for a smooth candidate scenery field.
The hypotheses state actual first and second spatial derivatives; no
identification with Malliavin differentiation is made. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.IBMMollifiedChainRule

variable (f f₁ f₂ U V W : ℝ → ℝ) (x : ℝ)

/-- The scenery-composed test function at a fixed spatial shift. -/
def g (r : ℝ) : ℝ := f (x + U r)

theorem g_hasDerivAt
    (hU : ∀ r, HasDerivAt U (V r) r)
    (hf : ∀ z, HasDerivAt f (f₁ z) z) (r : ℝ) :
    HasDerivAt (g f U x) (f₁ (x + U r) * V r) r := by
  have hinner : HasDerivAt (fun q => x + U q) (V r) r := by
    convert (hasDerivAt_const r x).add (hU r) using 1
    simp only [zero_add]
  change HasDerivAt (fun q => f (x + U q)) (f₁ (x + U r) * V r) r
  exact (hf (x + U r)).comp r hinner

theorem g_second_hasDerivAt
    (hU : ∀ r, HasDerivAt U (V r) r)
    (hV : ∀ r, HasDerivAt V (W r) r)
    (hf₁ : ∀ z, HasDerivAt f₁ (f₂ z) z) (r : ℝ) :
    HasDerivAt (fun q => f₁ (x + U q) * V q)
      (f₂ (x + U r) * V r ^ 2 + f₁ (x + U r) * W r) r := by
  have hinner : HasDerivAt (fun q => x + U q) (V r) r := by
    convert (hasDerivAt_const r x).add (hU r) using 1
    simp only [zero_add]
  have hfirst := (hf₁ (x + U r)).comp r hinner
  convert hfirst.mul (hV r) using 1
  · funext q
    rfl
  · simp only [Function.comp_def]
    ring

/-- The exact second spatial derivative formula needed for mollified IBM. -/
theorem deriv_deriv_g
    (hU : ∀ r, HasDerivAt U (V r) r)
    (hV : ∀ r, HasDerivAt V (W r) r)
    (hf : ∀ z, HasDerivAt f (f₁ z) z)
    (hf₁ : ∀ z, HasDerivAt f₁ (f₂ z) z) (r : ℝ) :
    deriv (deriv (g f U x)) r =
      f₂ (x + U r) * V r ^ 2 + f₁ (x + U r) * W r := by
  have hd : deriv (g f U x) = fun q => f₁ (x + U q) * V q := by
    funext q
    exact (g_hasDerivAt f f₁ U V x hU hf q).deriv
  rw [hd]
  exact (g_second_hasDerivAt f₁ f₂ U V W x hU hV hf₁ r).deriv

end OperatorDerivativeRewrite.Foundation.IBMMollifiedChainRule
