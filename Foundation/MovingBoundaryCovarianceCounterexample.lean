import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-! A moving-support correction is necessary when differentiating the interior
conditional mean on the corridor x²+y²≤1, even for zero potential. -/
noncomputable section
open MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.MovingBoundaryCovarianceCounterexample

def uniformSquareMean (r : ℝ) : ℝ := (∫ y in (-r)..r, y^2) / (2*r)

theorem uniformSquareMean_eq (r : ℝ) (hr : r ≠ 0) : uniformSquareMean r = r^2/3 := by
  rw [uniformSquareMean, integral_pow]
  field_simp
  ring

def corridorSquareMean (x : ℝ) : ℝ := uniformSquareMean (Real.sqrt (1-x^2))

theorem corridorSquareMean_eq {x : ℝ} (hx : x^2 < 1) :
    corridorSquareMean x = (1-x^2)/3 := by
  rw [corridorSquareMean, uniformSquareMean_eq _
    (ne_of_gt (Real.sqrt_pos.mpr (by linarith))), Real.sq_sqrt (by linarith)]

/-- The covariance-only formula with V=0 would predict zero; the actual mean varies. -/
theorem corridor_mean_changes :
    corridorSquareMean (0 : ℝ) = 1/3 ∧ corridorSquareMean (1/2 : ℝ) = 1/4 ∧
      corridorSquareMean (0 : ℝ) ≠ corridorSquareMean (1/2 : ℝ) := by
  have h0 := corridorSquareMean_eq (x := 0) (by norm_num)
  have h1 := corridorSquareMean_eq (x := 1/2) (by norm_num)
  norm_num at h0 h1
  exact ⟨h0, h1, by rw [h0, h1]; norm_num⟩

theorem polynomial_mean_derivative (x : ℝ) :
    HasDerivAt (fun z : ℝ => (1-z^2)/3) (-2*x/3) x := by
  have hd := ((hasDerivAt_pow 2 x).const_sub 1).div_const 3
  convert hd using 1 <;> simp <;> ring

theorem corridor_mean_derivative {x : ℝ} (hx : x^2 < 1) :
    HasDerivAt corridorSquareMean (-2*x/3) x := by
  have hnear : ∀ᶠ z : ℝ in nhds x, z^2 < 1 :=
    (isOpen_lt (continuous_id.pow 2) continuous_const).mem_nhds hx
  apply (polynomial_mean_derivative x).congr_of_eventuallyEq
  exact hnear.mono (fun z hz => corridorSquareMean_eq hz)

theorem zero_potential_covariance_identity_fails :
    deriv corridorSquareMean (1/2 : ℝ) ≠ 0 := by
  rw [(corridor_mean_derivative (x := 1/2) (by norm_num)).deriv]
  norm_num

end OperatorDerivativeRewrite.Foundation.MovingBoundaryCovarianceCounterexample
