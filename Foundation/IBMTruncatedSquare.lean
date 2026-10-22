import Foundation.IBMIntrinsicUnboundedChain
import Foundation.GaussianSobolevPrimitives

/-! A C1 square extension with bounded derivative for native IBM products. -/
noncomputable section
open MeasureTheory Set
namespace OperatorDerivativeRewrite.Foundation.IBMTruncatedSquare
set_option backward.isDefEq.respectTransparency false

def clamp (R x : ℝ) : ℝ := max (-R) (min x R)

theorem clamp_continuous (R : ℝ) : Continuous (clamp R) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem clamp_eq (R x : ℝ) (hx : |x| ≤ R) : clamp R x = x := by
  have h := abs_le.mp hx
  simp only [clamp,min_eq_left h.2,max_eq_right h.1]

theorem clamp_bound (R : ℝ) (hR : 0 ≤ R) (x : ℝ) : ‖clamp R x‖ ≤ R := by
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

def squareExtension (R : ℝ) : ℝ → ℝ :=
  GaussianSobolevFixedSupport.primitive 0 (fun x => 2*clamp R x)

theorem squareExtension_hasDerivAt (R x : ℝ) :
    HasDerivAt (squareExtension R) (2*clamp R x) x :=
  GaussianSobolevFixedSupport.primitive_hasDerivAt
    (continuous_const.mul (clamp_continuous R)) 0 x

theorem derivative_bound (R : ℝ) (hR : 0 ≤ R) (x : ℝ) : ‖2*clamp R x‖ ≤ 2*R := by
  rw [norm_mul,show ‖(2 : ℝ)‖ = 2 from by norm_num]
  exact mul_le_mul_of_nonneg_left (clamp_bound R hR x) (by norm_num)

theorem clamp_between (R x : ℝ) (hR : 0 ≤ R) (hx : |x| ≤ R)
    {y : ℝ} (hy : y ∈ uIcc 0 x) : clamp R y = y := by
  apply clamp_eq
  apply abs_le.mpr
  have hb := abs_le.mp hx
  rcases le_total 0 x with hx0 | hx0
  · rw [uIcc_of_le hx0] at hy
    exact ⟨by linarith [hy.1], hy.2.trans hb.2⟩
  · rw [uIcc_of_ge hx0] at hy
    exact ⟨hb.1.trans hy.1, by linarith [hy.2]⟩

theorem squareExtension_eq (R x : ℝ) (hR : 0 ≤ R) (hx : |x| ≤ R) :
    squareExtension R x = x^2 := by
  change (∫ y in (0 : ℝ)..x, 2*clamp R y) = x^2
  calc
    (∫ y in (0 : ℝ)..x, 2*clamp R y) = ∫ y in (0 : ℝ)..x, 2*y := by
      apply intervalIntegral.integral_congr
      intro y hy
      change 2*clamp R y = 2*y
      rw [clamp_between R x hR hx hy]
    _ = x^2 := by
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := (0 : ℝ)) (b := x) (f := fun y : ℝ => y^2) (f' := fun y : ℝ => 2*y)
        (fun y _ => by
          convert (hasDerivAt_id y).mul (hasDerivAt_id y) using 1 <;>
            simp [pow_two,two_mul] <;> rfl)
        ((continuous_const.mul continuous_id).intervalIntegrable 0 x)
      simpa using h

end OperatorDerivativeRewrite.Foundation.IBMTruncatedSquare
