import Foundation.TridiagonalMomentIntertwining

/-! Changing the last diagonal preserves eight moments and steers the ninth. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.TridiagonalNinthSteering
open TridiagonalMomentIntertwining Matrix
set_option maxHeartbeats 5000000
set_option maxRecDepth 2048

theorem monic_prefix (a b c f u v w z : ℝ) (n : ℕ) (hn : n ≤ 8) :
    ((monic a b c f u v w z)^n) 0 0 = ((monic a b c 0 u v w z)^n) 0 0 := by
  interval_cases n <;>
    norm_num [pow_succ,Matrix.mul_apply,Fin.sum_univ_succ,monic,Matrix.one_apply] <;> ring

theorem monic_ninth (a b c f u v w z : ℝ) :
    ((monic a b c f u v w z)^9) 0 0 =
      ((monic a b c 0 u v w z)^9) 0 0+u*v*w*z*f := by
  norm_num [pow_succ,Matrix.mul_apply,Fin.sum_univ_succ,monic,Matrix.one_apply]
  ring

theorem symmetric_prefix (a b c f r s e h : ℝ) (n : ℕ) (hn : n ≤ 8) :
    ((symmetric a b c f r s e h)^n) 0 0 = ((symmetric a b c 0 r s e h)^n) 0 0 := by
  rw [coordinate_moment,coordinate_moment]
  exact monic_prefix _ _ _ _ _ _ _ _ n hn

theorem symmetric_ninth (a b c f r s e h : ℝ) :
    ((symmetric a b c f r s e h)^9) 0 0 =
      ((symmetric a b c 0 r s e h)^9) 0 0+r^2*s^2*e^2*h^2*f := by
  rw [coordinate_moment,coordinate_moment]
  exact monic_ninth _ _ _ _ _ _ _ _

end OperatorDerivativeRewrite.Foundation.TridiagonalNinthSteering
