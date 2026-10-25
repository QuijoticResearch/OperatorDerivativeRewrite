import Foundation.IBMAllObservationLimits

/-! Deterministic mixed capped increments select the smaller radius, apart
from a controlled boundary crossing. No extra conditioning law is required. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.IBMClippedClockCovariation
open IBMClippedClockCrossing IBMTerminalBracketWeights

def mixedError (r s x y : ℝ) : ℝ :=
  (cap r y-cap r x)*(cap s y-cap s x)-
    (cap (min |r| |s|) y-cap (min |r| |s|) x)^2

theorem cap_min_radius (r s x : ℝ) :
    cap (min |r| |s|) x = if |r| ≤ |s| then cap r x else cap s x := by
  unfold cap
  rw [abs_of_nonneg (le_min (abs_nonneg r) (abs_nonneg s))]
  split_ifs with h
  · rw [min_eq_left h]
  · rw [min_eq_right (le_of_not_ge h)]

theorem mixed_increment_bound (r s x y : ℝ) :
    |(cap r y-cap r x)*(cap s y-cap s x)| ≤ (y-x)^2 := by
  have hr := cap_increment_sq_le r x y
  have hs := cap_increment_sq_le s x y
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg ((cap r y-cap r x)+(cap s y-cap s x)),
    sq_nonneg ((cap r y-cap r x)-(cap s y-cap s x))]

theorem mixedError_bound (r s x y : ℝ) : |mixedError r s x y| ≤ 2*(y-x)^2 := by
  have hm := abs_le.mp (mixed_increment_bound r s x y)
  have hc := cap_increment_sq_le (min |r| |s|) x y
  unfold mixedError
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (cap (min |r| |s|) y-cap (min |r| |s|) x)]

private theorem ordered_zero (r s δ x y : ℝ) (hrs : |r| ≤ |s|) (hi : |y-x| ≤ δ)
    (hr : δ < abs (|x|-|r|)) : mixedError r s x y = 0 := by
  have ha := abs_le.mp ((abs_abs_sub_abs_le_abs_sub y x).trans hi)
  rw [mixedError,cap_min_radius r s y,cap_min_radius r s x,if_pos hrs,if_pos hrs]
  by_cases hxr : |x| < |r|
  · have hyr : |y| ≤ |r| := by rw [abs_of_neg (sub_neg.mpr hxr)] at hr; linarith [ha.2]
    simp only [cap,min_eq_left hxr.le,min_eq_left hyr,min_eq_left (hxr.le.trans hrs),
      min_eq_left (hyr.trans hrs)]
    ring
  · have hrx : |r| ≤ |x| := le_of_not_gt hxr
    have hry : |r| ≤ |y| := by rw [abs_of_nonneg (sub_nonneg.mpr hrx)] at hr; linarith [ha.1]
    simp only [cap,min_eq_right hrx,min_eq_right hry,sub_self,zero_mul,zero_pow (by norm_num : (2:ℕ) ≠ 0)]

theorem mixedError_eq_zero (r s δ x y : ℝ) (hi : |y-x| ≤ δ)
    (hr : δ < abs (|x|-|r|)) (hs : δ < abs (|x|-|s|)) : mixedError r s x y = 0 := by
  by_cases hrs : |r| ≤ |s|
  · exact ordered_zero r s δ x y hrs hi hr
  · have h := ordered_zero s r δ x y (le_of_not_ge hrs) hi hs
    unfold mixedError at h ⊢
    rw [min_comm |r| |s|,mul_comm]
    exact h

theorem mixedError_crossing_bound (r s δ x y : ℝ) :
    |mixedError r s x y| ≤ 2*(y-x)^2 *
      (outerBand δ (x,r)+outerBand δ (x,s)+(if δ < |y-x| then 1 else 0)) := by
  have h0 : 0 ≤ outerBand δ (x,r) := by unfold outerBand; split_ifs <;> norm_num
  have h1 : 0 ≤ outerBand δ (x,s) := by unfold outerBand; split_ifs <;> norm_num
  have he := mixedError_bound r s x y
  by_cases hi : |y-x| ≤ δ
  · have ht : ¬δ < |y-x| := not_lt_of_ge hi
    by_cases hr : abs (|x|-|r|) ≤ δ
    · rw [show outerBand δ (x,r)=1 by simp [outerBand,hr],if_neg ht]
      nlinarith [sq_nonneg (y-x)]
    · by_cases hs : abs (|x|-|s|) ≤ δ
      · rw [show outerBand δ (x,s)=1 by simp [outerBand,hs],if_neg ht]
        nlinarith [sq_nonneg (y-x)]
      · rw [mixedError_eq_zero r s δ x y hi (lt_of_not_ge hr) (lt_of_not_ge hs),abs_zero]
        positivity
  · rw [if_pos (lt_of_not_ge hi)]
    nlinarith [sq_nonneg (y-x)]

end OperatorDerivativeRewrite.Foundation.IBMClippedClockCovariation
