import Foundation.IBMOriginBoundaryEnergy

/-! Exact deterministic crossing control for the actual folded capped clock.
The stochastic boundary energies are constructed in the imported modules. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.IBMClippedClockCrossing
open IBMTerminalBracketWeights IBMTerminalRiemannOccupation

def cap (r x : ℝ) : ℝ := min |x| |r|

def error (r x y : ℝ) : ℝ :=
  (cap r y-cap r x)^2-IBMTerminalBracketWeights.interior (x,r)*(y-x)^2

theorem cap_increment_sq_le (r x y : ℝ) : (cap r y-cap r x)^2 ≤ (y-x)^2 := by
  have hm := abs_min_sub_min_le_max |y| |r| |x| |r|
  simp only [sub_self,abs_zero] at hm
  rw [max_eq_left (abs_nonneg (|y|-|x|))] at hm
  have hb := hm.trans (abs_abs_sub_abs_le_abs_sub y x)
  have hp := pow_le_pow_left₀ (abs_nonneg _) hb 2
  simpa only [cap,sq_abs] using hp

theorem error_bound (r x y : ℝ) : |error r x y| ≤ (y-x)^2 := by
  have hc := cap_increment_sq_le r x y
  unfold error IBMTerminalBracketWeights.interior
  split_ifs <;> apply abs_le.mpr <;> constructor <;> nlinarith [sq_nonneg (cap r y-cap r x),sq_nonneg (y-x)]

theorem error_eq_zero_of_no_crossing (r δ x y : ℝ) (hi : |y-x| ≤ δ)
    (hx : δ < |x|) (hr : δ < abs (|x|-|r|)) : error r x y = 0 := by
  have hb := abs_le.mp hi
  have hs : (|y|-|x|)^2=(y-x)^2 := by
    by_cases hxp : 0 ≤ x
    · have hyp : 0 ≤ y := by rw [abs_of_nonneg hxp] at hx; linarith [hb.1]
      rw [abs_of_nonneg hxp,abs_of_nonneg hyp]
    · have hxn : x ≤ 0 := le_of_not_ge hxp
      have hyn : y ≤ 0 := by rw [abs_of_nonpos hxn] at hx; linarith [hb.2]
      rw [abs_of_nonpos hxn,abs_of_nonpos hyn]
      ring
  have ha := abs_le.mp ((abs_abs_sub_abs_le_abs_sub y x).trans hi)
  by_cases hxr : |x| < |r|
  · have hyr : |y| ≤ |r| := by
      rw [abs_of_neg (sub_neg.mpr hxr)] at hr
      linarith [ha.2]
    simp only [error,cap,IBMTerminalBracketWeights.interior,if_pos hxr,min_eq_left hxr.le,min_eq_left hyr,one_mul]
    linarith
  · have hrx : |r| ≤ |x| := le_of_not_gt hxr
    have hry : |r| ≤ |y| := by
      rw [abs_of_nonneg (sub_nonneg.mpr hrx)] at hr
      linarith [ha.1]
    simp only [error,cap,IBMTerminalBracketWeights.interior,if_neg hxr,min_eq_right hrx,min_eq_right hry,sub_self,
      zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_mul]

theorem crossing_bound (r δ x y : ℝ) :
    |error r x y| ≤ (y-x)^2 *
      (originBand δ (x,r)+outerBand δ (x,r)+(if δ < |y-x| then 1 else 0)) := by
  have h0 : 0 ≤ originBand δ (x,r) := by unfold originBand; split_ifs <;> norm_num
  have h1 : 0 ≤ outerBand δ (x,r) := by unfold outerBand; split_ifs <;> norm_num
  have he := error_bound r x y
  by_cases hi : |y-x| ≤ δ
  · have htail : ¬δ < |y-x| := not_lt_of_ge hi
    by_cases hx : |x| ≤ δ
    · have hz : originBand δ (x,r)=1 := by simp [originBand,hx]
      rw [hz,if_neg htail]
      nlinarith [sq_nonneg (y-x)]
    · by_cases hr : abs (|x|-|r|) ≤ δ
      · have hz : outerBand δ (x,r)=1 := by simp [outerBand,hr]
        rw [hz,if_neg htail]
        nlinarith [sq_nonneg (y-x)]
      · rw [error_eq_zero_of_no_crossing r δ x y hi (lt_of_not_ge hx) (lt_of_not_ge hr),abs_zero]
        positivity
  · have ht : δ < |y-x| := lt_of_not_ge hi
    rw [if_pos ht]
    nlinarith [sq_nonneg (y-x)]

end OperatorDerivativeRewrite.Foundation.IBMClippedClockCrossing
