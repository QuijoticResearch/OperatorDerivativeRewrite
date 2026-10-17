import Foundation.GaussianShearSectorMoments
import Mathlib.Analysis.Complex.ExponentialBounds

/-! A reversed spectral centroid inequality for the complete lattice spectrum
of one fixed actual Navier–Stokes shear, with positive denominators. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.GaussianShearCentroid
open GaussianFourierJets GaussianPeriodicHeat GaussianInfiniteShear GaussianFourierCoefficient
open GaussianShearSectorMoments
set_option backward.isDefEq.respectTransparency false

theorem first_sector_lower (p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    8*Real.exp (-2*(1+nu*t)) ≤ moment 0 p nu t := by
  have hb := bound_summable (2*p) (2*(1+nu*t)) (by positivity)
  have h := hb.sum_le_tsum ({(1 : ℤ), -1} : Finset ℤ) (fun n _ => by
    unfold bound
    positivity)
  have he : (∑ n ∈ ({(1 : ℤ), -1} : Finset ℤ), bound (2*p) (2*(1+nu*t)) n) =
      2*Real.exp (-2*(1+nu*t)) := by
    norm_num [bound]
    congr 1
    ring
  rw [he] at h
  rw [sector_zero_exact p nu t hs]
  nlinarith

theorem low_factor (nu t : ℝ) :
    Real.exp (-2*(1+nu*t)) = Real.exp (-2)*(amplitude nu t)^2 := by
  unfold amplitude
  rw [pow_two, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem low_gap_constant : (1 : ℝ) < 16*Real.exp (-2) := by
  have he : Real.exp (2 : ℝ) < 16 := by
    have h := Real.exp_one_lt_three
    have hp := Real.exp_pos (1 : ℝ)
    rw [show (2 : ℝ) = 1+1 by norm_num, Real.exp_add]
    nlinarith
  have hm := mul_lt_mul_of_pos_left he (Real.exp_pos (-2 : ℝ))
  rw [← Real.exp_add] at hm
  norm_num at hm
  nlinarith

theorem second_sector_positive (p : ℕ) (nu t : ℝ) (hs : 0 < 1+nu*t) :
    0 < moment 1 p nu t := by
  rw [sector_one_exact p nu t hs]
  have ha : 0 < amplitude nu t := Real.exp_pos _
  positivity

theorem enstrophy_order (nu t : ℝ) (hs : 0 < 1+nu*t) :
    moment 1 1 nu t < moment 0 1 nu t := by
  have hl := first_sector_lower 1 nu t hs
  rw [low_factor] at hl
  rw [sector_one_exact 1 nu t hs]
  have ha : 0 < amplitude nu t := Real.exp_pos _
  have hp : 0 < (16*Real.exp (-2)-1)*(amplitude nu t)^2 :=
    mul_pos (sub_pos.mpr low_gap_constant) (sq_pos_of_pos ha)
  nlinarith

theorem integer_power_order (n : ℤ) : |(n : ℝ)|^2 ≤ |(n : ℝ)|^4 := by
  by_cases hn : n = 0
  · simp [hn]
  have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  have h2 : 1 ≤ |(n : ℝ)|^2 := by nlinarith [sq_nonneg (|(n : ℝ)|-1)]
  nlinarith [mul_nonneg (sq_nonneg |(n : ℝ)|) (sub_nonneg.mpr h2)]

theorem dissipation_order (nu t : ℝ) (hs : 0 < 1+nu*t) :
    moment 0 1 nu t < moment 0 2 nu t := by
  let s := 2*(1+nu*t)
  have hs0 : 0 < s := by dsimp [s]; positivity
  have h4 := bound_summable 4 s hs0
  have h2 := bound_summable 2 s hs0
  have hn (n : ℤ) : 0 ≤ bound 4 s n-bound 2 s n := by
    unfold bound
    rw [← sub_mul]
    exact mul_nonneg (sub_nonneg.mpr (integer_power_order n)) (Real.exp_pos _).le
  have hh := (h4.sub h2).sum_le_tsum ({(2 : ℤ)} : Finset ℤ) (fun n _ => hn n)
  simp only [Finset.sum_singleton, h4.tsum_sub h2] at hh
  have hp : 0 < bound 4 s (2 : ℤ)-bound 2 s (2 : ℤ) := by
    unfold bound
    rw [← sub_mul]
    exact mul_pos (by norm_num) (Real.exp_pos _)
  rw [sector_zero_exact 1 nu t hs, sector_zero_exact 2 nu t hs]
  change 4*(∑' n : ℤ, bound 2 s n) < 4*(∑' n : ℤ, bound 4 s n)
  nlinarith

def binaryRatio (a b d e : ℝ) : ℝ :=
  let T := a+b
  let e0 := a/T-1/2
  let e1 := b/T-1/2
  (e0*d/T+e1*e/T)/(((d+e)/T)*(e0^2+e1^2))

theorem binaryRatio_eq (a b d : ℝ) (hb : 0 < b) (hba : b < a) (had : a < d) :
    binaryRatio a b d b = (a+b)*(d-b)/((d+b)*(a-b)) := by
  have ha : 0 < a := hb.trans hba
  have hd : 0 < d := ha.trans had
  have hT : a+b ≠ 0 := ne_of_gt (by positivity)
  have hD : d+b ≠ 0 := ne_of_gt (by positivity)
  have hdiff : a-b ≠ 0 := ne_of_gt (sub_pos.mpr hba)
  have he0 : a/(a+b)-1/2 = (a-b)/(2*(a+b)) := by field_simp; ring
  have he1 : b/(a+b)-1/2 = -(a-b)/(2*(a+b)) := by field_simp; ring
  unfold binaryRatio
  dsimp only
  rw [he0, he1]
  field_simp
  <;> ring

theorem binaryRatio_gt_one (a b d : ℝ) (hb : 0 < b) (hba : b < a) (had : a < d) :
    1 < binaryRatio a b d b := by
  rw [binaryRatio_eq a b d hb hba had]
  have ha : 0 < a := hb.trans hba
  have hd : 0 < d := ha.trans had
  have hden : 0 < (d+b)*(a-b) := mul_pos (by positivity) (sub_pos.mpr hba)
  rw [lt_div_iff₀ hden]
  have hp : 0 < 2*b*(d-a) := by positivity
  nlinarith

def centroid (nu t : ℝ) : ℝ :=
  binaryRatio (moment 0 1 nu t) (moment 1 1 nu t) (moment 0 2 nu t) (moment 1 2 nu t)

theorem centroid_gt_one (nu t : ℝ) (hs : 0 < 1+nu*t) : 1 < centroid nu t := by
  have he : moment 1 2 nu t = moment 1 1 nu t := by
    rw [sector_one_exact 2 nu t hs, sector_one_exact 1 nu t hs]
  rw [centroid, he]
  exact binaryRatio_gt_one _ _ _ (second_sector_positive 1 nu t hs)
    (enstrophy_order nu t hs) (dissipation_order nu t hs)

theorem centroid_gt_one_nonnegative (nu t : ℝ) (hnu : 0 ≤ nu) (ht : 0 ≤ t) :
    1 < centroid nu t := centroid_gt_one nu t (positive_parameter nu t hnu ht)

def sourceExpression (a b d e : ℝ) : ℝ :=
  let T := a+b
  let p0 := a/T
  let p1 := b/T
  let e0 := p0-1/2
  let e1 := p1-1/2
  (e0*(d/a)*p0+e1*(e/b)*p1)/(((d+e)/T)*(e0^2+e1^2))

theorem sourceExpression_eq (a b d e : ℝ) (ha : 0 < a) (hb : 0 < b) :
    sourceExpression a b d e = binaryRatio a b d e := by
  have ha0 := ne_of_gt ha
  have hb0 := ne_of_gt hb
  have hT : a+b ≠ 0 := ne_of_gt (add_pos ha hb)
  unfold sourceExpression binaryRatio
  dsimp only
  congr 1
  field_simp
  <;> ring

def sourceCentroid (nu t : ℝ) : ℝ := sourceExpression
  (moment 0 1 nu t) (moment 1 1 nu t) (moment 0 2 nu t) (moment 1 2 nu t)

theorem sourceCentroid_eq (nu t : ℝ) (hs : 0 < 1+nu*t) :
    sourceCentroid nu t = centroid nu t := by
  exact sourceExpression_eq _ _ _ _
    ((second_sector_positive 1 nu t hs).trans (enstrophy_order nu t hs))
    (second_sector_positive 1 nu t hs)

theorem sourceCentroid_gt_one (nu t : ℝ) (hs : 0 < 1+nu*t) :
    1 < sourceCentroid nu t := by
  rw [sourceCentroid_eq nu t hs]
  exact centroid_gt_one nu t hs

end OperatorDerivativeRewrite.Foundation.GaussianShearCentroid
