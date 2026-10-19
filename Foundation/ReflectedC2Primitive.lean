import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Mul
/-! Removing the origin slope makes an absolute-value reflection genuinely C2.
This deterministic theorem supplies the smooth scalar core for a reflected Ito/Tanaka proof. -/
noncomputable section
open Set Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.ReflectedC2Primitive

def corrected (f : ℝ → ℝ) (x : ℝ) : ℝ := f |x| - |x| * deriv f 0
def slope (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x < 0 then deriv f 0-deriv f (-x) else deriv f x-deriv f 0

theorem glue_zero {F p n : ℝ → ℝ} {d : ℝ}
    (hp : HasDerivAt p d 0) (hn : HasDerivAt n d 0)
    (heP : ∀ x, 0 ≤ x → F x = p x) (heN : ∀ x, x ≤ 0 → F x = n x) :
    HasDerivAt F d 0 := by
  have hP : HasDerivWithinAt F d (Ici 0) 0 :=
    hp.hasDerivWithinAt.congr (fun x hx => heP x hx) (heP 0 le_rfl)
  have hN : HasDerivWithinAt F d (Iic 0) 0 :=
    hn.hasDerivWithinAt.congr (fun x hx => heN x hx) (heN 0 le_rfl)
  have h := hN.union hP
  rw [Iic_union_Ici] at h
  exact h.hasDerivAt (by simp)

theorem corrected_pos (f : ℝ → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    corrected f x = f x-x*deriv f 0 := by rw [corrected, abs_of_nonneg hx]

theorem corrected_neg (f : ℝ → ℝ) {x : ℝ} (hx : x ≤ 0) :
    corrected f x = f (-x)+x*deriv f 0 := by rw [corrected, abs_of_nonpos hx]; ring

theorem slope_pos (f : ℝ → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    slope f x = deriv f x-deriv f 0 := by simp [slope, not_lt.mpr hx]

theorem slope_neg (f : ℝ → ℝ) {x : ℝ} (hx : x ≤ 0) :
    slope f x = deriv f 0-deriv f (-x) := by
  rcases hx.lt_or_eq with h | h
  · simp [slope,h]
  · subst x; simp [slope]

theorem corrected_hasDerivAt {f : ℝ → ℝ} (hf : Differentiable ℝ f) (x : ℝ) :
    HasDerivAt (corrected f) (slope f x) x := by
  have hp (r : ℝ) : HasDerivAt (fun y => f y-y*deriv f 0) (deriv f r-deriv f 0) r := by
    have h := (hf r).hasDerivAt.sub ((hasDerivAt_id r).mul_const (deriv f 0))
    change HasDerivAt (fun y => f y-y*deriv f 0) (deriv f r-1*deriv f 0) r at h
    rw [one_mul] at h
    exact h
  have hn (r : ℝ) : HasDerivAt (fun y => f (-y)+y*deriv f 0) (deriv f 0-deriv f (-r)) r := by
    convert ((hf (-r)).hasDerivAt.comp r (hasDerivAt_neg r)).add
      ((hasDerivAt_id r).mul_const (deriv f 0)) using 1 <;>
      first | rfl | ring
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [slope_neg f hx.le]
    apply (hn x).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hx] with y hy
    exact corrected_neg f hy.le
  · subst x
    rw [slope_pos f le_rfl, sub_self]
    exact glue_zero (by simpa using hp 0) (by simpa using hn 0)
      (fun y hy => corrected_pos f hy) (fun y hy => corrected_neg f hy)
  · rw [slope_pos f hx.le]
    apply (hp x).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact corrected_pos f hy.le

theorem slope_hasDerivAt {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    HasDerivAt (slope f) (deriv (deriv f) |x|) x := by
  have hp (r : ℝ) : HasDerivAt (fun y => deriv f y-deriv f 0) (deriv (deriv f) r) r :=
    (hf.differentiable_deriv_two r).hasDerivAt.sub_const _
  have hn (r : ℝ) : HasDerivAt (fun y => deriv f 0-deriv f (-y)) (deriv (deriv f) (-r)) r := by
    convert ((hf.differentiable_deriv_two (-r)).hasDerivAt.comp r (hasDerivAt_neg r)).const_sub
      (deriv f 0) using 1 <;> first | rfl | ring
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [abs_of_neg hx]
    apply (hn x).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hx] with y hy
    exact slope_neg f hy.le
  · subst x
    rw [abs_zero]
    exact glue_zero (hp 0) (by simpa using hn 0)
      (fun y hy => slope_pos f hy) (fun y hy => slope_neg f hy)
  · rw [abs_of_pos hx]
    apply (hp x).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact slope_pos f hy.le

theorem corrected_C2 {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 2 (corrected f) := by
  have h1 : deriv (corrected f) = slope f :=
    funext fun x => (corrected_hasDerivAt (hf.differentiable (by norm_num)) x).deriv
  have h2 : deriv (slope f) = fun x => deriv (deriv f) |x| :=
    funext fun x => (slope_hasDerivAt hf x).deriv
  have hs : ContDiff ℝ 1 (slope f) := contDiff_one_iff_deriv.mpr
    ⟨fun x => (slope_hasDerivAt hf x).differentiableAt, by
      rw [h2]
      exact ((hf.deriv' (n := 1)).continuous_deriv_one).comp continuous_abs⟩
  rw [show (2 : WithTop ℕ∞) = 1+1 by norm_num, contDiff_succ_iff_deriv]
  exact ⟨fun x => (corrected_hasDerivAt (hf.differentiable (by norm_num)) x).differentiableAt,
    by simp, by rw [h1]; exact hs⟩

theorem corrected_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    deriv (corrected f) = slope f := funext fun x => (corrected_hasDerivAt hf x).deriv

theorem corrected_second_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    deriv (deriv (corrected f)) x = deriv (deriv f) |x| := by
  rw [corrected_deriv (hf.differentiable (by norm_num))]
  exact (slope_hasDerivAt hf x).deriv

theorem corrected_deriv_bound {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C : ℝ}
    (hC : ∀ x, ‖deriv f x‖ ≤ C) (x : ℝ) : ‖deriv (corrected f) x‖ ≤ 2*C := by
  rw [corrected_deriv hf]
  by_cases hx : x < 0
  · rw [slope, if_pos hx]
    exact (norm_sub_le _ _).trans ((add_le_add (hC 0) (hC (-x))).trans_eq (by ring))
  · rw [slope, if_neg hx]
    exact (norm_sub_le _ _).trans ((add_le_add (hC x) (hC 0)).trans_eq (by ring))

theorem corrected_second_deriv_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {C : ℝ}
    (hC : ∀ x, ‖deriv (deriv f) x‖ ≤ C) (x : ℝ) :
    ‖deriv (deriv (corrected f)) x‖ ≤ C := by
  rw [corrected_second_deriv hf]
  exact hC |x|

end OperatorDerivativeRewrite.Foundation.ReflectedC2Primitive
