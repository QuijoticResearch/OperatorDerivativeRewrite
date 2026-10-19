import Foundation.RiemannQuarticIntervalExp

/-! Verified real sine/cosine enclosures from the complex exponential series. -/
open Inclusion
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticIntervalTrig
open RiemannQuarticDyadic RiemannQuarticIntervalExp

def reSign (m : ℕ) : ℚ := if m%4=0 then 1 else if m%4=2 then -1 else 0
def imSign (m : ℕ) : ℚ := if m%4=1 then 1 else if m%4=3 then -1 else 0
def cosCoeff (m : ℕ) : ℚ := reSign m/(m.factorial : ℚ)
def sinCoeff (m : ℕ) : ℚ := imSign m/(m.factorial : ℚ)

theorem I_pow_re (m : ℕ) : (Complex.I^m).re=(reSign m : ℝ) := by
  rw [Complex.I_pow_eq_pow_mod]
  have hm := Nat.mod_lt m (by norm_num : 0 < 4)
  interval_cases h : m%4 <;> norm_num [reSign, h, Complex.I_pow_three]

theorem I_pow_im (m : ℕ) : (Complex.I^m).im=(imSign m : ℝ) := by
  rw [Complex.I_pow_eq_pow_mod]
  have hm := Nat.mod_lt m (by norm_num : 0 < 4)
  interval_cases h : m%4 <;> norm_num [imSign, h, Complex.I_pow_three]

theorem term_re (m : ℕ) (x : ℝ) :
    ((Complex.I*(x : ℂ))^m/(m.factorial : ℂ)).re=(cosCoeff m : ℝ)*x^m := by
  simp only [Complex.div_natCast_re, mul_pow, Complex.mul_re, ← Complex.ofReal_pow,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, I_pow_re,
    cosCoeff, Rat.cast_div, Rat.cast_natCast]
  ring

theorem term_im (m : ℕ) (x : ℝ) :
    ((Complex.I*(x : ℂ))^m/(m.factorial : ℂ)).im=(sinCoeff m : ℝ)*x^m := by
  simp only [Complex.div_natCast_im, mul_pow, Complex.mul_im, ← Complex.ofReal_pow,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, I_pow_im,
    sinCoeff, Rat.cast_div, Rat.cast_natCast]
  ring

theorem phase_error (x : ℝ) (hx : |x| ≤ 1) (n : ℕ) (hn : 0 < n) :
    ‖Complex.exp (Complex.I*(x : ℂ))-
      ∑ m ∈ Finset.range n, (Complex.I*(x : ℂ))^m/(m.factorial : ℂ)‖ ≤
      2/(n.factorial : ℝ) := by
  have he := Complex.norm_exp_sub_sum_le_exp_norm_sub_sum (Complex.I*(x : ℂ)) n
  have ht := taylor_error ‖Complex.I*(x : ℂ)‖
    (by simpa only [abs_norm, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_abs] using hx) n hn
  exact he.trans ((le_abs_self _).trans ht)

theorem cos_error (x : ℝ) (hx : |x| ≤ 1) (n : ℕ) (hn : 0 < n) :
    |Real.cos x-(∑ m ∈ Finset.range n, (cosCoeff m : ℝ)*x^m)| ≤
      2/(n.factorial : ℝ) := by
  have hr := RCLike.abs_re_le_norm (Complex.exp (Complex.I*(x : ℂ))-
    ∑ m ∈ Finset.range n, (Complex.I*(x : ℂ))^m/(m.factorial : ℂ))
  have h := hr.trans (phase_error x hx n hn)
  simpa only [RCLike.re_eq_complex_re, Complex.sub_re, Complex.re_sum, term_re,
    Complex.exp_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, mul_zero, sub_zero,
    zero_add, Real.exp_zero] using h

theorem sin_error (x : ℝ) (hx : |x| ≤ 1) (n : ℕ) (hn : 0 < n) :
    |Real.sin x-(∑ m ∈ Finset.range n, (sinCoeff m : ℝ)*x^m)| ≤
      2/(n.factorial : ℝ) := by
  have hr := RCLike.abs_im_le_norm (Complex.exp (Complex.I*(x : ℂ))-
    ∑ m ∈ Finset.range n, (Complex.I*(x : ℂ))^m/(m.factorial : ℂ))
  have h := hr.trans (phase_error x hx n hn)
  simpa only [RCLike.im_eq_complex_im, Complex.sub_im, Complex.im_sum, term_im,
    Complex.exp_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, mul_zero, sub_zero,
    zero_add, Real.exp_zero] using h

def seriesBox (coeff : ℕ → ℚ) (I : Box) (p n : ℕ) : Box :=
  add (horner (fun m => rational (coeff m) p) I p n)
    (range (-2/(n.factorial : ℚ)) (2/(n.factorial : ℚ)) p) p

theorem seriesBox_mem (coeff : ℕ → ℚ) {x y : ℝ} {I : Box} (hx : x ∈ I)
    (p n : ℕ) (he : |y-(∑ m ∈ Finset.range n, (coeff m : ℝ)*x^m)| ≤
      2/(n.factorial : ℝ)) : y ∈ seriesBox coeff I p n := by
  have hp := horner_mem hx p n (fun m => (coeff m : ℝ))
    (fun m => rational (coeff m) p) (fun m _ => rational_mem (coeff m) p)
  have he' := abs_le.mp he
  have hr : y-(∑ m ∈ Finset.range n, (coeff m : ℝ)*x^m) ∈
      range (-2/(n.factorial : ℚ)) (2/(n.factorial : ℚ)) p := by
    apply range_mem
    · simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_natCast, neg_div] using he'.1
    · simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] using he'.2
  have h := add_mem hp hr p
  have heq : (∑ m ∈ Finset.range n, (coeff m : ℝ)*x^m)+
      (y-(∑ m ∈ Finset.range n, (coeff m : ℝ)*x^m))=y := by ring
  rw [heq] at h
  exact h

def smallTrig (I : Box) (p n : ℕ) : Box × Box :=
  (seriesBox cosCoeff I p n, seriesBox sinCoeff I p n)

theorem smallTrig_mem {x : ℝ} {I : Box} (hx : x ∈ I) (hsmall : |x| ≤ 1)
    (p n : ℕ) (hn : 0 < n) :
    Real.cos x ∈ (smallTrig I p n).1 ∧ Real.sin x ∈ (smallTrig I p n).2 :=
  ⟨seriesBox_mem cosCoeff hx p n (cos_error x hsmall n hn),
   seriesBox_mem sinCoeff hx p n (sin_error x hsmall n hn)⟩

def double (J : Box × Box) (p : ℕ) : Box × Box :=
  (sub (mul J.1 J.1 p) (mul J.2 J.2 p) p,
    mul (rational 2 p) (mul J.1 J.2 p) p)

theorem double_mem {x : ℝ} {J : Box × Box}
    (hc : Real.cos x ∈ J.1) (hs : Real.sin x ∈ J.2) (p : ℕ) :
    Real.cos (2*x) ∈ (double J p).1 ∧ Real.sin (2*x) ∈ (double J p).2 := by
  have hc' := sub_mem (mul_mem hc hc p) (mul_mem hs hs p) p
  have hs' := mul_mem (rational_mem 2 p) (mul_mem hc hs p) p
  have hec : Real.cos (2*x)=Real.cos x*Real.cos x-Real.sin x*Real.sin x := by
    rw [show 2*x=x+x by ring, Real.cos_add]
  have hes : Real.sin (2*x)=2*Real.cos x*Real.sin x := by
    rw [show 2*x=x+x by ring, Real.sin_add]
    ring
  constructor
  · rw [hec]; exact hc'
  · rw [hes]; simpa only [Rat.cast_ofNat, mul_assoc, double] using hs'

def doubleLoop (J : Box × Box) (p : ℕ) : ℕ → Box × Box
  | 0 => J
  | s+1 => double (doubleLoop J p s) p

theorem doubleLoop_mem {x : ℝ} {J : Box × Box}
    (hc : Real.cos x ∈ J.1) (hs : Real.sin x ∈ J.2) (p s : ℕ) :
    Real.cos (((2^s : ℕ) : ℝ)*x) ∈ (doubleLoop J p s).1 ∧
      Real.sin (((2^s : ℕ) : ℝ)*x) ∈ (doubleLoop J p s).2 := by
  induction s with
  | zero => simpa [doubleLoop] using And.intro hc hs
  | succ s ih =>
    have h := double_mem ih.1 ih.2 p
    have he : ((2^(s+1) : ℕ) : ℝ)*x=2*(((2^s : ℕ) : ℝ)*x) := by
      push_cast
      ring
    simpa only [doubleLoop, he] using h

def scaledTrig (I : Box) (p n s : ℕ) : Box × Box :=
  doubleLoop (smallTrig (divNat I (2^s) p) p n) p s

theorem scaledTrig_mem {x : ℝ} {I : Box} (hx : x ∈ I) (p n s : ℕ)
    (hn : 0 < n) (hsmall : |x/((2^s : ℕ) : ℝ)| ≤ 1) :
    Real.cos x ∈ (scaledTrig I p n s).1 ∧ Real.sin x ∈ (scaledTrig I p n s).2 := by
  have ht := smallTrig_mem (divNat_mem hx (2^s) p) hsmall p n hn
  have hd := doubleLoop_mem ht.1 ht.2 p s
  have he : ((2^s : ℕ) : ℝ)*(x/((2^s : ℕ) : ℝ))=x := by field_simp
  simpa only [he, scaledTrig] using hd

end OperatorDerivativeRewrite.Foundation.RiemannQuarticIntervalTrig
