import Foundation.RiemannQuarticDyadic

/-! Kernel-checked finite-series, range-reduced and tiny-exponential enclosures.
No external interval calculation is assumed correct. -/
open Inclusion
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticIntervalExp
open RiemannQuarticDyadic

theorem taylor_error (x : ℝ) (hx : |x| ≤ 1) (n : ℕ) (hn : 0 < n) :
    |Real.exp x-(∑ m ∈ Finset.range n, x^m/(m.factorial : ℝ))| ≤
      2/(n.factorial : ℝ) := by
  have he := Real.exp_bound hx hn
  have hp : |x|^n ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hc : (n+1 : ℝ)/((n.factorial : ℝ)*n) ≤ 2/(n.factorial : ℝ) := by
    apply (div_le_div_iff₀ (by positivity) hf).mpr
    nlinarith
  have hb : 0 ≤ (n+1 : ℝ)/((n.factorial : ℝ)*n) := by positivity
  calc
    _ ≤ |x|^n*((n+1 : ℝ)/((n.factorial : ℝ)*n)) := by
      simpa only [Nat.cast_succ] using he
    _ ≤ 1*((n+1 : ℝ)/((n.factorial : ℝ)*n)) := by
      exact mul_le_mul_of_nonneg_right hp hb
    _ ≤ _ := by simpa only [one_mul] using hc

def smallExp (I : Box) (p n : ℕ) : Box :=
  add (sum (fun m => divNat (pow I p m) m.factorial p) p n)
    (range (-2/(n.factorial : ℚ)) (2/(n.factorial : ℚ)) p) p

theorem smallExp_mem {x : ℝ} {I : Box} (hx : x ∈ I) (hsmall : |x| ≤ 1)
    (p n : ℕ) (hn : 0 < n) : Real.exp x ∈ smallExp I p n := by
  have hp := sum_mem p n (fun i _ => divNat_mem (pow_mem hx p i) i.factorial p)
  have he := abs_le.mp (taylor_error x hsmall n hn)
  have hr : Real.exp x-(∑ m ∈ Finset.range n, x^m/(m.factorial : ℝ)) ∈
      range (-2/(n.factorial : ℚ)) (2/(n.factorial : ℚ)) p := by
    apply range_mem
    · simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_natCast, neg_div] using he.1
    · simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] using he.2
  have h := add_mem hp hr p
  have heq : (∑ m ∈ Finset.range n, x^m/(m.factorial : ℝ))+
      (Real.exp x-(∑ m ∈ Finset.range n, x^m/(m.factorial : ℝ)))=Real.exp x := by ring
  rw [heq] at h
  exact h

def smallExpHorner (I : Box) (p n : ℕ) : Box :=
  add (horner (fun m => rational (1/(m.factorial : ℚ)) p) I p n)
    (range (-2/(n.factorial : ℚ)) (2/(n.factorial : ℚ)) p) p

theorem smallExpHorner_mem {x : ℝ} {I : Box} (hx : x ∈ I) (hsmall : |x| ≤ 1)
    (p n : ℕ) (hn : 0 < n) : Real.exp x ∈ smallExpHorner I p n := by
  have hp := horner_mem hx p n (fun m => 1/(m.factorial : ℝ))
    (fun m => rational (1/(m.factorial : ℚ)) p) (fun m _ => by
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using
        rational_mem (1/(m.factorial : ℚ)) p)
  have heq : (∑ m ∈ Finset.range n, (1/(m.factorial : ℝ))*x^m) =
      ∑ m ∈ Finset.range n, x^m/(m.factorial : ℝ) := by
    apply Finset.sum_congr rfl
    intro m hm
    ring
  rw [heq] at hp
  have he := abs_le.mp (taylor_error x hsmall n hn)
  have hr : Real.exp x-(∑ m ∈ Finset.range n, x^m/(m.factorial : ℝ)) ∈
      range (-2/(n.factorial : ℚ)) (2/(n.factorial : ℚ)) p := by
    apply range_mem
    · simpa only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_natCast, neg_div] using he.1
    · simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] using he.2
  have h := add_mem hp hr p
  have heq' : (∑ m ∈ Finset.range n, x^m/(m.factorial : ℝ))+
      (Real.exp x-(∑ m ∈ Finset.range n, x^m/(m.factorial : ℝ)))=Real.exp x := by ring
  rw [heq'] at h
  exact h

def square (I : Box) (p : ℕ) : ℕ → Box
  | 0 => I
  | s+1 => mul (square I p s) (square I p s) p

theorem square_mem {x : ℝ} {I : Box} (hx : x ∈ I) (p s : ℕ) :
    x^(2^s : ℕ) ∈ square I p s := by
  induction s with
  | zero => simpa [square] using hx
  | succ s ih =>
    simpa only [square, Nat.pow_succ, pow_mul, pow_two] using mul_mem ih ih p

def scaledExp (I : Box) (p n s : ℕ) : Box :=
  square (smallExp (divNat I (2^s) p) p n) p s

theorem scaledExp_mem {x : ℝ} {I : Box} (hx : x ∈ I) (p n s : ℕ)
    (hn : 0 < n) (hsmall : |x/((2^s : ℕ) : ℝ)| ≤ 1) :
    Real.exp x ∈ scaledExp I p n s := by
  have he := smallExp_mem (divNat_mem hx (2^s) p) hsmall p n hn
  have hs := square_mem he p s
  have heq : Real.exp (x/((2^s : ℕ) : ℝ))^(2^s : ℕ)=Real.exp x := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [heq] at hs
  exact hs

def scaledExpHorner (I : Box) (p n s : ℕ) : Box :=
  square (smallExpHorner (divNat I (2^s) p) p n) p s

theorem scaledExpHorner_mem {x : ℝ} {I : Box} (hx : x ∈ I) (p n s : ℕ)
    (hn : 0 < n) (hsmall : |x/((2^s : ℕ) : ℝ)| ≤ 1) :
    Real.exp x ∈ scaledExpHorner I p n s := by
  have he := smallExpHorner_mem (divNat_mem hx (2^s) p) hsmall p n hn
  have hs := square_mem he p s
  have heq : Real.exp (x/((2^s : ℕ) : ℝ))^(2^s : ℕ)=Real.exp x := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [heq] at hs
  exact hs

theorem exp_nat_ge_two_pow (p : ℕ) : (2 : ℝ)^p ≤ Real.exp p := by
  have h : (2 : ℝ) ≤ Real.exp 1 := by have hh := Real.add_one_le_exp (1 : ℝ); linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h p
  simpa only [← Real.exp_nat_mul, mul_one] using hp

theorem tinyExp_mem (x : ℝ) (p : ℕ) (hx : x ≤ -(p : ℝ)) :
    Real.exp x ∈ range 0 (1/(2^p : ℚ)) p := by
  have hu : Real.exp x ≤ 1/(2 : ℝ)^p := by
    calc
      _ ≤ Real.exp (-(p : ℝ)) := Real.exp_le_exp.mpr hx
      _ = (Real.exp (p : ℝ))⁻¹ := Real.exp_neg _
      _ ≤ ((2 : ℝ)^p)⁻¹ :=
        (inv_le_inv₀ (Real.exp_pos _) (by positivity)).mpr (exp_nat_ge_two_pow p)
      _ = _ := by rw [one_div]
  apply range_mem (by simpa using (Real.exp_pos x).le)
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using hu

end OperatorDerivativeRewrite.Foundation.RiemannQuarticIntervalExp
