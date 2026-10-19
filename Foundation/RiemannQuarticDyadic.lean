import Foundation.RiemannQuarticTaylorJets
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

/-! Outward rounding for the concrete quartic-flow interval calculation.
Arithmetic and rational approximation reuse Mathlib's dyadic intervals. -/
open Inclusion
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticDyadic
abbrev Box := Interval Dyadic

def down (q : ℚ) (p : ℕ) : Dyadic := q.toDyadic p

def up (q : ℚ) (p : ℕ) : Dyadic :=
  let d := down q p
  if d.toRat=q then d else d+Dyadic.step p

theorem down_le (q : ℚ) (p : ℕ) : (down q p).toReal ≤ (q : ℝ) := by
  exact Rat.cast_le.mpr Rat.toRat_toDyadic_le

theorem le_up (q : ℚ) (p : ℕ) : (q : ℝ) ≤ (up q p).toReal := by
  have h := IntervalDyadicReal.ratCast_mem q p
  change (q : ℝ) ∈ (Interval.Icc (down q p) (up q p)).map Dyadic.toReal at h
  exact Interval.le_map_ub Dyadic.toReal h

def round (I : Box) (p : ℕ) : Box where
  lb := I.lb.map (fun d => down d.toRat p)
  ub := I.ub.map (fun d => up d.toRat p)

theorem round_mem {x : ℝ} {I : Box} (hx : x ∈ I) (p : ℕ) : x ∈ round I p := by
  change x ∈ I.map Dyadic.toReal at hx
  change x ∈ (round I p).map Dyadic.toReal
  rw [Interval.mem_map_iff] at hx ⊢
  constructor
  · intro a ha
    cases h : I.lb with
    | bot => simp [round, h] at ha
    | coe b =>
      have hab : down b.toRat p=a := by simpa [round, h] using ha
      subst a
      exact (down_le b.toRat p).trans (hx.1 b h)
  · intro a ha
    cases h : I.ub with
    | top => simp [round, h] at ha
    | coe b =>
      have hab : up b.toRat p=a := by simpa [round, h] using ha
      subst a
      exact (hx.2 b h).trans (le_up b.toRat p)

def rational (q : ℚ) (p : ℕ) : Box := IntervalDyadicReal.rat q p

theorem rational_mem (q : ℚ) (p : ℕ) : (q : ℝ) ∈ rational q p :=
  IntervalDyadicReal.ratCast_mem q p

def add (I J : Box) (p : ℕ) : Box := round (I.add J) p
def neg (I : Box) : Box := I.neg
def sub (I J : Box) (p : ℕ) : Box := round (I.sub J) p
def mul (I J : Box) (p : ℕ) : Box := round (I.mul J) p
def divNat (I : Box) (n p : ℕ) : Box := mul I (rational (1/(n : ℚ)) p) p

theorem add_mem {x y : ℝ} {I J : Box} (hx : x ∈ I) (hy : y ∈ J) (p : ℕ) :
    x+y ∈ add I J p :=
  round_mem (IntervalDyadicReal.add_mem hx hy) p

theorem neg_mem {x : ℝ} {I : Box} (hx : x ∈ I) : -x ∈ neg I :=
  IntervalDyadicReal.neg_mem hx

theorem sub_mem {x y : ℝ} {I J : Box} (hx : x ∈ I) (hy : y ∈ J) (p : ℕ) :
    x-y ∈ sub I J p :=
  round_mem (IntervalDyadicReal.sub_mem hx hy) p

theorem mul_mem {x y : ℝ} {I J : Box} (hx : x ∈ I) (hy : y ∈ J) (p : ℕ) :
    x*y ∈ mul I J p :=
  round_mem (IntervalDyadicReal.mul_mem hx hy) p

theorem divNat_mem {x : ℝ} {I : Box} (hx : x ∈ I) (n p : ℕ) :
    x/(n : ℝ) ∈ divNat I n p := by
  have h := mul_mem hx (rational_mem (1/(n : ℚ)) p) p
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, mul_one_div, divNat] using h

def pow (I : Box) (p : ℕ) : ℕ → Box
  | 0 => rational 1 p
  | n+1 => mul (pow I p n) I p

theorem pow_mem {x : ℝ} {I : Box} (hx : x ∈ I) (p n : ℕ) : x^n ∈ pow I p n := by
  induction n with
  | zero => simpa [pow] using rational_mem 1 p
  | succ n ih => simpa only [pow, pow_succ] using mul_mem ih hx p

def sum (F : ℕ → Box) (p : ℕ) : ℕ → Box
  | 0 => rational 0 p
  | n+1 => add (sum F p n) (F n) p

theorem sum_mem {f : ℕ → ℝ} {F : ℕ → Box} (p n : ℕ)
    (h : ∀ i < n, f i ∈ F i) : (∑ i ∈ Finset.range n, f i) ∈ sum F p n := by
  induction n with
  | zero => simpa [sum] using rational_mem 0 p
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact add_mem (ih (fun i hi => h i (by omega))) (h n (by omega)) p

def horner (F : ℕ → Box) (I : Box) (p : ℕ) : ℕ → Box
  | 0 => rational 0 p
  | n+1 => add (F 0) (mul I (horner (fun i => F (i+1)) I p n) p) p

theorem horner_mem {x : ℝ} {I : Box} (hx : x ∈ I) (p n : ℕ)
    (f : ℕ → ℝ) (F : ℕ → Box) (h : ∀ i < n, f i ∈ F i) :
    (∑ i ∈ Finset.range n, f i*x^i) ∈ horner F I p n := by
  induction n generalizing f F with
  | zero => simpa [horner] using rational_mem 0 p
  | succ n ih =>
    have ht := ih (fun i => f (i+1)) (fun i => F (i+1))
      (fun i hi => h (i+1) (by omega))
    have hr := add_mem (h 0 (by omega)) (mul_mem hx ht p) p
    have heq : (∑ i ∈ Finset.range (n+1), f i*x^i) =
        f 0+x*(∑ i ∈ Finset.range n, f (i+1)*x^i) := by
      rw [Finset.sum_range_succ']
      simp only [pow_zero, mul_one, Finset.mul_sum, pow_succ]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [heq]
    exact hr

def range (a b : ℚ) (p : ℕ) : Box := Interval.Icc (down a p) (up b p)

theorem range_mem {a b : ℚ} {x : ℝ} (ha : (a : ℝ) ≤ x) (hb : x ≤ (b : ℝ)) (p : ℕ) :
    x ∈ range a b p :=
  Interval.mem_map_Icc Dyadic.toReal ((down_le a p).trans ha) (hb.trans (le_up b p))

end OperatorDerivativeRewrite.Foundation.RiemannQuarticDyadic
