import Foundation.RiemannQuarticIntervalJets
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Actual scaled sine/cosine derivative channels and their interval enclosures. -/
open scoped ContDiff
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticTrigJets
open RiemannQuarticDyadic RiemannQuarticIntervalTrig RiemannQuarticTaylorJets

theorem reSign_succ (n : ℕ) : reSign (n+1) = -imSign n := by
  have hn := Nat.mod_lt n (by norm_num : 0 < 4)
  interval_cases h : n%4 <;> norm_num [reSign, imSign, Nat.add_mod, h]

theorem imSign_succ (n : ℕ) : imSign (n+1) = reSign n := by
  have hn := Nat.mod_lt n (by norm_num : 0 < 4)
  interval_cases h : n%4 <;> norm_num [reSign, imSign, Nat.add_mod, h]

theorem iterated_cos (n : ℕ) : iteratedDeriv n Real.cos =
    fun u => (reSign n : ℝ)*Real.cos u-(imSign n : ℝ)*Real.sin u := by
  induction n with
  | zero => simp [reSign, imSign]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext u
    have hd := ((Real.hasDerivAt_cos u).const_mul (reSign n : ℝ)).sub
      ((Real.hasDerivAt_sin u).const_mul (imSign n : ℝ))
    have hd' : deriv (fun y => (reSign n : ℝ)*Real.cos y-(imSign n : ℝ)*Real.sin y) u =
        (reSign n : ℝ)*(-Real.sin u)-(imSign n : ℝ)*Real.cos u := hd.deriv
    rw [hd']
    simp only [reSign_succ, imSign_succ, Rat.cast_neg]
    ring

theorem iterated_sin (n : ℕ) : iteratedDeriv n Real.sin =
    fun u => (imSign n : ℝ)*Real.cos u+(reSign n : ℝ)*Real.sin u := by
  induction n with
  | zero => simp [reSign, imSign]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext u
    have hd := ((Real.hasDerivAt_cos u).const_mul (imSign n : ℝ)).add
      ((Real.hasDerivAt_sin u).const_mul (reSign n : ℝ))
    have hd' : deriv (fun y => (imSign n : ℝ)*Real.cos y+(reSign n : ℝ)*Real.sin y) u =
        (imSign n : ℝ)*(-Real.sin u)+(reSign n : ℝ)*Real.cos u := hd.deriv
    rw [hd']
    simp only [reSign_succ, imSign_succ, Rat.cast_neg]
    ring

theorem coefficient_cos (a u : ℝ) (n : ℕ) :
    coefficient (fun v => Real.cos (a*v)) n u =
      (a^n/(n.factorial : ℝ))*
        ((reSign n : ℝ)*Real.cos (a*u)-(imSign n : ℝ)*Real.sin (a*u)) := by
  unfold coefficient
  rw [iteratedDeriv_comp_const_mul (by fun_prop : ContDiff ℝ n Real.cos) a, iterated_cos]
  ring

theorem coefficient_sin (a u : ℝ) (n : ℕ) :
    coefficient (fun v => Real.sin (a*v)) n u =
      (a^n/(n.factorial : ℝ))*
        ((imSign n : ℝ)*Real.cos (a*u)+(reSign n : ℝ)*Real.sin (a*u)) := by
  unfold coefficient
  rw [iteratedDeriv_comp_const_mul (by fun_prop : ContDiff ℝ n Real.sin) a, iterated_sin]
  ring

def cosJet (A : Box) (J : Box × Box) (p n : ℕ) : Box :=
  mul (divNat (pow A p n) n.factorial p)
    (sub (mul (rational (reSign n) p) J.1 p)
      (mul (rational (imSign n) p) J.2 p) p) p

def sinJet (A : Box) (J : Box × Box) (p n : ℕ) : Box :=
  mul (divNat (pow A p n) n.factorial p)
    (add (mul (rational (imSign n) p) J.1 p)
      (mul (rational (reSign n) p) J.2 p) p) p

theorem cosJet_mem {a u : ℝ} {A : Box} {J : Box × Box} (ha : a ∈ A)
    (hc : Real.cos (a*u) ∈ J.1) (hs : Real.sin (a*u) ∈ J.2) (p n : ℕ) :
    coefficient (fun v => Real.cos (a*v)) n u ∈ cosJet A J p n := by
  rw [coefficient_cos]
  exact mul_mem (divNat_mem (pow_mem ha p n) n.factorial p)
    (sub_mem (mul_mem (rational_mem (reSign n) p) hc p)
      (mul_mem (rational_mem (imSign n) p) hs p) p) p

theorem sinJet_mem {a u : ℝ} {A : Box} {J : Box × Box} (ha : a ∈ A)
    (hc : Real.cos (a*u) ∈ J.1) (hs : Real.sin (a*u) ∈ J.2) (p n : ℕ) :
    coefficient (fun v => Real.sin (a*v)) n u ∈ sinJet A J p n := by
  rw [coefficient_sin]
  exact mul_mem (divNat_mem (pow_mem ha p n) n.factorial p)
    (add_mem (mul_mem (rational_mem (imSign n) p) hc p)
      (mul_mem (rational_mem (reSign n) p) hs p) p) p

end OperatorDerivativeRewrite.Foundation.RiemannQuarticTrigJets
