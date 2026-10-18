import Foundation.HigherEvenRootInnovation
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Exact polynomial action of actual cyclic probability transitions. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.CyclicPolynomialKernel
open CyclicRootProbabilityNoise
variable (N : ℕ) [NeZero N]

def transition (c : ℂ) (f : ℂ → ℂ) (x : ℂ) : ℂ := ∫ k, f (x+noise N c k) ∂probability N

theorem monomial_formula (c x : ℂ) (n : ℕ) :
    transition N c (fun y => y^n) x =
      ∑ j ∈ Finset.range (n+1), ((n.choose j : ℂ)*x^(n-j))*
        (if (j : ZMod N) = 0 then c^j else 0) := by
  have hp (k : ZMod N) : (x+noise N c k)^n =
      ∑ j ∈ Finset.range (n+1), ((n.choose j : ℂ)*x^(n-j))*(noise N c k)^j := by
    rw [add_comm x (noise N c k),add_pow]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold transition
  simp_rw [hp]
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul,holomorphic_moment]

theorem lower_monomial (c x : ℂ) (n : ℕ) (hn : n < N) :
    transition N c (fun y => y^n) x = x^n := by
  rw [monomial_formula,Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    have hpos : 0 < j := Nat.pos_of_ne_zero hj0
    have hjN : j < N := lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hn
    have hcast : (j : ZMod N) ≠ 0 := fun h =>
      Nat.not_le_of_gt hjN (Nat.le_of_dvd hpos ((ZMod.natCast_eq_zero_iff j N).mp h))
    simp [hcast]
  · simp

theorem leading_monomial (c x : ℂ) : transition N c (fun y => y^N) x = x^N+c^N := by
  rw [monomial_formula,Finset.sum_range_succ]
  have hs : (∑ j ∈ Finset.range N, ((N.choose j : ℂ)*x^(N-j))*
      (if (j : ZMod N) = 0 then c^j else 0)) = x^N := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j hj hj0
      have hpos : 0 < j := Nat.pos_of_ne_zero hj0
      have hcast : (j : ZMod N) ≠ 0 := fun h =>
        Nat.not_le_of_gt (Finset.mem_range.mp hj)
          (Nat.le_of_dvd hpos ((ZMod.natCast_eq_zero_iff j N).mp h))
      simp [hcast]
    · simp [NeZero.pos N]
  rw [hs]
  simp

def rate (m : ℕ) (a : ℝ) : ℝ := (Nat.factorial (2*m) : ℝ)/a^(2*m)

theorem rate_pos (m : ℕ) (a : ℝ) (ha : a ≠ 0) : 0 < rate m a := by
  apply div_pos (by exact_mod_cast Nat.factorial_pos (2*m))
  rw [pow_mul]
  exact pow_pos (sq_pos_of_ne_zero ha) m

def generator (m : ℕ) [NeZero m] (a : ℝ) (f : ℂ → ℂ) (x : ℂ) : ℂ :=
  (rate m a : ℂ)*(transition (2*m) ((a : ℂ)*HigherEvenRootInnovation.phase m) f x-f x)

theorem generator_lower (m : ℕ) [NeZero m] (a : ℝ) (n : ℕ) (hn : n < 2*m) (x : ℂ) :
    generator m a (fun y => y^n) x = 0 := by
  rw [generator,lower_monomial _ _ _ n hn,sub_self,mul_zero]

theorem lower_derivative (m : ℕ) [NeZero m] (a : ℝ) (n : ℕ) (hn : n < 2*m) (x : ℂ) :
    generator m a (fun y => y^n) x =
      (-1 : ℂ)^(m+1)*iteratedDeriv (2*m) (fun y : ℂ => y^n) x := by
  rw [generator_lower m a n hn,iteratedDeriv_pow,Nat.descFactorial_eq_zero_iff_lt.mpr hn]
  simp

theorem generator_leading (m : ℕ) [NeZero m] (a : ℝ) (ha : a ≠ 0) (x : ℂ) :
    generator m a (fun y => y^(2*m)) x =
      (Nat.factorial (2*m) : ℂ)*(-1 : ℂ)^(m+1) := by
  rw [generator,leading_monomial,add_sub_cancel_left,mul_pow,HigherEvenRootInnovation.phase_power]
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  simp only [rate,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_pow]
  field_simp

theorem leading_derivative (m : ℕ) [NeZero m] (a : ℝ) (ha : a ≠ 0) (x : ℂ) :
    generator m a (fun y => y^(2*m)) x =
      (-1 : ℂ)^(m+1)*iteratedDeriv (2*m) (fun y : ℂ => y^(2*m)) x := by
  rw [generator_leading m a ha,iteratedDeriv_pow,Nat.descFactorial_self]
  simp [mul_comm]

theorem generator_not_pure_derivative (m : ℕ) [NeZero m] (a : ℝ) (ha : a ≠ 0) :
    generator m a (fun y => y^(4*m)) 0 ≠
      (-1 : ℂ)^(m+1)*iteratedDeriv (2*m) (fun y : ℂ => y^(4*m)) 0 := by
  have hm := NeZero.pos m
  have hn : 4*m ≠ 0 := by omega
  have hc : ((4*m : ℕ) : ZMod (2*m)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact ⟨2,by ring⟩
  have hg : generator m a (fun y => y^(4*m)) 0 ≠ 0 := by
    unfold generator transition
    simp only [zero_add,zero_pow hn,sub_zero,holomorphic_moment,hc,ite_true]
    apply mul_ne_zero
    · exact Complex.ofReal_ne_zero.mpr (rate_pos m a ha).ne'
    · apply pow_ne_zero
      apply mul_ne_zero (Complex.ofReal_ne_zero.mpr ha)
      exact Complex.exp_ne_zero _
  rw [iteratedDeriv_fun_pow_zero]
  have hne : 2*m ≠ 4*m := by omega
  simpa only [hne,ite_false,Nat.cast_zero,mul_zero] using hg

end OperatorDerivativeRewrite.Foundation.CyclicPolynomialKernel
