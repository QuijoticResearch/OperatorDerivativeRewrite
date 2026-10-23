import Foundation.IBMSimpsonPeano

/-! Global fifth-order Simpson error for C5 primitives. The explicit global
bound is used only for L2 upgrades; the earlier C4 probability theorem remains. -/
noncomputable section
open Set
namespace OperatorDerivativeRewrite.Foundation.IBMSimpsonFifthError

theorem taylor_three_explicit (g : ℝ → ℝ) (hg : ContDiff ℝ 4 g)
    (x y : ℝ) (hxy : x ≠ y) :
    taylorWithinEval g 3 (uIcc x y) x y = IBMThirdPeano.polynomial g x y := by
  have hder : iteratedDerivWithin 3 g (uIcc x y) x = iteratedDeriv 3 g x :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hxy)
      (hg.of_le (by norm_num)).contDiffAt left_mem_uIcc
  rw [taylorWithinEval_succ g 2, IBMThirdPeano.taylor_two_explicit g
    (hg.of_le (by norm_num)) x y hxy, hder]
  norm_num [IBMThirdPeano.polynomial, smul_eq_mul]
  ring

theorem third_remainder_bound (g : ℝ → ℝ) (hg : ContDiff ℝ 4 g) (M : ℝ)
    (hM : ∀ z, ‖iteratedDeriv 4 g z‖ ≤ M) (x y : ℝ) :
    |IBMThirdPeano.remainder g x y| ≤ (M/24)*|y-x|^4 := by
  by_cases hxy : x = y
  · subst y; simp [IBMThirdPeano.remainder, IBMThirdPeano.polynomial]
  obtain ⟨z,hz,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 3) hxy hg.contDiffOn
  rw [taylor_three_explicit g hg x y hxy] at he
  change IBMThirdPeano.remainder g x y = _ at he
  rw [he]
  norm_num [smul_eq_mul, abs_div, abs_mul, abs_pow]
  have hb : |iteratedDeriv 4 g z| ≤ M := by simpa only [Real.norm_eq_abs] using hM z
  calc
    _ ≤ M*|y-x|^4/24 := by gcongr
    _ = (M/24)*|y-x|^4 := by ring

/-- A deliberately nonoptimal but uniform constant suffices for the actual
stochastic L2 bound. No sixth derivative is used. -/
theorem error_bound (f : ℝ → ℝ) (hf : ContDiff ℝ 5 f) (M : ℝ)
    (hM : ∀ z, ‖iteratedDeriv 5 f z‖ ≤ M) (x y : ℝ) :
    |IBMSimpsonPeano.simpson (deriv f) x y-(f y-f x)| ≤ M*|y-x|^5 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hg : ContDiff ℝ 4 (deriv f) := hf.deriv'
  have hD (z : ℝ) : ‖iteratedDeriv 4 (deriv f) z‖ ≤ M := by
    simpa only [← iteratedDeriv_succ'] using hM z
  have he := third_remainder_bound (deriv f) hg M hD x y
  have hm := third_remainder_bound (deriv f) hg M hD x ((x+y)/2)
  have hmid : |(x+y)/2-x| ≤ |y-x| := by
    have hi : (x+y)/2-x = (y-x)/2 := by ring
    rw [hi, abs_div]
    norm_num
  have hm' : |IBMThirdPeano.remainder (deriv f) x ((x+y)/2)| ≤ (M/24)*|y-x|^4 :=
    hm.trans (by gcongr)
  have h4 := IBMFourthTaylor.remainder_bound f hf M hM x y
  simp only [Real.norm_eq_abs] at h4
  rw [IBMSimpsonPeano.error_identity f (hf.of_le (by norm_num))]
  calc
    _ ≤ |(y-x)/6*(4*IBMThirdPeano.remainder (deriv f) x ((x+y)/2)+
        IBMThirdPeano.remainder (deriv f) x y)| + |IBMFourthTaylor.remainder f x y| := abs_sub _ _
    _ ≤ |y-x|/6*(4*|IBMThirdPeano.remainder (deriv f) x ((x+y)/2)|+
        |IBMThirdPeano.remainder (deriv f) x y|)+|IBMFourthTaylor.remainder f x y| := by
      rw [abs_mul, abs_div]
      norm_num
      gcongr
      simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] using
        abs_add_le (4*IBMThirdPeano.remainder (deriv f) x ((x+y)/2))
          (IBMThirdPeano.remainder (deriv f) x y)
    _ ≤ |y-x|/6*(4*((M/24)*|y-x|^4)+(M/24)*|y-x|^4)+(M/120)*|y-x|^5 := by gcongr
    _ ≤ M*|y-x|^5 := by
      nlinarith [mul_nonneg hM0 (pow_nonneg (abs_nonneg (y-x)) 5)]

end OperatorDerivativeRewrite.Foundation.IBMSimpsonFifthError
