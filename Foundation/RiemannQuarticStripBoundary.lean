import Foundation.RiemannQuarticNaturalContour
/-! The raw theta-moment series fails at and beyond Re(v)=0.
This is a representation-domain obstruction, not an obstruction to a separately
proved analytic continuation or to eventual quartic real-rooting. -/
noncomputable section
open Set Metric Complex Filter
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticStripBoundary
open RiemannQuarticSaddleTheta RiemannQuarticKernel

theorem not_summable_moment_nonpos (k : ℕ) (v : ℂ) (hv : v.re ≤ 0) :
    ¬ Summable (complexThetaTerm k v) := by
  have hlow (n : ℕ) : 1 ≤ ‖complexThetaTerm k v n‖ := by
    rw [norm_complexThetaTerm]
    unfold thetaTerm
    have hb : 1 ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hp : 1 ≤ (((n+1 : ℕ) : ℝ))^k := one_le_pow₀ hb
    have hc : -Real.pi*(((n+1 : ℕ) : ℝ))^2 ≤ 0 := by nlinarith [sq_nonneg (((n+1 : ℕ) : ℝ)),Real.pi_pos]
    have he : 1 ≤ Real.exp (-Real.pi*(((n+1 : ℕ) : ℝ))^2*v.re) :=
      Real.one_le_exp (mul_nonneg_of_nonpos_of_nonpos hc hv)
    simpa only [Nat.cast_add,Nat.cast_one,one_mul] using (mul_le_mul hp he (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ (((n+1 : ℕ) : ℝ))^k))
  intro hs
  have ht := hs.tendsto_atTop_zero.norm
  simp only [norm_zero] at ht
  obtain ⟨n,hn⟩ := (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2))).exists
  linarith [hlow n]

theorem boundary_exp_real_zero (x : ℝ) :
    (Complex.exp (4*((x : ℂ)+((Real.pi/8 : ℝ) : ℂ)*Complex.I))).re=0 := by
  have hi : (4*((x : ℂ)+((Real.pi/8 : ℝ) : ℂ)*Complex.I)).im=Real.pi/2 := by
    simp [Complex.mul_im,Complex.mul_re]
    ring
  rw [Complex.exp_re,hi,Real.cos_pi_div_two,mul_zero]

theorem boundary_moment_not_summable (k : ℕ) (x : ℝ) :
    ¬ Summable (complexThetaTerm k (Complex.exp (4*((x : ℂ)+((Real.pi/8 : ℝ) : ℂ)*Complex.I)))) :=
  not_summable_moment_nonpos k _ (boundary_exp_real_zero x).le

end OperatorDerivativeRewrite.Foundation.RiemannQuarticStripBoundary
