import Foundation.HigherEvenRenewalTransform

/-! Quantitative holomorphic Taylor cancellation for actual cyclic innovations. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.CyclicExponentialTaylor
open HigherEvenRootInnovation

def leadingTerm (m : ℕ) (a : ℝ) (w : ℂ) : ℂ :=
  ((w*(a : ℂ))^(2*m)*(-1 : ℂ)^(m+1))/(Nat.factorial (2*m) : ℂ)

theorem expected_taylor (m : ℕ) [NeZero m] (a : ℝ) (w : ℂ) :
    (∫ k, (∑ j ∈ Finset.range (2*m+1), (w*innovation m a k)^j/(Nat.factorial j : ℂ))
      ∂CyclicRootProbabilityNoise.probability (2*m)) = 1+leadingTerm m a w := by
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_div,mul_pow,integral_const_mul]
  rw [Finset.sum_range_succ,leading_moment]
  have hs : (∑ j ∈ Finset.range (2*m),
      (w^j*(∫ k, innovation m a k^j ∂CyclicRootProbabilityNoise.probability (2*m)))/
        (Nat.factorial j : ℂ)) = 1 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j hj hj0
      rw [lower_moment m a j (Nat.pos_of_ne_zero hj0) (Finset.mem_range.mp hj)]
      simp
    · simp [NeZero.pos (2*m)]
  rw [hs]
  unfold leadingTerm
  rw [mul_pow]
  ring

theorem remainder_bound (m : ℕ) [NeZero m] (a : ℝ) (w : ℂ) :
    ‖HigherEvenRenewalTransform.markTransform m a w-1-leadingTerm m a w‖ ≤
      (‖w‖*|a|)^(2*m+1)*Real.exp (‖w‖*|a|) := by
  have he : HigherEvenRenewalTransform.markTransform m a w-1-leadingTerm m a w =
      ∫ k, (Complex.exp (w*innovation m a k)-
        ∑ j ∈ Finset.range (2*m+1), (w*innovation m a k)^j/(Nat.factorial j : ℂ))
          ∂CyclicRootProbabilityNoise.probability (2*m) := by
    rw [integral_sub Integrable.of_finite Integrable.of_finite,expected_taylor]
    change HigherEvenRenewalTransform.markTransform m a w-1-leadingTerm m a w =
      HigherEvenRenewalTransform.markTransform m a w-(1+leadingTerm m a w)
    ring
  rw [he]
  calc
    _ ≤ ∫ k, ‖Complex.exp (w*innovation m a k)-
        ∑ j ∈ Finset.range (2*m+1), (w*innovation m a k)^j/(Nat.factorial j : ℂ)‖
          ∂CyclicRootProbabilityNoise.probability (2*m) := norm_integral_le_integral_norm _
    _ ≤ ∫ _k : ZMod (2*m), (‖w‖*|a|)^(2*m+1)*Real.exp (‖w‖*|a|)
          ∂CyclicRootProbabilityNoise.probability (2*m) := by
      apply integral_mono Integrable.of_finite (integrable_const _)
      intro k
      simpa only [norm_mul,HigherEvenRenewalProcess.innovation_norm] using
        Complex.norm_exp_sub_sum_le_norm_mul_exp (w*innovation m a k) (2*m+1)
    _ = _ := by simp

theorem rate_leading (m : ℕ) [NeZero m] (a : ℝ) (ha : a ≠ 0) (w : ℂ) :
    (CyclicPolynomialKernel.rate m a : ℂ)*leadingTerm m a w = (-1 : ℂ)^(m+1)*w^(2*m) := by
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hF : (Nat.factorial (2*m) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  simp only [leadingTerm,CyclicPolynomialKernel.rate,Complex.ofReal_div,
    Complex.ofReal_natCast,Complex.ofReal_pow,mul_pow]
  field_simp

theorem normalized_error_bound (m : ℕ) [NeZero m] (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (w : ℂ) :
    ‖HigherEvenRenewalTransform.normalizedSymbol m a w-(-1 : ℂ)^(m+1)*w^(2*m)‖ ≤
      ((Nat.factorial (2*m) : ℝ)*‖w‖^(2*m+1)*Real.exp ‖w‖)*a := by
  have he : HigherEvenRenewalTransform.normalizedSymbol m a w-(-1 : ℂ)^(m+1)*w^(2*m) =
      (CyclicPolynomialKernel.rate m a : ℂ)*
        (HigherEvenRenewalTransform.markTransform m a w-1-leadingTerm m a w) := by
    rw [mul_sub,rate_leading m a ha.ne']
    rfl
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (CyclicPolynomialKernel.rate_pos m a ha.ne')]
  have ht := mul_le_mul_of_nonneg_left (remainder_bound m a w)
    (CyclicPolynomialKernel.rate_pos m a ha.ne').le
  rw [abs_of_pos ha] at ht
  apply ht.trans
  calc
    _ = ((Nat.factorial (2*m) : ℝ)*‖w‖^(2*m+1)*a)*Real.exp (‖w‖*a) := by
      simp only [CyclicPolynomialKernel.rate,mul_pow,pow_succ]
      field_simp
    _ ≤ ((Nat.factorial (2*m) : ℝ)*‖w‖^(2*m+1)*a)*Real.exp ‖w‖ := by
      apply mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_of_le_one_right (norm_nonneg w) ha1))
      positivity
    _ = _ := by ring

theorem generator_exponential (m : ℕ) [NeZero m] (a : ℝ) (w x : ℂ) :
    CyclicPolynomialKernel.generator m a (fun y => Complex.exp (w*y)) x =
      HigherEvenRenewalTransform.normalizedSymbol m a w*Complex.exp (w*x) := by
  change (CyclicPolynomialKernel.rate m a : ℂ)*
      ((∫ k, Complex.exp (w*(x+innovation m a k))
        ∂CyclicRootProbabilityNoise.probability (2*m))-Complex.exp (w*x)) =
    (CyclicPolynomialKernel.rate m a : ℂ)*
      ((∫ k, Complex.exp (w*innovation m a k)
        ∂CyclicRootProbabilityNoise.probability (2*m))-1)*Complex.exp (w*x)
  simp_rw [mul_add,Complex.exp_add]
  rw [integral_const_mul]
  ring

end OperatorDerivativeRewrite.Foundation.CyclicExponentialTaylor
