import Foundation.IBMFourthTaylor

/-! C4 control of the existing fourth Taylor remainder by a compact modulus
of continuity of the fourth derivative. No fifth derivative bound is used. -/
noncomputable section
open Set
namespace OperatorDerivativeRewrite.Foundation.IBMFourthPeano

def lower (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  iteratedDeriv 1 f x * (y - x) + (1/2 : ℝ) * iteratedDeriv 2 f x * (y - x)^2 +
    (1/6 : ℝ) * iteratedDeriv 3 f x * (y - x)^3

theorem taylor_four_explicit (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f)
    (x y : ℝ) (hxy : x ≠ y) :
    taylorWithinEval f 4 (uIcc x y) x y =
      f x + lower f x y + (1/24 : ℝ)*iteratedDeriv 4 f x*(y - x)^4 := by
  have hder (n : ℕ) (hn : n ≤ 4) :
      iteratedDerivWithin n f (uIcc x y) x = iteratedDeriv n f x :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hxy)
      (hf.of_le (by exact_mod_cast hn)).contDiffAt left_mem_uIcc
  rw [taylorWithinEval_succ f 3, taylorWithinEval_succ f 2,
    taylorWithinEval_succ f 1, taylorWithinEval_succ f 0, taylor_within_zero_eval,
    hder 1 (by decide), hder 2 (by decide), hder 3 (by decide), hder 4 (by decide)]
  norm_num [smul_eq_mul, lower]
  ring

theorem increment_identity (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (x y : ℝ) :
    f y - f x = lower f x y + (1/24 : ℝ)*iteratedDeriv 4 f x*(y - x)^4 +
      IBMFourthTaylor.remainder f x y := by
  by_cases hxy : x = y
  · subst y; simp [lower, IBMFourthTaylor.remainder]
  rw [IBMFourthTaylor.remainder, taylor_four_explicit f hf x y hxy]
  ring

/-- The same genuine remainder is a fourth-derivative oscillation times the
fourth power of the increment. The intermediate point stays in the segment. -/
theorem remainder_lagrange (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (x y : ℝ) :
    ∃ z ∈ uIcc x y, IBMFourthTaylor.remainder f x y =
      (iteratedDeriv 4 f z-iteratedDeriv 4 f x)*(y - x)^4/24 := by
  by_cases hxy : x = y
  · subst y
    exact ⟨x, by simp, by simp [IBMFourthTaylor.remainder]⟩
  obtain ⟨z, hz, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 3) hxy hf.contDiffOn
  refine ⟨z, ⟨hz.1.le, hz.2.le⟩, ?_⟩
  have hd : iteratedDerivWithin 4 f (uIcc x y) x = iteratedDeriv 4 f x :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hxy)
      hf.contDiffAt left_mem_uIcc
  rw [IBMFourthTaylor.remainder, taylorWithinEval_succ f 3, hd]
  norm_num [smul_eq_mul] at he ⊢
  linarith

theorem remainder_continuous (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) :
    Continuous (fun p : ℝ × ℝ => IBMFourthTaylor.remainder f p.1 p.2) := by
  have he : (fun p : ℝ × ℝ => IBMFourthTaylor.remainder f p.1 p.2) =
      fun p => f p.2-f p.1-lower f p.1 p.2 -
        (1/24 : ℝ)*iteratedDeriv 4 f p.1*(p.2-p.1)^4 := by
    funext p
    have h := increment_identity f hf p.1 p.2
    linarith
  rw [he]
  have h1 := ContDiff.continuous_iteratedDeriv 1 hf (by norm_num)
  have h2 := ContDiff.continuous_iteratedDeriv 2 hf (by norm_num)
  have h3 := ContDiff.continuous_iteratedDeriv 3 hf (by norm_num)
  have h4 := ContDiff.continuous_iteratedDeriv 4 hf (by norm_num)
  have h0 := hf.continuous
  unfold lower
  fun_prop

/-- Uniform Peano control on a compact spatial interval. No fifth derivative,
nor any global bound on a derivative, is supplied. -/
theorem compact_remainder_bound (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (R ε : ℝ)
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ x y : ℝ, |x| ≤ R → |y| ≤ R → |y - x| < δ →
      |IBMFourthTaylor.remainder f x y| ≤ ε*|y - x|^4 := by
  have h4 := ContDiff.continuous_iteratedDeriv 4 hf (by norm_num)
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc : IsCompact (Icc (-R) R)).uniformContinuousOn_of_continuous
      h4.continuousOn) (24*ε) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro x y hx hy hxy
  obtain ⟨z, hz, he⟩ := remainder_lagrange f hf x y
  have hxR : x ∈ Icc (-R) R := abs_le.mp hx
  have hyR : y ∈ Icc (-R) R := abs_le.mp hy
  have hgeom : z ∈ Icc (-R) R ∧ |z-x| ≤ |y - x| := by
    rcases le_total x y with h | h
    · rw [uIcc_of_le h] at hz
      refine ⟨⟨hxR.1.trans hz.1, hz.2.trans hyR.2⟩, ?_⟩
      rw [abs_of_nonneg (sub_nonneg.mpr hz.1), abs_of_nonneg (sub_nonneg.mpr h)]
      linarith [hz.2]
    · rw [uIcc_of_ge h] at hz
      refine ⟨⟨hyR.1.trans hz.1, hz.2.trans hxR.2⟩, ?_⟩
      rw [abs_of_nonpos (sub_nonpos.mpr hz.2), abs_of_nonpos (sub_nonpos.mpr h)]
      linarith [hz.1]
  have hosc : |iteratedDeriv 4 f z-iteratedDeriv 4 f x| < 24*ε := by
    simpa only [Real.dist_eq] using hu z hgeom.1 x hxR
      (by simpa only [Real.dist_eq] using hgeom.2.trans_lt hxy)
  rw [he, abs_div, abs_mul, abs_pow]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 24)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 24)).mpr
  have hm := mul_le_mul_of_nonneg_right hosc.le (pow_nonneg (abs_nonneg (y - x)) 4)
  nlinarith

end OperatorDerivativeRewrite.Foundation.IBMFourthPeano
