import Foundation.IBMFourthPeano

/-! Compact third-order Peano control, used for actual symmetric quadrature
of C3 one-forms along IBM. This is a deterministic Taylor theorem. -/
noncomputable section
open Set
namespace OperatorDerivativeRewrite.Foundation.IBMThirdPeano

def polynomial (g : ℝ → ℝ) (x y : ℝ) : ℝ :=
  g x + iteratedDeriv 1 g x * (y - x) +
    (1/2 : ℝ) * iteratedDeriv 2 g x * (y - x)^2 +
    (1/6 : ℝ) * iteratedDeriv 3 g x * (y - x)^3

def remainder (g : ℝ → ℝ) (x y : ℝ) : ℝ := g y - polynomial g x y

theorem taylor_two_explicit (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g)
    (x y : ℝ) (hxy : x ≠ y) :
    taylorWithinEval g 2 (uIcc x y) x y =
      g x + iteratedDeriv 1 g x * (y - x) +
        (1/2 : ℝ) * iteratedDeriv 2 g x * (y - x)^2 := by
  have hder (n : ℕ) (hn : n ≤ 3) :
      iteratedDerivWithin n g (uIcc x y) x = iteratedDeriv n g x :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hxy)
      (hg.of_le (by exact_mod_cast hn)).contDiffAt left_mem_uIcc
  rw [taylorWithinEval_succ g 1, taylorWithinEval_succ g 0, taylor_within_zero_eval,
    hder 1 (by decide), hder 2 (by decide)]
  norm_num [smul_eq_mul]
  ring

theorem remainder_lagrange (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g) (x y : ℝ) :
    ∃ z ∈ uIcc x y, remainder g x y =
      (iteratedDeriv 3 g z - iteratedDeriv 3 g x) * (y - x)^3 / 6 := by
  by_cases hxy : x = y
  · subst y
    exact ⟨x, by simp, by simp [remainder, polynomial]⟩
  obtain ⟨z, hz, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 2) hxy hg.contDiffOn
  refine ⟨z, ⟨hz.1.le, hz.2.le⟩, ?_⟩
  rw [taylor_two_explicit g hg x y hxy] at he
  norm_num [smul_eq_mul] at he
  unfold remainder polynomial
  simp only [iteratedDeriv_one]
  linarith

theorem compact_remainder_bound (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g) (R ε : ℝ)
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ x y : ℝ, |x| ≤ R → |y| ≤ R → |y - x| < δ →
      |remainder g x y| ≤ ε * |y - x|^3 := by
  have h3 := ContDiff.continuous_iteratedDeriv 3 hg (by norm_num)
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc : IsCompact (Icc (-R) R)).uniformContinuousOn_of_continuous
      h3.continuousOn) (6 * ε) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro x y hx hy hxy
  obtain ⟨z, hz, he⟩ := remainder_lagrange g hg x y
  have hxR : x ∈ Icc (-R) R := abs_le.mp hx
  have hyR : y ∈ Icc (-R) R := abs_le.mp hy
  have hgeom : z ∈ Icc (-R) R ∧ |z - x| ≤ |y - x| := by
    rcases le_total x y with h | h
    · rw [uIcc_of_le h] at hz
      refine ⟨⟨hxR.1.trans hz.1, hz.2.trans hyR.2⟩, ?_⟩
      rw [abs_of_nonneg (sub_nonneg.mpr hz.1), abs_of_nonneg (sub_nonneg.mpr h)]
      linarith [hz.2]
    · rw [uIcc_of_ge h] at hz
      refine ⟨⟨hyR.1.trans hz.1, hz.2.trans hxR.2⟩, ?_⟩
      rw [abs_of_nonpos (sub_nonpos.mpr hz.2), abs_of_nonpos (sub_nonpos.mpr h)]
      linarith [hz.1]
  have hosc : |iteratedDeriv 3 g z - iteratedDeriv 3 g x| < 6 * ε := by
    simpa only [Real.dist_eq] using hu z hgeom.1 x hxR
      (by simpa only [Real.dist_eq] using hgeom.2.trans_lt hxy)
  rw [he, abs_div, abs_mul, abs_pow]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 6)).mpr
  have hm := mul_le_mul_of_nonneg_right hosc.le (pow_nonneg (abs_nonneg (y - x)) 3)
  nlinarith

end OperatorDerivativeRewrite.Foundation.IBMThirdPeano
