import Foundation.GaussianTimeSpaceHermite

/-! Exact geometry of the second-chaos embedding. On equal-variance positively
correlated directions it preserves mean-square roughness up to constants;
globally it identifies antipodes. -/
noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false

namespace OperatorDerivativeRewrite.Foundation.GaussianQuadraticGeometry
open InfiniteGaussian GaussianTimeSpaceHermite

theorem wick_two_norm_sq (h : CoefficientSpace) :
    ‖(wick h 2 : GaussianL2)‖^2 = 2*(‖h‖^2)^2 := by
  rw [← real_inner_self_eq_norm_sq, wick_inner]
  norm_num [real_inner_self_eq_norm_sq]

theorem wick_two_distance_sq (h k : CoefficientSpace) :
    ‖(wick h 2 : GaussianL2)-(wick k 2 : GaussianL2)‖^2 =
      2*((‖h‖^2)^2+(‖k‖^2)^2-2*(inner ℝ h k)^2) := by
  rw [norm_sub_sq_real, wick_two_norm_sq, wick_two_norm_sq, wick_inner]
  norm_num <;> ring

/-- This is an exact metric identity at fixed variance, including negative
correlations. The vanishing antipodal factor explains the global folding. -/
theorem fixed_variance_distance_sq (h k : CoefficientSpace) (v : ℝ)
    (hh : ‖h‖^2=v) (hk : ‖k‖^2=v) :
    ‖(wick h 2 : GaussianL2)-(wick k 2 : GaussianL2)‖^2 =
      2*(v+inner ℝ h k)*‖h-k‖^2 := by
  rw [wick_two_distance_sq, hh, hk, norm_sub_sq_real, hh, hk]
  ring

theorem positive_correlation_distance_bounds (h k : CoefficientSpace) (v : ℝ)
    (hh : ‖h‖^2=v) (hk : ‖k‖^2=v) (hc : 0 ≤ inner ℝ h k) :
    2*v*‖h-k‖^2 ≤ ‖(wick h 2 : GaussianL2)-(wick k 2 : GaussianL2)‖^2 ∧
      ‖(wick h 2 : GaussianL2)-(wick k 2 : GaussianL2)‖^2 ≤ 4*v*‖h-k‖^2 := by
  have hn : ‖h‖=‖k‖ := by nlinarith [norm_nonneg h, norm_nonneg k]
  have hi := real_inner_le_norm h k
  rw [← hn, ← pow_two, hh] at hi
  rw [fixed_variance_distance_sq h k v hh hk]
  constructor
  · nlinarith [mul_nonneg hc (sq_nonneg ‖h-k‖)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hi) (sq_nonneg ‖h-k‖)]

/-- The quadratic chaos embedding is globally noninjective: h and -h are
the same second-chaos class, despite their different first-chaos directions. -/
theorem wick_two_antipodal (h : CoefficientSpace) :
    (wick h 2 : GaussianL2) = (wick (-h) 2 : GaussianL2) := by
  have hz : ‖(wick h 2 : GaussianL2)-(wick (-h) 2 : GaussianL2)‖^2 = 0 := by
    rw [wick_two_distance_sq]
    simp only [norm_neg, inner_neg_right, real_inner_self_eq_norm_sq, neg_sq]
    ring
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  nlinarith [hz]

end OperatorDerivativeRewrite.Foundation.GaussianQuadraticGeometry
