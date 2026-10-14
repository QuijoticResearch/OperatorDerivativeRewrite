import Foundation.GaussianCubicConditionalPrediction
import Foundation.GaussianPoissonChaosTransfer

/-! Exact finite terminal Hermite prediction and its chaos-rank bounds. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianPolynomialPredictionRank
open InfiniteGaussian GaussianConditionalGraph GaussianWickConditionalProjection
open GaussianPoissonChaosTransfer GaussianTimeSpaceHermite

theorem conditional_expansion {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) {N : ℕ} (c : Fin N → ℝ) :
    conditionalProjection h (gaussianExpansion u c)=gaussianExpansion (sourceProjection h u) c := by
  simp only [gaussianExpansion,map_sum,map_smul,conditional_wick_projection]

theorem conditional_expansion_energy {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) {N : ℕ} (c : Fin N → ℝ) :
    ‖conditionalProjection h (gaussianExpansion u c)‖^2=
      ∑ i, (c i)^2*(i.val.factorial : ℝ)*(‖sourceProjection h u‖^2)^i.val := by
  rw [conditional_expansion,← real_inner_self_eq_norm_sq,gaussianExpansion_inner]
  simp only [pow_two]

theorem conditional_expansion_rank_upper {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) (hu : ‖u‖^2=1) {N : ℕ} (c : Fin N → ℝ)
    (m : ℕ) (hrank : ∀ i, i.val<m → c i=0) :
    ‖conditionalProjection h (gaussianExpansion u c)‖^2 ≤
      (‖sourceProjection h u‖^2)^m*‖gaussianExpansion u c‖^2 := by
  have hv : ‖sourceProjection h u‖^2 ≤ 1 := by
    rw [← hu]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      ((sourceSpan h).norm_starProjection_apply_le u)
  have hn := gaussianExpansion_inner u c c
  rw [real_inner_self_eq_norm_sq,hu] at hn
  rw [conditional_expansion_energy,hn]
  simp only [one_pow,mul_one,← pow_two]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hm : i.val<m
  · simp [hrank i hm]
  · have hp := pow_le_pow_of_le_one (sq_nonneg ‖sourceProjection h u‖) hv (Nat.le_of_not_gt hm)
    have hc : 0 ≤ (c i)^2*(i.val.factorial : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hp hc]

theorem conditional_expansion_rank_lower {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) {N : ℕ} (c : Fin N → ℝ) (m : Fin N) :
    (c m)^2*(m.val.factorial : ℝ)*(‖sourceProjection h u‖^2)^m.val ≤
      ‖conditionalProjection h (gaussianExpansion u c)‖^2 := by
  rw [conditional_expansion_energy]
  exact Finset.single_le_sum
    (f := fun i : Fin N => (c i)^2*(i.val.factorial : ℝ)*(‖sourceProjection h u‖^2)^i.val)
    (fun i hi => by positivity) (Finset.mem_univ m)

end OperatorDerivativeRewrite.Foundation.GaussianPolynomialPredictionRank
