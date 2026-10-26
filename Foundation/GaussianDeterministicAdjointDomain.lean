import Foundation.GaussianFirstChaosRecovery
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The bounded adjoint of deterministic Gaussian integration recovers first
chaos. It differs from the closed random-field derivative on quadratic chaos;
testing only deterministic fields does not determine a random gradient. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.GaussianDeterministicAdjointDomain
open OperatorDerivativeRewrite.Foundation
open InfiniteGaussian GaussianTimeSpaceHermite IBMCubicFirstChaos GaussianTimeFieldNorm

def deterministicDerivative : GaussianL2 →L[ℝ] CoefficientSpace :=
  firstChaosEmbedding.toContinuousLinearMap.adjoint

theorem deterministic_first (h : CoefficientSpace) :
    deterministicDerivative (firstChaosEmbedding h) = h := by
  apply ext_inner_left ℝ
  intro k
  change inner ℝ k (firstChaosEmbedding.toContinuousLinearMap.adjoint
    (firstChaosEmbedding h)) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact firstChaosEmbedding.inner_map_map k h

theorem deterministic_wick_other (h : CoefficientSpace) (n : ℕ) (hn : n ≠ 1) :
    deterministicDerivative (wick h n : GaussianL2) = 0 := by
  apply ext_inner_left ℝ
  intro k
  change inner ℝ k (firstChaosEmbedding.toContinuousLinearMap.adjoint
    (wick h n : GaussianL2)) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (firstChaosEmbedding k) (wick h n : GaussianL2) = _
  rw [← wick_one_eq_embedding, wick_inner]
  simp [Ne.symm hn]

theorem quadratic_derivative (h : CoefficientSpace) :
    polynomialDerivative (wick h 2) = (2 : ℝ) • scalarTensor h (firstChaosEmbedding h) := by
  have hd := core_derivative h (‖h‖^2) 1
  have he : (core h (‖h‖^2) 1 : GaussianL2) = firstChaosEmbedding h := wick_one_eq_embedding h
  rw [he] at hd
  norm_num at hd
  exact hd

theorem quadratic_derivative_norm_sq (h : CoefficientSpace) :
    ‖polynomialDerivative (wick h 2)‖^2 = 4 * ‖h‖^4 := by
  have hs : ‖scalarTensor h (firstChaosEmbedding h)‖^2 = ‖h‖^4 := by
    rw [← real_inner_self_eq_norm_sq, scalarTensor_pair_inner,
      firstChaosEmbedding.inner_map_map, real_inner_self_eq_norm_sq]
    ring
  rw [quadratic_derivative, norm_smul, mul_pow, hs]
  norm_num

theorem quadratic_gradient_nonzero {h : CoefficientSpace} (hh : h ≠ 0) :
    polynomialDerivative (wick h 2) ≠ 0 := by
  intro hz
  have he := quadratic_derivative_norm_sq h
  rw [hz, norm_zero, zero_pow (by omega)] at he
  have hp : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have hp4 : 0 < ‖h‖^4 := pow_pos hp 4
  linarith

theorem deterministic_lift_not_closed_gradient {h : CoefficientSpace} (hh : h ≠ 0) :
    ((wick h 2 : GaussianL2), scalarTensor (deterministicDerivative (wick h 2)) gaussianOne)
      ∉ closedCylindricalDerivative.graph := by
  intro hg
  have hz := deterministic_wick_other h 2 (by omega)
  have ht : scalarTensor 0 gaussianOne = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [scalarTensor_pair_inner, inner_zero_left, mul_zero]
  rw [hz, ht] at hg
  have he := closedCylindricalDerivative.mem_graph_snd_inj
    (closedCylindricalDerivative_core_graph (wick h 2)) hg rfl
  exact quadratic_gradient_nonzero hh he

theorem quadratic_gradient_constant_pairing (h k : CoefficientSpace) :
    inner ℝ (polynomialDerivative (wick h 2)) (scalarTensor k gaussianOne) = 0 := by
  have hc : inner ℝ (firstChaosEmbedding h) gaussianOne = 0 := by
    rw [← wick_one_eq_embedding, real_inner_comm]
    exact wick_centered h 0
  rw [quadratic_derivative, real_inner_smul_left, scalarTensor_pair_inner, hc]
  ring

theorem quadratic_duality_not_unique {h : CoefficientSpace} (hh : h ≠ 0) :
    ∃ u v : GaussianVectorL2, u ≠ v ∧
      (∀ k : CoefficientSpace, inner ℝ (wick h 2 : GaussianL2) (firstChaosEmbedding k) =
        inner ℝ u (scalarTensor k gaussianOne)) ∧
      (∀ k : CoefficientSpace, inner ℝ (wick h 2 : GaussianL2) (firstChaosEmbedding k) =
        inner ℝ v (scalarTensor k gaussianOne)) := by
  refine ⟨polynomialDerivative (wick h 2), 0, quadratic_gradient_nonzero hh, ?_, ?_⟩
  · intro k
    rw [quadratic_gradient_constant_pairing, ← wick_one_eq_embedding, wick_inner]
    norm_num
  · intro k
    rw [inner_zero_left, ← wick_one_eq_embedding, wick_inner]
    norm_num

end OperatorDerivativeRewrite.Foundation.GaussianDeterministicAdjointDomain
