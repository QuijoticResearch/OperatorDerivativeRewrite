import Foundation.PoissonGraphApprox

/-! Basis-vector tests for the adjoint domains of one-site Poisson operators. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.PoissonAdjoints
open PoissonDifferenceCore PoissonDifferenceOperators PoissonMaximalOperators
open PoissonTruncationConvergence

theorem difference_single_zero :
    finsuppDifference (Finsupp.single 0 (1 : ℝ)) =
      -Finsupp.single 0 1 := by
  ext n
  simp only [finsuppDifference_apply, Finsupp.neg_apply]
  cases n with
  | zero => simp
  | succ n => simp

theorem difference_single_succ (n : ℕ) :
    finsuppDifference (Finsupp.single (n + 1) (1 : ℝ)) =
      Finsupp.single n 1 - Finsupp.single (n + 1) 1 := by
  ext k
  simp only [finsuppDifference_apply, Finsupp.sub_apply]
  by_cases h : k = n
  · subst k
    simp
  · by_cases h' : k = n + 1
    · subst k
      simp
    · have h'' : k + 1 ≠ n + 1 := by omega
      simp [h, h']

theorem divergence_single (rate : ℝ≥0) (n : ℕ) :
    finsuppDivergence rate (Finsupp.single n (1 : ℝ)) =
      -(rate : ℝ) • Finsupp.single n 1 +
        (n + 1 : ℝ) • Finsupp.single (n + 1) 1 := by
  ext k
  simp only [finsuppDivergence_apply, Finsupp.add_apply, Finsupp.smul_apply]
  cases k with
  | zero =>
    by_cases h : n = 0
    · subst n
      simp [poissonDivergenceExpr, backwardWeighted]
    · simp [poissonDivergenceExpr, backwardWeighted, h]
  | succ k =>
    by_cases h : k = n
    · subst k
      simp [poissonDivergenceExpr, backwardWeighted]
    · by_cases h' : k + 1 = n
      · simp [poissonDivergenceExpr, backwardWeighted, h, h']
      · simp [poissonDivergenceExpr, backwardWeighted, h, h']


theorem difference_single_zero_inner (rate : ℝ≥0) (hr : 0 < rate)
    (u : FieldL2 rate) :
    inner ℝ (fieldFinsupp rate
      (finsuppDifference (Finsupp.single 0 (1 : ℝ)))) u =
      -(rate : ℝ) * poissonWeight rate 0 * u 0 := by
  rw [difference_single_zero]
  change inner ℝ ((fieldEmbedding rate) (-Finsupp.single 0 1)) u = _
  rw [map_neg, inner_neg_left]
  change -inner ℝ (fieldFinsupp rate (Finsupp.single 0 1)) u = _
  rw [field_inner_single rate hr]
  ring

theorem difference_single_succ_inner (rate : ℝ≥0) (hr : 0 < rate)
    (u : FieldL2 rate) (n : ℕ) :
    inner ℝ (fieldFinsupp rate
      (finsuppDifference (Finsupp.single (n + 1) (1 : ℝ)))) u =
      (rate : ℝ) * poissonWeight rate n * u n -
        (rate : ℝ) * poissonWeight rate (n + 1) * u (n + 1) := by
  rw [difference_single_succ]
  change inner ℝ ((fieldEmbedding rate)
    (Finsupp.single n 1 - Finsupp.single (n + 1) 1)) u = _
  rw [map_sub, inner_sub_left]
  change inner ℝ (fieldFinsupp rate (Finsupp.single n 1)) u -
    inner ℝ (fieldFinsupp rate (Finsupp.single (n + 1) 1)) u = _
  rw [field_inner_single rate hr, field_inner_single rate hr]

/-- Adjoint pairs of the difference core obey the Poisson divergence formula. -/
theorem difference_adjoint_le_maximalDivergence (rate : ℝ≥0) (hr : 0 < rate) :
    (coreDifference rate hr).adjoint ≤ maximalDivergence rate hr := by
  apply LinearPMap.le_of_le_graph
  rintro ⟨u, v⟩ hz
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint
    (coreDifference_dense_domain rate hr)] at hz
  have ht (p : ℕ →₀ ℝ) :
      inner ℝ (fieldFinsupp rate (finsuppDifference p)) u -
        inner ℝ (scalarFinsupp rate p) v = 0 :=
    (Submodule.mem_adjoint_iff _ _).mp hz _ _
      (coreDifference_finsupp_graph rate hr p)
  rw [maximalDivergence_graph]
  intro n
  cases n with
  | zero =>
      have h := ht (Finsupp.single 0 1)
      rw [difference_single_zero_inner rate hr u,
        scalar_inner_single] at h
      simp only [maximalDivergenceExpr]
      have hw := poisson_weight_pos rate hr 0
      nlinarith
  | succ n =>
      have h := ht (Finsupp.single (n + 1) 1)
      rw [difference_single_succ_inner rate hr u,
        scalar_inner_single] at h
      simp only [maximalDivergenceExpr]
      have hw := poisson_weight_pos rate hr (n + 1)
      have hrw := poisson_weight_succ rate n
      rw [← hrw] at h
      have he : poissonWeight rate (n + 1) * (v (n + 1)) =
          poissonWeight rate (n + 1) *
            ((n + 1 : ℝ) * u n - (rate : ℝ) * u (n + 1)) := by nlinarith [h]
      exact mul_left_cancel₀ (ne_of_gt hw) he

theorem divergence_single_inner (rate : ℝ≥0) (n : ℕ)
    (f : ScalarL2 rate) :
    inner ℝ (scalarFinsupp rate
      (finsuppDivergence rate (Finsupp.single n (1 : ℝ)))) f =
      -(rate : ℝ) * poissonWeight rate n * f n +
        (n + 1 : ℝ) * poissonWeight rate (n + 1) * f (n + 1) := by
  rw [divergence_single]
  change inner ℝ ((scalarEmbedding rate)
    (-(rate : ℝ) • Finsupp.single n 1 +
      (n + 1 : ℝ) • Finsupp.single (n + 1) 1)) f = _
  rw [map_add, map_smul, map_smul, inner_add_left, real_inner_smul_left,
    real_inner_smul_left]
  change -(rate : ℝ) * inner ℝ (scalarFinsupp rate (Finsupp.single n 1)) f +
    (n + 1 : ℝ) * inner ℝ (scalarFinsupp rate (Finsupp.single (n + 1) 1)) f = _
  rw [scalar_inner_single, scalar_inner_single]
  ring

/-- Every Hilbert-adjoint pair of divergence obeys the actual forward-difference formula. -/
theorem divergence_adjoint_le_maximalDifference (rate : ℝ≥0) (hr : 0 < rate) :
    (coreDivergence rate hr).adjoint ≤ maximalDifference rate hr := by
  apply LinearPMap.le_of_le_graph
  rintro ⟨f, g⟩ hz
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint
    (coreDivergence_dense_domain rate hr)] at hz
  have ht (p : ℕ →₀ ℝ) :
      inner ℝ (scalarFinsupp rate (finsuppDivergence rate p)) f -
        inner ℝ (fieldFinsupp rate p) g = 0 :=
    (Submodule.mem_adjoint_iff _ _).mp hz _ _
      (coreDivergence_finsupp_graph rate hr p)
  rw [maximalDifference_graph]
  intro n
  have h := ht (Finsupp.single n 1)
  rw [divergence_single_inner rate n f, field_inner_single rate hr] at h
  have hrw := poisson_weight_succ rate n
  rw [hrw] at h
  have hw := poisson_weight_pos rate hr n
  have hc : (rate : ℝ) * poissonWeight rate n ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (ne_of_gt hr)) (ne_of_gt hw)
  have he : (rate : ℝ) * poissonWeight rate n * (f (n + 1) - f n) =
      (rate : ℝ) * poissonWeight rate n * g n := by nlinarith [h]
  exact (mul_left_cancel₀ hc he).symm

/-- The adjoint of the difference core is exactly the maximal Poisson divergence. -/
theorem coreDifference_adjoint_eq_maximalDivergence (rate : ℝ≥0) (hr : 0 < rate) :
    (coreDifference rate hr).adjoint = maximalDivergence rate hr := by
  apply le_antisymm
  · exact difference_adjoint_le_maximalDivergence rate hr
  · rw [← closure_coreDivergence_eq_maximal rate hr]
    exact OperatorDerivativeRewrite.Foundation.operatorClosure_le_closed
      (coreDivergence_isClosable rate hr)
      ((coreDifference rate hr).adjoint_isClosed (coreDifference_dense_domain rate hr))
      (coreDivergence_le_difference_adjoint rate hr)

/-- The adjoint of the divergence core is exactly the maximal Poisson difference. -/
theorem coreDivergence_adjoint_eq_maximalDifference (rate : ℝ≥0) (hr : 0 < rate) :
    (coreDivergence rate hr).adjoint = maximalDifference rate hr := by
  apply le_antisymm
  · exact divergence_adjoint_le_maximalDifference rate hr
  · rw [← closure_coreDifference_eq_maximal rate hr]
    exact OperatorDerivativeRewrite.Foundation.operatorClosure_le_closed
      (coreDifference_isClosable rate hr)
      ((coreDivergence rate hr).adjoint_isClosed (coreDivergence_dense_domain rate hr))
      (coreDifference_le_divergence_adjoint rate hr)

/-- The closed maximal Poisson operators are genuine mutual Hilbert adjoints. -/
theorem maximalDifference_adjoint_eq_maximalDivergence (rate : ℝ≥0) (hr : 0 < rate) :
    (maximalDifference rate hr).adjoint = maximalDivergence rate hr := by
  rw [← closure_coreDifference_eq_maximal rate hr,
    OperatorDerivativeRewrite.Foundation.operatorClosure_adjoint_eq
      (coreDifference_isClosable rate hr) (coreDifference_dense_domain rate hr)]
  exact coreDifference_adjoint_eq_maximalDivergence rate hr

theorem maximalDivergence_adjoint_eq_maximalDifference (rate : ℝ≥0) (hr : 0 < rate) :
    (maximalDivergence rate hr).adjoint = maximalDifference rate hr := by
  rw [← closure_coreDivergence_eq_maximal rate hr,
    OperatorDerivativeRewrite.Foundation.operatorClosure_adjoint_eq
      (coreDivergence_isClosable rate hr) (coreDivergence_dense_domain rate hr)]
  exact coreDivergence_adjoint_eq_maximalDifference rate hr
end OperatorDerivativeRewrite.Foundation.PoissonAdjoints
