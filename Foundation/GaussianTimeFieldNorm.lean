import Foundation.GaussianTimePolynomialIntegral

/-!
# Actual vector-L² norms of time-step fields

Orthogonality of deterministic interval directions gives the elapsed-time norm
formula even for arbitrary scalar L² coefficients. On polynomial past
coefficients this is exactly the norm of the genuine predictable integral,
whose value already agrees with the existing Gaussian divergence.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace OperatorDerivativeRewrite.Foundation.GaussianTimeFieldNorm

open InfiniteGaussian GaussianTimeHilbert GaussianTimeProcess GaussianTimeDivergence
open GaussianTimePolynomialIntegral SeparableHilbertEmbedding
attribute [local instance] timeHilbert_secondCountable

/-- Pairing two actual rank-one fields factors into scalar and deterministic pairings. -/
theorem scalarTensor_pair_inner (h k : CoefficientSpace) (f g : GaussianL2) :
    inner ℝ (scalarTensor h f) (scalarTensor k g) = inner ℝ f g * inner ℝ h k := by
  rw [L2_inner_eq_integral, L2_inner_eq_integral, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [scalarTensor_coeFn h f, scalarTensor_coeFn k g] with ω hf hg
  simp [hf, hg, real_inner_smul_left, inner_smul_right, mul_assoc, mul_comm]

theorem incrementDirection_norm_sq (s t : ℝ≥0) (hst : s ≤ t) :
    ‖incrementDirection s t‖ ^ 2 = (t : ℝ) - s := by
  unfold incrementDirection
  rw [(hilbertEmbedding TimeHilbert).norm_map, ← timeVector_sub s t hst]
  exact timeVector_sub_norm_sq s t hst

/-- Distinct partition intervals remain orthogonal after the actual Hilbert embedding. -/
theorem partitionDirection_inner_eq_zero {n : ℕ}
    (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ) (i j : Fin n) (hij : i ≠ j) :
    inner ℝ (incrementDirection (τ i.castSucc) (τ i.succ))
      (incrementDirection (τ j.castSucc) (τ j.succ)) = 0 := by
  wlog h : i < j generalizing i j
  · rw [real_inner_comm]
    exact this j i hij.symm (lt_of_le_of_ne (le_of_not_gt h) hij.symm)
  unfold incrementDirection
  rw [(hilbertEmbedding TimeHilbert).inner_map_map,
    ← timeVector_sub _ _ (hτ (Fin.castSucc_le_succ i)),
    ← timeVector_sub _ _ (hτ (Fin.castSucc_le_succ j))]
  exact timeVector_increments_orthogonal _ _ _ _
    (hτ (Fin.castSucc_le_succ i)) (hτ (Fin.succ_le_castSucc_iff.mpr h))
    (hτ (Fin.castSucc_le_succ j))

/-- The actual embedded vector-L² field of a finite time partition. -/
def partitionField {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (A : Fin n → GaussianL2) :
    GaussianVectorL2 :=
  ∑ i, scalarTensor (incrementDirection (τ i.castSucc) (τ i.succ)) (A i)

/-- The field norm formula uses orthogonal time intervals, without adaptation assumptions. -/
theorem partitionField_norm_sq {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (A : Fin n → GaussianL2) :
    ‖partitionField τ A‖ ^ 2 =
      ∑ i, ((τ i.succ : ℝ) - τ i.castSucc) * ‖A i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, partitionField, sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [scalarTensor_pair_inner, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      incrementDirection_norm_sq _ _ (hτ (Fin.castSucc_le_succ i)), mul_comm]
  · intro j _ hji
    rw [scalarTensor_pair_inner, partitionDirection_inner_eq_zero τ hτ i j hji.symm,
      mul_zero]
  · simp

theorem polynomialPartitionField_norm_sq {ι : Type*} [Fintype ι] {n : ℕ}
    (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (r : (i : Fin n) → ι → Set.Iic (τ i.castSucc)) (p : Fin n → MvPolynomial ι ℝ) :
    ‖polynomialPartitionField τ r p‖ ^ 2 =
      ∑ i, ((τ i.succ : ℝ) - τ i.castSucc) *
        ∫ ω, (MvPolynomial.eval (fun j => process (r i j) ω) (p i)) ^ 2
          ∂gaussianProduct := by
  rw [show polynomialPartitionField τ r p =
    partitionField τ (fun i => pastCoefficient (fun j => r i j) (p i)) from rfl,
    partitionField_norm_sq τ hτ]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [← real_inner_self_eq_norm_sq, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [pastCoefficient_coeFn (fun j => (r i j).val) (p i)] with ω hω
  simp [hω]

/-- Actual vector-L² Itô isometry on the polynomial common domain of both constructions. -/
theorem polynomialPartitionIntegralL2_norm_sq_eq_field {ι : Type*} [Fintype ι] {n : ℕ}
    (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (r : (i : Fin n) → ι → Set.Iic (τ i.castSucc)) (p : Fin n → MvPolynomial ι ℝ) :
    ‖polynomialPartitionIntegralL2 τ hτ r p‖ ^ 2 =
      ‖polynomialPartitionField τ r p‖ ^ 2 := by
  rw [polynomialPartitionIntegralL2_norm_sq, polynomialPartitionField_norm_sq τ hτ]

theorem polynomialPartitionIntegralL2_norm_eq_field {ι : Type*} [Fintype ι] {n : ℕ}
    (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (r : (i : Fin n) → ι → Set.Iic (τ i.castSucc)) (p : Fin n → MvPolynomial ι ℝ) :
    ‖polynomialPartitionIntegralL2 τ hτ r p‖ = ‖polynomialPartitionField τ r p‖ := by
  have h := polynomialPartitionIntegralL2_norm_sq_eq_field τ hτ r p
  nlinarith [norm_nonneg (polynomialPartitionIntegralL2 τ hτ r p),
    norm_nonneg (polynomialPartitionField τ r p)]

end OperatorDerivativeRewrite.Foundation.GaussianTimeFieldNorm
