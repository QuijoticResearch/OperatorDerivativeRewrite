import Foundation.FiniteGaussianOperators

/-! Actual tensor Hermite lowering and raising on the polynomial gradient/divergence core. -/
noncomputable section
open MeasureTheory Polynomial Module
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FiniteGaussian
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]

/-- The verified one-dimensional operator action determines the normalized polynomial derivative. -/
theorem normalizedHermitePolynomial_derivative (n : ℕ) :
    (normalizedHermitePolynomial (n + 1)).derivative =
      Real.sqrt (n + 1 : ℝ) • normalizedHermitePolynomial n := by
  apply GaussianCore.polynomialEmbedding_injective
  have h := GaussianCore.polynomialDerivative_polynomial (normalizedHermitePolynomial (n + 1))
  rw [normalizedHermitePolynomial_L2] at h
  have he := GaussianCore.polynomialDerivative.mem_graph_snd_inj h
    (GaussianCore.normalizedHermite_derivative_graph n) rfl
  change GaussianCore.polynomialL2 _ = _
  rw [GaussianCore.polynomialEmbedding.map_smul]
  simpa only [GaussianCore.polynomialEmbedding, LinearMap.coe_mk, AddHom.coe_mk,
    normalizedHermitePolynomial_L2] using he

/-- The normalized polynomial raising action is the actual Gaussian divergence expression. -/
theorem normalizedHermitePolynomial_divergence (n : ℕ) :
    GaussianCore.divergencePolynomial (normalizedHermitePolynomial n) =
      Real.sqrt (n + 1 : ℝ) • normalizedHermitePolynomial (n + 1) := by
  apply GaussianCore.polynomialEmbedding_injective
  have h : (GaussianCore.polynomialL2 (normalizedHermitePolynomial n),
      GaussianCore.polynomialL2 (GaussianCore.divergencePolynomial (normalizedHermitePolynomial n)))
      ∈ GaussianCore.polynomialDivergence.graph := by
    rw [GaussianCore.polynomialDivergence_graph]; exact ⟨_, rfl⟩
  rw [normalizedHermitePolynomial_L2] at h
  have he := GaussianCore.polynomialDivergence.mem_graph_snd_inj h
    (GaussianCore.normalizedHermite_divergence_graph n) rfl
  change GaussianCore.polynomialL2 _ = _
  rw [GaussianCore.polynomialEmbedding.map_smul]
  simpa only [GaussianCore.polynomialEmbedding, LinearMap.coe_mk, AddHom.coe_mk,
    normalizedHermitePolynomial_L2] using he

/-- Positive-coordinate tensor lowering; the other factors remain unchanged. -/
theorem tensorHermitePolynomial_lowering [DecidableEq ι] (α : ι → ℕ) (i : ι)
    (n : ℕ) (hi : α i = n + 1) :
    MvPolynomial.pderiv i (tensorHermitePolynomial α) =
      Real.sqrt (n + 1 : ℝ) • tensorHermitePolynomial (Function.update α i n) := by
  rw [tensorHermitePolynomial, tensorPolynomialMap_pderiv, hi,
    normalizedHermitePolynomial_derivative, MultilinearMap.map_update_smul]
  congr 1
  apply congrArg tensorPolynomialMap
  funext j
  by_cases h : j = i <;> simp [h]

/-- A zero Hermite degree gives actual zero partial derivative. -/
theorem tensorHermitePolynomial_lowering_zero (α : ι → ℕ) (i : ι) (hi : α i = 0) :
    MvPolynomial.pderiv i (tensorHermitePolynomial α) = 0 := by
  classical
  rw [tensorHermitePolynomial, tensorPolynomialMap_pderiv, hi]
  simp only [normalizedHermitePolynomial, GaussianCore.hermitePolynomial_zero,
    Nat.factorial_zero, Nat.cast_one, Real.sqrt_one, inv_one, one_smul, derivative_one]
  exact MultilinearMap.map_update_zero _ _ _

/-- Coordinate Gaussian divergence acts on precisely one separable polynomial factor. -/
theorem tensorPolynomialMap_coordinateDivergence [DecidableEq ι]
    (p : ι → ℝ[X]) (i : ι) :
    coordinateDivergencePolynomial i (tensorPolynomialMap p) =
      tensorPolynomialMap (Function.update p i (GaussianCore.divergencePolynomial (p i))) := by
  have hx : MvPolynomial.X i * tensorPolynomialMap p =
      tensorPolynomialMap (Function.update p i (Polynomial.X * p i)) := by
    simp only [tensorPolynomialMap, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, AlgHom.toLinearMap_apply]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [Function.update_self, map_mul, Polynomial.aeval_X]
    rw [← mul_assoc]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [coordinateDivergencePolynomial, hx, tensorPolynomialMap_pderiv,
    ← MultilinearMap.map_update_sub]
  rfl

/-- Tensor raising is the actual coordinate Gaussian divergence, with the correct normalization. -/
theorem tensorHermitePolynomial_raising [DecidableEq ι] (α : ι → ℕ) (i : ι) :
    coordinateDivergencePolynomial i (tensorHermitePolynomial α) =
      Real.sqrt (α i + 1 : ℝ) • tensorHermitePolynomial (Function.update α i (α i + 1)) := by
  rw [tensorHermitePolynomial, tensorPolynomialMap_coordinateDivergence,
    normalizedHermitePolynomial_divergence, MultilinearMap.map_update_smul]
  congr 1
  apply congrArg tensorPolynomialMap
  funext j
  by_cases h : j = i <;> simp [h]

/-- Actual polynomial vector field with one tensor Hermite component. -/
def tensorHermiteVector [DecidableEq ι] (i : ι) (α : ι → ℕ) : VectorGaussianL2 ι :=
  vectorPolynomialL2 (Pi.single i (tensorHermitePolynomial α))

/-- The actual polynomial divergence raises a single vector Hermite component. -/
theorem tensorHermiteVector_divergence_graph [DecidableEq ι] (i : ι) (α : ι → ℕ) :
    (tensorHermiteVector i α,
      Real.sqrt (α i + 1 : ℝ) • tensorHermite (Function.update α i (α i + 1))) ∈
      polynomialDivergence.graph := by
  have h := polynomialDivergence_polynomial_graph (Pi.single i (tensorHermitePolynomial α))
  have he : divergencePolynomial (Pi.single i (tensorHermitePolynomial α)) =
      coordinateDivergencePolynomial i (tensorHermitePolynomial α) := by
    simp [divergencePolynomial, Pi.single_apply, apply_ite, coordinateDivergencePolynomial]
  rw [he, tensorHermitePolynomial_raising] at h
  change (_, productPolynomialEmbedding (_ • _)) ∈ _ at h
  rw [map_smul] at h
  simpa only [productPolynomialEmbedding, LinearMap.coe_mk, AddHom.coe_mk,
    tensorHermitePolynomial_L2, tensorHermiteVector] using h

/-- The gradient core action on a tensor is its true Euclidean-valued polynomial gradient. -/
theorem tensorHermite_gradient_graph (α : ι → ℕ) :
    (tensorHermite α, gradientPolynomialL2 (tensorHermitePolynomial α)) ∈
      polynomialGradient.graph := by
  have h := polynomialGradient_polynomial_graph (tensorHermitePolynomial α)
  rwa [tensorHermitePolynomial_L2] at h

/-- Every positive-degree gradient component has the correct lowering weight in scalar L². -/
theorem tensorHermite_gradient_component [DecidableEq ι] (α : ι → ℕ) (i : ι)
    (n : ℕ) (hi : α i = n + 1) :
    vectorL2Component i (gradientPolynomialL2 (tensorHermitePolynomial α)) =
      Real.sqrt (n + 1 : ℝ) • tensorHermite (Function.update α i n) := by
  rw [gradientPolynomialL2, vectorPolynomialL2_component]
  change productPolynomialL2 (MvPolynomial.pderiv i (tensorHermitePolynomial α)) = _
  rw [tensorHermitePolynomial_lowering α i n hi]
  change productPolynomialEmbedding (_ • _) = _
  rw [map_smul]
  change _ • productPolynomialL2 (tensorHermitePolynomial _) = _
  rw [tensorHermitePolynomial_L2]

end OperatorDerivativeRewrite.Foundation.FiniteGaussian
