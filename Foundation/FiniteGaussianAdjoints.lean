import Foundation.FiniteGaussianTruncation

/-! Full gradient identification by total-degree graph approximation. -/
noncomputable section
open MeasureTheory Polynomial Module Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FiniteGaussian
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Tensor-coordinate vector pairings are the actual scalar component coefficients. -/
theorem tensorHermiteVector_inner (u : VectorGaussianL2 ι) (i : ι) (α : ι → ℕ) :
    inner ℝ (tensorHermiteVector i α) u = vectorHermiteCoefficient u i α := by
  rw [real_inner_comm, tensorHermiteVector, vectorPolynomialL2_inner]
  have hz : productPolynomialL2 (0 : MvPolynomial ι ℝ) = 0 := productPolynomialEmbedding.map_zero
  simp [Pi.single_apply, apply_ite, hz, tensorHermitePolynomial_L2,
    vectorHermiteCoefficient, scalarHermiteCoefficient, real_inner_comm]

/-- Testing the genuine divergence raising action gives all maximal gradient coefficients. -/
theorem divergence_adjoint_coefficients {f : ScalarGaussianL2 ι} {g : VectorGaussianL2 ι}
    (h : (f, g) ∈ polynomialDivergence.adjoint.graph) (i : ι) (α : ι → ℕ) :
    vectorHermiteCoefficient g i α = gradientCoefficient f i α := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint polynomialDivergence_dense_domain] at h
  have hh := (Submodule.mem_adjoint_iff _ _).mp h _ _ (tensorHermiteVector_divergence_graph i α)
  rw [real_inner_smul_left, tensorHermiteVector_inner, sub_eq_zero] at hh
  exact hh.symm

omit [DecidableEq ι] in
/-- Completeness of scalar components determines actual vector L² classes. -/
theorem vectorHermiteCoefficient_ext {u v : VectorGaussianL2 ι}
    (h : ∀ i α, vectorHermiteCoefficient u i α = vectorHermiteCoefficient v i α) : u = v := by
  classical
  have hc (i : ι) : vectorL2Component i u = vectorL2Component i v :=
    scalarHermiteCoefficient_ext (h i)
  rw [← vectorL2_reassemble u, ← vectorL2_reassemble v]
  simp only [hc]

/-- Raising a coordinate increases total degree by exactly one. -/
theorem hermiteDegree_raise (α : ι → ℕ) (i : ι) :
    hermiteDegree (Function.update α i (α i + 1)) = hermiteDegree α + 1 := by
  unfold hermiteDegree
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
  have h : (∑ j ∈ Finset.univ.erase i, α j) + α i = ∑ j, α j :=
    Finset.sum_erase_add Finset.univ α (Finset.mem_univ i)
  omega

/-- The lowering action commutes with total-degree projection and a one-degree shift. -/
theorem gradientCoefficient_truncation (f : ScalarGaussianL2 ι) (N : ℕ) (i : ι) (α : ι → ℕ) :
    gradientCoefficient (scalarHermiteTruncation f (N + 1)) i α =
      if hermiteDegree α ≤ N then gradientCoefficient f i α else 0 := by
  unfold gradientCoefficient
  rw [scalarHermiteTruncation_coefficient, hermiteDegree_raise]
  by_cases hN : hermiteDegree α ≤ N
  · have hb : hermiteDegree α + 1 ≤ N + 1 := by omega
    simp only [hN, hb, ↓reduceIte]
  · have hb : ¬ hermiteDegree α + 1 ≤ N + 1 := by omega
    simp only [hN, hb, ↓reduceIte, mul_zero]

/-- Actual polynomial gradient graph approximants for every maximal gradient pair. -/
theorem divergence_adjoint_truncation_graph (f : ScalarGaussianL2 ι) (g : VectorGaussianL2 ι)
    (h : (f, g) ∈ polynomialDivergence.adjoint.graph) (N : ℕ) :
    (scalarHermiteTruncation f (N + 1), vectorHermiteTruncation g N) ∈
      polynomialGradient.graph := by
  have hc := polynomialGradient_polynomial_graph (scalarHermiteTruncationPolynomial f (N + 1))
  rw [scalarHermiteTruncationPolynomial_L2] at hc
  have he : gradientPolynomialL2 (scalarHermiteTruncationPolynomial f (N + 1)) =
      vectorHermiteTruncation g N := by
    apply vectorHermiteCoefficient_ext
    intro i α
    rw [divergence_adjoint_coefficients
      (LinearPMap.le_graph_of_le polynomialGradient_le_divergence_adjoint hc),
      gradientCoefficient_truncation, vectorHermiteTruncation_coefficient,
      divergence_adjoint_coefficients h i α]
  rwa [he] at hc

/-- The approximants converge in both L² coordinates and therefore in graph norm. -/
theorem divergence_adjoint_truncation_tendsto (f : ScalarGaussianL2 ι) (g : VectorGaussianL2 ι) :
    Tendsto (fun N => (scalarHermiteTruncation f (N + 1), vectorHermiteTruncation g N))
      atTop (𝓝 (f, g)) :=
  ((scalarHermiteTruncation_tendsto f).comp (tendsto_add_atTop_nat 1)).prodMk_nhds
    (vectorHermiteTruncation_tendsto g)

omit [DecidableEq ι] in
/-- Reverse inclusion is proved by the explicit genuine polynomial graph approximants. -/
theorem closedGradient_graph_of_adjoint {f : ScalarGaussianL2 ι} {g : VectorGaussianL2 ι}
    (h : (f, g) ∈ polynomialDivergence.adjoint.graph) : (f, g) ∈ closedGradient.graph := by
  classical
  rw [← polynomialGradient_isClosable.graph_closure_eq_closure_graph]
  apply mem_closure_of_tendsto (divergence_adjoint_truncation_tendsto f g)
  exact Eventually.of_forall (divergence_adjoint_truncation_graph f g h)

omit [DecidableEq ι] in
/-- Full gradient identification, proved independently of the divergence approximation. -/
theorem closedGradient_eq_divergence_adjoint :
    (closedGradient (ι := ι)) = polynomialDivergence.adjoint := by
  classical
  apply le_antisymm closedGradient_le_divergence_adjoint
  apply LinearPMap.le_of_le_graph
  rintro ⟨f, g⟩ h
  exact closedGradient_graph_of_adjoint h

omit [DecidableEq ι] in
/-- Taking the adjoint is unchanged by closing the densely defined divergence. -/
theorem closedVectorDivergence_adjoint_eq :
    (closedVectorDivergence (ι := ι)).adjoint = polynomialDivergence.adjoint :=
  operatorClosure_adjoint_eq polynomialDivergence_isClosable polynomialDivergence_dense_domain

omit [DecidableEq ι] in
/-- The two verified closed operators are genuine mutual Hilbert adjoints. -/
theorem closedGradient_eq_closedVectorDivergence_adjoint :
    (closedGradient (ι := ι)) = closedVectorDivergence.adjoint := by
  classical
  rw [closedVectorDivergence_adjoint_eq, closedGradient_eq_divergence_adjoint]

omit [DecidableEq ι] in
/-- The reverse closed adjoint identity retains the combined-coefficient domain. -/
theorem closedVectorDivergence_eq_closedGradient_adjoint :
    (closedVectorDivergence (ι := ι)) = closedGradient.adjoint := by
  classical
  rw [closedGradient_adjoint_eq, closedVectorDivergence_eq_gradient_adjoint]

omit [DecidableEq ι] in
/-- The finite scalar tensor span is a graph core of the full maximal gradient. -/
theorem divergence_adjoint_has_polynomial_core :
    (polynomialDivergence (ι := ι)).adjoint.HasCore productPolynomialEmbedding.range := by
  classical
  rw [← closedGradient_eq_divergence_adjoint]
  exact closedGradient_has_polynomial_core

omit [DecidableEq ι] in
/-- The finite vector polynomial span is a graph core of the full maximal divergence. -/
theorem gradient_adjoint_has_polynomial_core :
    (polynomialGradient (ι := ι)).adjoint.HasCore vectorPolynomialEmbedding.range := by
  classical
  rw [← closedVectorDivergence_eq_gradient_adjoint]
  exact closedVectorDivergence_has_polynomial_core

end OperatorDerivativeRewrite.Foundation.FiniteGaussian
