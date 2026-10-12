import Foundation.GaussianNumberSectors

/-! Finite Hermite tensors are eigenvectors of the actual infinite Gaussian
number operator. Their verified density proves completeness of its sectors. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianNumberSectors
open InfiniteGaussian FiniteGaussian

theorem tensor_coordinate_number {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ι → ℕ) (i : ι) :
    coordinateDivergencePolynomial i (MvPolynomial.pderiv i (tensorHermitePolynomial α)) =
      (α i : ℝ) • tensorHermitePolynomial α := by
  by_cases hi : α i = 0
  · rw [tensorHermitePolynomial_lowering_zero α i hi]
    simp [coordinateDivergencePolynomial, hi]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hi
    rw [tensorHermitePolynomial_lowering α i k hk]
    have hs (c : ℝ) (p : MvPolynomial ι ℝ) :
        coordinateDivergencePolynomial i (c • p) = c • coordinateDivergencePolynomial i p := by
      simp [coordinateDivergencePolynomial, smul_sub]
    rw [hs, tensorHermitePolynomial_raising, Function.update_self, smul_smul]
    have he : Function.update (Function.update α i k) i (k + 1) = α := by
      ext j
      by_cases hji : j = i <;> simp [hji, hk]
    rw [he, ← pow_two, Real.sq_sqrt (by positivity), hk]
    norm_num

theorem tensor_number_polynomial {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℕ) :
    divergencePolynomial (gradientPolynomial (tensorHermitePolynomial α)) =
      ((∑ i, α i : ℕ) : ℝ) • tensorHermitePolynomial α := by
  change (∑ i, coordinateDivergencePolynomial i
    (MvPolynomial.pderiv i (tensorHermitePolynomial α))) = _
  simp only [tensor_coordinate_number, ← Finset.sum_smul, Nat.cast_sum]

theorem finiteHermite_mem_sector (s : Finset ℕ) (α : s → ℕ) :
    finitePullback s (tensorHermite α) ∈ sector (∑ i, α i) := by
  apply (mem_sector _ _).mpr
  refine ⟨finiteVectorPullback s (gradientPolynomialL2 (tensorHermitePolynomial α)), ?_, ?_⟩
  · have h : (finitePullback s (productPolynomialL2 (tensorHermitePolynomial α)),
        finiteVectorPullback s (gradientPolynomialL2 (tensorHermitePolynomial α))) ∈
          closedCylindricalDerivative.graph := by
      rw [closedCylindricalDerivative_graph]
      exact cylindricalDerivative.graph.le_topologicalClosure
        (finitePolynomialGradient_lift_graph s (tensorHermitePolynomial α))
    simpa only [tensorHermitePolynomial_L2] using h
  · have h := LinearPMap.le_graph_of_le cylindricalDivergence_le_hilbertDivergence
      (finitePolynomialDivergence_lift_graph s (gradientPolynomial (tensorHermitePolynomial α)))
    rw [tensor_number_polynomial] at h
    change (_, finitePullback s (productPolynomialEmbedding (_ • _))) ∈ _ at h
    rw [map_smul, map_smul] at h
    change (_, ((∑ i, α i : ℕ) : ℝ) •
      finitePullback s (productPolynomialL2 (tensorHermitePolynomial α))) ∈ _ at h
    rw [tensorHermitePolynomial_L2] at h
    exact h

theorem sector_total : (⨆ n, sector n).topologicalClosure = ⊤ := by
  let S := (⨆ n, sector n).topologicalClosure
  have hf (s : Finset ℕ) (g : ScalarGaussianL2 s) : finitePullback s g ∈ S := by
    have h : Submodule.span ℝ (Set.range (tensorHermite (ι := s))) ≤
        S.comap (finitePullback s).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨α, rfl⟩
      exact (⨆ n, sector n).le_topologicalClosure
        (le_iSup sector (∑ i, α i) (finiteHermite_mem_sector s α))
    have hc : IsClosed (S.comap (finitePullback s).toLinearMap : Set (ScalarGaussianL2 s)) :=
      (⨆ n, sector n).isClosed_topologicalClosure.preimage (finitePullback s).continuous
    exact (closure_minimal h hc) (tensorHermite_dense_span g)
  have hd : Dense (S : Set GaussianL2) := polynomialCylinders_dense.mono (by
    intro f hmem
    obtain ⟨s, p, rfl⟩ := Set.mem_iUnion.mp hmem
    exact hf s (productPolynomialL2 p))
  have ht := Submodule.dense_iff_topologicalClosure_eq_top.mp hd
  rwa [(⨆ n, sector n).isClosed_topologicalClosure.submodule_topologicalClosure_eq] at ht

end OperatorDerivativeRewrite.Foundation.GaussianNumberSectors
