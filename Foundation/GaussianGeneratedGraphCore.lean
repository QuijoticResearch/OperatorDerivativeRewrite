import Foundation.GaussianConditionalGraph

/-! Polynomial graph density inside an arbitrary Gaussian-generated scalar
subspace, for the original closed derivative. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianGeneratedGraphCore
open InfiniteGaussian GaussianNumberSectors GaussianConditionalGraph
variable {I : Type*}

theorem familyPolynomial_mem_core (h : I → CoefficientSpace) (p : MvPolynomial I ℝ) :
    familyPolynomialEmbedding h p ∈ polynomialCylindricalDomain := by
  obtain ⟨s, p, rfl⟩ := MvPolynomial.exists_finset_rename p
  rw [familyPolynomial_rename]
  exact isonormalCylinderL2_mem_core (fun i : s => h i) p

def familyCore (h : I → CoefficientSpace) : MvPolynomial I ℝ →ₗ[ℝ] polynomialCylindricalDomain :=
  (familyPolynomialEmbedding h).codRestrict polynomialCylindricalDomain (familyPolynomial_mem_core h)

def familyGraphMap (h : I → CoefficientSpace) :
    MvPolynomial I ℝ →ₗ[ℝ] (GaussianL2 × GaussianVectorL2) :=
  (familyPolynomialEmbedding h).prod (polynomialDerivative.comp (familyCore h))

def completedFamilyGraph (h : I → CoefficientSpace) : Submodule ℝ (GaussianL2 × GaussianVectorL2) :=
  (familyGraphMap h).range.topologicalClosure

theorem completedFamilyGraph_le_derivative (h : I → CoefficientSpace) :
    completedFamilyGraph h ≤ closedCylindricalDerivative.graph := by
  apply Submodule.topologicalClosure_minimal
  · rintro z ⟨p, rfl⟩
    exact closedCylindricalDerivative_core_graph (familyCore h p)
  · exact closedCylindricalDerivative_isClosed

theorem completedFamilyGraph_measurable (h : I → CoefficientSpace)
    {z : GaussianL2 × GaussianVectorL2} (hz : z ∈ completedFamilyGraph h) : z.1 ∈ generated h := by
  have hs : completedFamilyGraph h ≤ (generated h).comap (LinearMap.fst ℝ _ _) := by
    apply Submodule.topologicalClosure_minimal
    · rintro z ⟨p, rfl⟩
      exact familyPolynomial_aestronglyMeasurable h p
    · exact (generated_isClosed h).preimage continuous_fst
  exact hs hz

theorem projected_polynomial_graph (n : ℕ) (h : I → CoefficientSpace) (p : MvPolynomial I ℝ) :
    (projection n (familyPolynomialEmbedding h p), projectedGradient n (familyPolynomialEmbedding h p)) ∈
      (familyGraphMap h).range := by
  obtain ⟨q, hq⟩ := projection_familyPolynomial n h p
  have hd : projectedGradient n (familyPolynomialEmbedding h p) =
      polynomialDerivative (familyCore h q) := by
    have hg := (projectedGradient_graph n (familyPolynomialEmbedding h p)).1
    rw [hq] at hg
    exact closedCylindricalDerivative.mem_graph_snd_inj hg
      (closedCylindricalDerivative_core_graph (familyCore h q)) rfl
  refine ⟨q, ?_⟩
  change (familyPolynomialEmbedding h q, polynomialDerivative (familyCore h q)) = _
  rw [hq, hd]

theorem projected_generated_graph (n : ℕ) (h : I → CoefficientSpace)
    {f : GaussianL2} (hf : f ∈ generated h) :
    (projection n f, projectedGradient n f) ∈ completedFamilyGraph h := by
  let L := (projection n).prod (projectedGradient n)
  have hs : (familyPolynomialEmbedding h).range.topologicalClosure ≤
      (completedFamilyGraph h).comap L.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro f ⟨p, rfl⟩
      exact (familyGraphMap h).range.le_topologicalClosure (projected_polynomial_graph n h p)
    · exact (familyGraphMap h).range.isClosed_topologicalClosure.preimage L.continuous
  rw [familyPolynomial_closure] at hs
  exact hs hf

theorem independent_graph_mem_completedFamily (h : I → CoefficientSpace)
    {f : GaussianL2} {g : GaussianVectorL2} (hf : f ∈ generated h)
    (hd : (f, g) ∈ closedCylindricalDerivative.graph) : (f, g) ∈ completedFamilyGraph h := by
  apply (familyGraphMap h).range.isClosed_topologicalClosure.mem_of_tendsto
    (simultaneous_graph_tendsto hd)
  apply Eventually.of_forall
  intro N
  change (truncation N f, gradientTruncation N f) ∈ completedFamilyGraph h
  rw [truncation, gradientTruncation, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.sum_apply, prod_mk_sum]
  exact (completedFamilyGraph h).sum_mem (fun n _ => projected_generated_graph n h hf)

theorem completedFamilyGraph_eq_independent (h : I → CoefficientSpace) :
    completedFamilyGraph h = closedCylindricalDerivative.graph ⊓
      (generated h).comap (LinearMap.fst ℝ GaussianL2 GaussianVectorL2) := by
  apply le_antisymm
  · intro z hz
    exact ⟨completedFamilyGraph_le_derivative h hz, completedFamilyGraph_measurable h hz⟩
  · rintro z ⟨hd, hf⟩
    exact independent_graph_mem_completedFamily h hf hd

theorem exists_polynomial_graph_sequence (h : I → CoefficientSpace)
    {f : GaussianL2} {g : GaussianVectorL2} (hf : f ∈ generated h)
    (hd : (f, g) ∈ closedCylindricalDerivative.graph) :
    ∃ p : ℕ → MvPolynomial I ℝ,
      Tendsto (fun n => (familyPolynomialEmbedding h (p n), polynomialDerivative (familyCore h (p n))))
        atTop (𝓝 (f, g)) := by
  obtain ⟨z, hz, ht⟩ := mem_closure_iff_seq_limit.mp (independent_graph_mem_completedFamily h hf hd)
  choose p hp using hz
  refine ⟨p, ?_⟩
  convert ht using 1
  funext n
  exact hp n

end OperatorDerivativeRewrite.Foundation.GaussianGeneratedGraphCore
