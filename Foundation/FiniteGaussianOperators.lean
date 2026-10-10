import Foundation.FiniteGaussianVector
import Foundation.AdjointClosure

/-! Genuine densely defined, closable Gaussian polynomial gradient and divergence.
Only adjoint inclusions are asserted; maximal graph-domain identification is separate. -/
noncomputable section
open MeasureTheory Polynomial Module
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FiniteGaussian
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]

/-- Polynomial gradient is the family of actual partial derivatives. -/
def gradientPolynomial : MvPolynomial ι ℝ →ₗ[ℝ] (ι → MvPolynomial ι ℝ) :=
  LinearMap.pi fun i => (MvPolynomial.pderiv i).toLinearMap

/-- Gaussian divergence, with the positive adjoint sign convention. -/
def divergencePolynomial : (ι → MvPolynomial ι ℝ) →ₗ[ℝ] MvPolynomial ι ℝ where
  toFun u := ∑ i, coordinateDivergencePolynomial i (u i)
  map_add' u v := by
    simp [coordinateDivergencePolynomial, mul_add, Finset.sum_add_distrib]; abel
  map_smul' c u := by
    simp [coordinateDivergencePolynomial, smul_sub, ← Finset.smul_sum]

/-- The actual gradient as an Euclidean-valued polynomial L² class. -/
def gradientPolynomialL2 (p : MvPolynomial ι ℝ) : VectorGaussianL2 ι :=
  vectorPolynomialL2 (gradientPolynomial p)

/-- Scalar polynomial Hilbert pairing equals its integrable product integral. -/
theorem productPolynomialL2_inner (p q : MvPolynomial ι ℝ) :
    inner ℝ (productPolynomialL2 p) (productPolynomialL2 q) =
      ∫ x, MvPolynomial.eval x p * MvPolynomial.eval x q ∂productGaussian ι := by
  rw [L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [productPolynomialL2_coeFn p, productPolynomialL2_coeFn q] with x hp hq
  rw [hp, hq, Real.inner_apply]

/-- Genuine scalar/vector polynomial integration by parts. -/
theorem gradient_divergence_polynomial_pairing (p : MvPolynomial ι ℝ)
    (u : ι → MvPolynomial ι ℝ) :
    inner ℝ (gradientPolynomialL2 p) (vectorPolynomialL2 u) =
      inner ℝ (productPolynomialL2 p) (productPolynomialL2 (divergencePolynomial u)) := by
  have hi (i : ι) : Integrable (fun x => MvPolynomial.eval x p *
      MvPolynomial.eval x (coordinateDivergencePolynomial i (u i))) (productGaussian ι) :=
    mul_L2_integrable (productPolynomial_memLp p 2 (by simp))
      (productPolynomial_memLp _ 2 (by simp))
  rw [vectorPolynomialL2_inner]
  simp only [gradientPolynomialL2, vectorPolynomialL2_component, productPolynomialL2_inner]
  change (∑ i, ∫ x, MvPolynomial.eval x (MvPolynomial.pderiv i p) *
      MvPolynomial.eval x (u i) ∂productGaussian ι) = _
  simp only [divergencePolynomial, LinearMap.coe_mk, AddHom.coe_mk, map_sum, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  exact productPolynomial_integration_by_parts p (u i) i

/-- Gradient graph contains only actual polynomial evaluations and actual derivatives. -/
def polynomialGradientGraph : Submodule ℝ (ScalarGaussianL2 ι × VectorGaussianL2 ι) :=
  LinearMap.range (productPolynomialEmbedding.prod
    (vectorPolynomialEmbedding.comp gradientPolynomial))

/-- Divergence graph contains only actual fields and their Gaussian divergence expressions. -/
def polynomialDivergenceGraph : Submodule ℝ (VectorGaussianL2 ι × ScalarGaussianL2 ι) :=
  LinearMap.range (vectorPolynomialEmbedding.prod
    (productPolynomialEmbedding.comp divergencePolynomial))

theorem polynomialGradientGraph_vertical_zero (z : ScalarGaussianL2 ι × VectorGaussianL2 ι)
    (hz : z ∈ polynomialGradientGraph) (hzero : z.1 = 0) : z.2 = 0 := by
  obtain ⟨p, hp⟩ := hz
  subst z
  have hp0 : p = 0 := productPolynomialEmbedding_injective (by simpa using hzero)
  change vectorPolynomialEmbedding (gradientPolynomial p) = 0
  rw [hp0, map_zero, map_zero]

theorem polynomialDivergenceGraph_vertical_zero (z : VectorGaussianL2 ι × ScalarGaussianL2 ι)
    (hz : z ∈ polynomialDivergenceGraph) (hzero : z.1 = 0) : z.2 = 0 := by
  obtain ⟨u, hu⟩ := hz
  subst z
  have hu0 : u = 0 := vectorPolynomialEmbedding_injective (by simpa using hzero)
  change productPolynomialEmbedding (divergencePolynomial u) = 0
  rw [hu0, map_zero, map_zero]

/-- ∇₀ has exactly the algebraic scalar polynomial L² domain. -/
def polynomialGradient : ScalarGaussianL2 ι →ₗ.[ℝ] VectorGaussianL2 ι :=
  polynomialGradientGraph.toLinearPMap

/-- δ₀ has exactly the algebraic vector polynomial L² domain. -/
def polynomialDivergence : VectorGaussianL2 ι →ₗ.[ℝ] ScalarGaussianL2 ι :=
  polynomialDivergenceGraph.toLinearPMap

theorem polynomialGradient_graph :
    (polynomialGradient (ι := ι)).graph = polynomialGradientGraph :=
  polynomialGradientGraph.toLinearPMap_graph_eq polynomialGradientGraph_vertical_zero

theorem polynomialDivergence_graph :
    (polynomialDivergence (ι := ι)).graph = polynomialDivergenceGraph :=
  polynomialDivergenceGraph.toLinearPMap_graph_eq polynomialDivergenceGraph_vertical_zero

theorem polynomialGradient_polynomial_graph (p : MvPolynomial ι ℝ) :
    (productPolynomialL2 p, gradientPolynomialL2 p) ∈ polynomialGradient.graph := by
  rw [polynomialGradient_graph]
  exact ⟨p, rfl⟩

theorem polynomialDivergence_polynomial_graph (u : ι → MvPolynomial ι ℝ) :
    (vectorPolynomialL2 u, productPolynomialL2 (divergencePolynomial u)) ∈
      polynomialDivergence.graph := by
  rw [polynomialDivergence_graph]
  exact ⟨u, rfl⟩

theorem polynomialGradient_domain :
    polynomialGradient.domain = (productPolynomialEmbedding (ι := ι)).range := by
  ext f
  rw [LinearPMap.mem_domain_iff, polynomialGradient_graph]
  constructor
  · rintro ⟨g, p, hp⟩
    exact ⟨p, congrArg Prod.fst hp⟩
  · rintro ⟨p, rfl⟩
    exact ⟨gradientPolynomialL2 p, p, rfl⟩

theorem polynomialDivergence_domain :
    polynomialDivergence.domain = (vectorPolynomialEmbedding (ι := ι)).range := by
  ext u
  rw [LinearPMap.mem_domain_iff, polynomialDivergence_graph]
  constructor
  · rintro ⟨g, v, hv⟩
    exact ⟨v, congrArg Prod.fst hv⟩
  · rintro ⟨v, rfl⟩
    exact ⟨productPolynomialL2 (divergencePolynomial v), v, rfl⟩

theorem polynomialGradient_dense_domain :
    Dense ((polynomialGradient (ι := ι)).domain : Set (ScalarGaussianL2 ι)) := by
  rw [polynomialGradient_domain]
  exact productPolynomialEmbedding_dense

theorem polynomialDivergence_dense_domain :
    Dense ((polynomialDivergence (ι := ι)).domain : Set (VectorGaussianL2 ι)) := by
  rw [polynomialDivergence_domain]
  exact vectorPolynomialEmbedding_dense

/-- The formal adjoint identity is proved on the actual two operator domains. -/
theorem polynomialGradient_formalAdjoint :
    (polynomialGradient (ι := ι)).IsFormalAdjoint polynomialDivergence := by
  intro f u
  have hf := polynomialGradient.mem_graph f
  have hu := polynomialDivergence.mem_graph u
  rw [polynomialGradient_graph] at hf
  rw [polynomialDivergence_graph] at hu
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hu
  have hp1 := congrArg Prod.fst hp
  have hp2 := congrArg Prod.snd hp
  have hq1 := congrArg Prod.fst hq
  have hq2 := congrArg Prod.snd hq
  change productPolynomialL2 p = (f : ScalarGaussianL2 ι) at hp1
  change gradientPolynomialL2 p = polynomialGradient f at hp2
  change vectorPolynomialL2 q = (u : VectorGaussianL2 ι) at hq1
  change productPolynomialL2 (divergencePolynomial q) = polynomialDivergence u at hq2
  rw [← hp1, ← hp2, ← hq1, ← hq2]
  exact gradient_divergence_polynomial_pairing p q

/-- ∇₀ ⊆ δ₀*, including domain inclusion and values. -/
theorem polynomialGradient_le_divergence_adjoint :
    (polynomialGradient (ι := ι)) ≤ polynomialDivergence.adjoint :=
  polynomialGradient_formalAdjoint.symm.le_adjoint polynomialDivergence_dense_domain

/-- δ₀ ⊆ ∇₀*, including domain inclusion and values. -/
theorem polynomialDivergence_le_gradient_adjoint :
    (polynomialDivergence (ι := ι)) ≤ polynomialGradient.adjoint :=
  polynomialGradient_formalAdjoint.le_adjoint polynomialGradient_dense_domain

/-- Genuine closability follows from the closed adjoint extension, not a closure hypothesis. -/
theorem polynomialGradient_isClosable : (polynomialGradient (ι := ι)).IsClosable :=
  (polynomialDivergence.adjoint_isClosed polynomialDivergence_dense_domain).isClosable.leIsClosable
    polynomialGradient_le_divergence_adjoint

theorem polynomialDivergence_isClosable : (polynomialDivergence (ι := ι)).IsClosable :=
  (polynomialGradient.adjoint_isClosed polynomialGradient_dense_domain).isClosable.leIsClosable
    polynomialDivergence_le_gradient_adjoint

abbrev closedGradient := (polynomialGradient (ι := ι)).closure
abbrev closedVectorDivergence := (polynomialDivergence (ι := ι)).closure

theorem closedGradient_isClosed : (closedGradient (ι := ι)).IsClosed :=
  polynomialGradient_isClosable.closure_isClosed

theorem closedVectorDivergence_isClosed : (closedVectorDivergence (ι := ι)).IsClosed :=
  polynomialDivergence_isClosable.closure_isClosed

theorem closedGradient_dense_domain :
    Dense ((closedGradient (ι := ι)).domain : Set (ScalarGaussianL2 ι)) :=
  operatorClosure_dense_domain polynomialGradient_dense_domain

theorem closedVectorDivergence_dense_domain :
    Dense ((closedVectorDivergence (ι := ι)).domain : Set (VectorGaussianL2 ι)) :=
  operatorClosure_dense_domain polynomialDivergence_dense_domain

/-- The strongest closed-gradient inclusion established here; equality is not inferred. -/
theorem closedGradient_le_divergence_adjoint :
    (closedGradient (ι := ι)) ≤ polynomialDivergence.adjoint :=
  operatorClosure_le_closed polynomialGradient_isClosable
    (polynomialDivergence.adjoint_isClosed polynomialDivergence_dense_domain)
    polynomialGradient_le_divergence_adjoint

theorem closedVectorDivergence_le_gradient_adjoint :
    (closedVectorDivergence (ι := ι)) ≤ polynomialGradient.adjoint :=
  operatorClosure_le_closed polynomialDivergence_isClosable
    (polynomialGradient.adjoint_isClosed polynomialGradient_dense_domain)
    polynomialDivergence_le_gradient_adjoint

theorem closedGradient_polynomial_graph (p : MvPolynomial ι ℝ) :
    (productPolynomialL2 p, gradientPolynomialL2 p) ∈ closedGradient.graph :=
  LinearPMap.le_graph_of_le polynomialGradient.le_closure (polynomialGradient_polynomial_graph p)

theorem closedVectorDivergence_polynomial_graph (u : ι → MvPolynomial ι ℝ) :
    (vectorPolynomialL2 u, productPolynomialL2 (divergencePolynomial u)) ∈
      closedVectorDivergence.graph :=
  LinearPMap.le_graph_of_le polynomialDivergence.le_closure
    (polynomialDivergence_polynomial_graph u)

/-- Polynomials are graph cores for these closures, not automatically for the maximal adjoints. -/
theorem closedGradient_has_polynomial_core :
    (closedGradient (ι := ι)).HasCore productPolynomialEmbedding.range := by
  rw [← polynomialGradient_domain]
  exact polynomialGradient.closureHasCore

theorem closedVectorDivergence_has_polynomial_core :
    (closedVectorDivergence (ι := ι)).HasCore vectorPolynomialEmbedding.range := by
  rw [← polynomialDivergence_domain]
  exact polynomialDivergence.closureHasCore

/-- The polynomial gradient is the actual Fréchet gradient on the Euclidean coordinate model. -/
theorem gradientPolynomial_hasFDerivAt (p : MvPolynomial ι ℝ) (z : EuclideanSpace ℝ ι) :
    HasFDerivAt (fun y : EuclideanSpace ℝ ι => MvPolynomial.eval y.ofLp p)
      (innerSL ℝ (vectorPolynomialFunction (gradientPolynomial p) z.ofLp)) z := by
  let b := EuclideanSpace.basisFun ι ℝ
  have hc : cylinder b p = (fun y : EuclideanSpace ℝ ι => MvPolynomial.eval y.ofLp p) := by
    funext y
    simp [cylinder, coordinate, b]
  have hg : cylinderGradient b p z = vectorPolynomialFunction (gradientPolynomial p) z.ofLp := by
    simpa [cylinderGradient, cylinder, coordinate, b, gradientPolynomial, vectorPolynomialFunction]
      using b.sum_repr (vectorPolynomialFunction (gradientPolynomial p) z.ofLp)
  have h := cylinder_hasFDerivAt b p z
  rwa [hc, hg] at h

/-- Closing the genuine operator preserves the actual polynomial gradient value. -/
theorem closedGradient_polynomial_apply (p : MvPolynomial ι ℝ)
    (hp : productPolynomialL2 p ∈ closedGradient.domain) :
    closedGradient ⟨productPolynomialL2 p, hp⟩ = gradientPolynomialL2 p :=
  closedGradient.mem_graph_snd_inj (closedGradient.mem_graph ⟨productPolynomialL2 p, hp⟩)
    (closedGradient_polynomial_graph p) rfl

/-- Closing the genuine operator preserves the actual Gaussian polynomial divergence value. -/
theorem closedVectorDivergence_polynomial_apply (u : ι → MvPolynomial ι ℝ)
    (hu : vectorPolynomialL2 u ∈ closedVectorDivergence.domain) :
    closedVectorDivergence ⟨vectorPolynomialL2 u, hu⟩ =
      productPolynomialL2 (divergencePolynomial u) :=
  closedVectorDivergence.mem_graph_snd_inj
    (closedVectorDivergence.mem_graph ⟨vectorPolynomialL2 u, hu⟩)
    (closedVectorDivergence_polynomial_graph u) rfl

end OperatorDerivativeRewrite.Foundation.FiniteGaussian
