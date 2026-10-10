import Foundation.FiniteGaussianLadders

/-! Spectral characterization of the actual polynomial gradient adjoint.
The divergence coefficients combine coordinates before imposing square summability. -/
noncomputable section
open MeasureTheory Polynomial Module
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FiniteGaussian
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Scalar coefficients in the verified independent Gaussian tensor basis. -/
def scalarHermiteCoefficient (f : ScalarGaussianL2 ι) (α : ι → ℕ) : ℝ :=
  inner ℝ (tensorHermite α) f

/-- Coefficients of actual Euclidean-valued L² components. -/
def vectorHermiteCoefficient (u : VectorGaussianL2 ι) (i : ι) (α : ι → ℕ) : ℝ :=
  scalarHermiteCoefficient (vectorL2Component i u) α

/-- The scalar output coefficients of Gaussian divergence; cancellation is retained. -/
def divergenceCoefficient (u : VectorGaussianL2 ι) (α : ι → ℕ) : ℝ :=
  ∑ i, if α i = 0 then 0 else
    Real.sqrt (α i : ℝ) * vectorHermiteCoefficient u i (Function.update α i (α i - 1))

/-- The vector output coefficients of Gaussian gradient. -/
def gradientCoefficient (f : ScalarGaussianL2 ι) (i : ι) (α : ι → ℕ) : ℝ :=
  Real.sqrt (α i + 1 : ℝ) * scalarHermiteCoefficient f (Function.update α i (α i + 1))

omit [DecidableEq ι] in
/-- Parseval on the actual scalar Gaussian L² space. -/
theorem scalarHermiteCoefficient_hasSum_sq (f : ScalarGaussianL2 ι) :
    HasSum (fun α => scalarHermiteCoefficient f α ^ 2) (‖f‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (tensorHermiteBasis.repr f)
  simpa [HilbertBasis.repr_apply_apply, tensorHermiteBasis_apply, scalarHermiteCoefficient,
    Real.rpow_two, Real.norm_eq_abs, sq_abs] using h

omit [DecidableEq ι] in
/-- Every square-summable tensor coefficient family is realized by an actual L² class. -/
theorem exists_scalarHermite_coefficients (c : (ι → ℕ) → ℝ)
    (hc : Summable (fun α => c α ^ 2)) :
    ∃ f : ScalarGaussianL2 ι, ∀ α, scalarHermiteCoefficient f α = c α := by
  have hm : Memℓp c 2 := memℓp_gen (by
    simpa [Real.rpow_two, Real.norm_eq_abs, sq_abs] using hc)
  refine ⟨tensorHermiteBasis.repr.symm ⟨c, hm⟩, ?_⟩
  intro α
  change inner ℝ (tensorHermite α) (tensorHermiteBasis.repr.symm ⟨c, hm⟩) = c α
  rw [← tensorHermiteBasis_apply, ← HilbertBasis.repr_apply_apply,
    LinearIsometryEquiv.apply_symm_apply]

omit [DecidableEq ι] in
/-- Completeness makes the actual scalar coefficients unique. -/
theorem scalarHermiteCoefficient_ext {f g : ScalarGaussianL2 ι}
    (h : ∀ α, scalarHermiteCoefficient f α = scalarHermiteCoefficient g α) : f = g := by
  apply tensorHermiteBasis.repr.injective
  ext α
  simpa [HilbertBasis.repr_apply_apply, tensorHermiteBasis_apply,
    scalarHermiteCoefficient] using h α

omit [DecidableEq ι] in
/-- The zero coordinate mode contributes no partial derivative. -/
theorem tensorHermite_gradient_component_zero (α : ι → ℕ) (i : ι) (hi : α i = 0) :
    vectorL2Component i (gradientPolynomialL2 (tensorHermitePolynomial α)) = 0 := by
  rw [gradientPolynomialL2, vectorPolynomialL2_component]
  change productPolynomialL2 (MvPolynomial.pderiv i (tensorHermitePolynomial α)) = 0
  rw [tensorHermitePolynomial_lowering_zero α i hi]
  exact productPolynomialEmbedding.map_zero

/-- Pairing an arbitrary L² field against the genuine gradient of a Hermite tensor
produces precisely the combined divergence coefficient. -/
theorem tensorHermite_gradient_pairing (u : VectorGaussianL2 ι) (α : ι → ℕ) :
    inner ℝ (gradientPolynomialL2 (tensorHermitePolynomial α)) u =
      divergenceCoefficient u α := by
  rw [real_inner_comm]; unfold gradientPolynomialL2; rw [vectorPolynomialL2_inner]
  change (∑ i, inner ℝ (vectorL2Component i u)
    (productPolynomialL2 (MvPolynomial.pderiv i (tensorHermitePolynomial α)))) = _
  unfold divergenceCoefficient
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : α i = 0
  · rw [tensorHermitePolynomial_lowering_zero α i hi]
    have hz : productPolynomialL2 (0 : MvPolynomial ι ℝ) = 0 :=
      productPolynomialEmbedding.map_zero
    simp [hi, hz]
  · have he : α i = (α i - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi)).symm
    rw [tensorHermitePolynomial_lowering α i (α i - 1) he]
    change inner ℝ (vectorL2Component i u)
      (productPolynomialEmbedding (Real.sqrt (((α i - 1 : ℕ) : ℝ) + 1) •
        tensorHermitePolynomial (Function.update α i (α i - 1)))) = _
    rw [map_smul]
    change inner ℝ (vectorL2Component i u)
      (Real.sqrt (((α i - 1 : ℕ) : ℝ) + 1) • productPolynomialL2
        (tensorHermitePolynomial (Function.update α i (α i - 1)))) = _
    rw [tensorHermitePolynomial_L2, real_inner_smul_right, real_inner_comm]
    simp only [hi, ↓reduceIte, vectorHermiteCoefficient, scalarHermiteCoefficient]
    rw [← Nat.cast_add_one, ← he]

/-- Necessity follows by testing the actual adjoint on the polynomial Hermite core. -/
theorem gradient_adjoint_coefficients {u : VectorGaussianL2 ι} {g : ScalarGaussianL2 ι}
    (h : (u, g) ∈ polynomialGradient.adjoint.graph) (α : ι → ℕ) :
    scalarHermiteCoefficient g α = divergenceCoefficient u α := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint polynomialGradient_dense_domain] at h
  have hh := (Submodule.mem_adjoint_iff _ _).mp h _ _ (tensorHermite_gradient_graph α)
  rw [tensorHermite_gradient_pairing, sub_eq_zero] at hh
  exact hh.symm

/-- Sufficiency is proved on the whole polynomial domain by algebraic Hermite spanning;
no adjoint-domain or graph-density hypothesis is imposed. -/
theorem gradient_adjoint_graph_of_coefficients (u : VectorGaussianL2 ι)
    (g : ScalarGaussianL2 ι)
    (h : ∀ α, scalarHermiteCoefficient g α = divergenceCoefficient u α) :
    (u, g) ∈ polynomialGradient.adjoint.graph := by
  let L : MvPolynomial ι ℝ →ₗ[ℝ] ℝ :=
    (innerSL ℝ u).toLinearMap.comp (vectorPolynomialEmbedding.comp gradientPolynomial) -
      (innerSL ℝ g).toLinearMap.comp productPolynomialEmbedding
  have hs : Submodule.span ℝ (Set.range (tensorHermitePolynomial (ι := ι))) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨α, rfl⟩
    change inner ℝ u (gradientPolynomialL2 (tensorHermitePolynomial α)) -
      inner ℝ g (productPolynomialL2 (tensorHermitePolynomial α)) = 0
    rw [tensorHermitePolynomial_L2,
      real_inner_comm (gradientPolynomialL2 (tensorHermitePolynomial α)) u,
      real_inner_comm (tensorHermite α) g,
      tensorHermite_gradient_pairing]
    exact sub_eq_zero.mpr (h α).symm
  rw [tensorHermitePolynomial_span] at hs
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint polynomialGradient_dense_domain]
  apply (Submodule.mem_adjoint_iff _ _).mpr
  intro a b hab
  rw [polynomialGradient_graph] at hab
  obtain ⟨p, hp⟩ := hab
  have ha : productPolynomialL2 p = a := congrArg Prod.fst hp
  have hb : gradientPolynomialL2 p = b := congrArg Prod.snd hp
  rw [← ha, ← hb]
  have hh := hs (Submodule.mem_top (x := p))
  change inner ℝ u (gradientPolynomialL2 p) - inner ℝ g (productPolynomialL2 p) = 0 at hh
  simpa only [real_inner_comm (gradientPolynomialL2 p) u,
    real_inner_comm (productPolynomialL2 p) g] using hh

/-- Exact spectral graph of the full divergence adjoint ∇₀*. -/
theorem gradient_adjoint_graph_iff (u : VectorGaussianL2 ι) (g : ScalarGaussianL2 ι) :
    (u, g) ∈ polynomialGradient.adjoint.graph ↔
      ∀ α, scalarHermiteCoefficient g α = divergenceCoefficient u α :=
  ⟨gradient_adjoint_coefficients, gradient_adjoint_graph_of_coefficients u g⟩

/-- The full adjoint domain requires only square summability of the combined coefficients. -/
theorem gradient_adjoint_domain_iff (u : VectorGaussianL2 ι) :
    u ∈ polynomialGradient.adjoint.domain ↔
      Summable (fun α => divergenceCoefficient u α ^ 2) := by
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨g, hg⟩
    have he := gradient_adjoint_coefficients hg
    simpa only [he] using (scalarHermiteCoefficient_hasSum_sq g).summable
  · intro hu
    obtain ⟨g, hg⟩ := exists_scalarHermite_coefficients _ hu
    exact ⟨g, gradient_adjoint_graph_of_coefficients u g hg⟩

/-- The output norm is the square sum of the combined coefficients. -/
theorem gradient_adjoint_norm_sq (u : VectorGaussianL2 ι) (g : ScalarGaussianL2 ι)
    (h : (u, g) ∈ polynomialGradient.adjoint.graph) :
    ‖g‖ ^ 2 = ∑' α, divergenceCoefficient u α ^ 2 := by
  rw [← (scalarHermiteCoefficient_hasSum_sq g).tsum_eq]
  exact tsum_congr (fun α => by rw [gradient_adjoint_coefficients h α])

omit [DecidableEq ι] in
/-- The same full spectral graph describes the adjoint of the closed gradient. -/
theorem closedGradient_adjoint_eq :
    (closedGradient (ι := ι)).adjoint = polynomialGradient.adjoint :=
  operatorClosure_adjoint_eq polynomialGradient_isClosable polynomialGradient_dense_domain

/-- Existing closed polynomial divergence has these coefficients, without asserting equality
of its domain with the maximal adjoint domain. -/
theorem closedVectorDivergence_coefficients {u : VectorGaussianL2 ι} {g : ScalarGaussianL2 ι}
    (h : (u, g) ∈ closedVectorDivergence.graph) (α : ι → ℕ) :
    scalarHermiteCoefficient g α = divergenceCoefficient u α :=
  gradient_adjoint_coefficients
    (LinearPMap.le_graph_of_le closedVectorDivergence_le_gradient_adjoint h) α

/-- Every genuine polynomial divergence has the same combined spectral coefficients. -/
theorem polynomialDivergence_coefficients (u : ι → MvPolynomial ι ℝ) (α : ι → ℕ) :
    scalarHermiteCoefficient (productPolynomialL2 (divergencePolynomial u)) α =
      divergenceCoefficient (vectorPolynomialL2 u) α :=
  gradient_adjoint_coefficients
    (LinearPMap.le_graph_of_le polynomialDivergence_le_gradient_adjoint
      (polynomialDivergence_polynomial_graph u)) α

/-- No coordinates means every divergence coefficient is zero. -/
theorem divergenceCoefficient_empty [IsEmpty ι] (u : VectorGaussianL2 ι) (α : ι → ℕ) :
    divergenceCoefficient u α = 0 := by
  simp [divergenceCoefficient]

omit [DecidableEq ι] in
/-- Dimension zero has the full vector L² adjoint domain. -/
theorem gradient_adjoint_domain_empty [IsEmpty ι] (u : VectorGaussianL2 ι) :
    u ∈ polynomialGradient.adjoint.domain := by
  classical
  rw [gradient_adjoint_domain_iff]
  simp only [divergenceCoefficient_empty, zero_pow (by decide : 2 ≠ 0)]
  exact summable_zero

omit [DecidableEq ι] in
/-- The actual zero-dimensional adjoint output is zero, not a prescribed derivative value. -/
theorem gradient_adjoint_graph_empty [IsEmpty ι] (u : VectorGaussianL2 ι) :
    (u, (0 : ScalarGaussianL2 ι)) ∈ polynomialGradient.adjoint.graph := by
  classical
  apply gradient_adjoint_graph_of_coefficients
  intro α
  simp [scalarHermiteCoefficient, divergenceCoefficient_empty]

end OperatorDerivativeRewrite.Foundation.FiniteGaussian
