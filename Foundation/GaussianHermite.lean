import Foundation.GaussianAdjoints
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! The actual probabilists' Hermite polynomials, with Gaussian normalization. -/
noncomputable section
open MeasureTheory Polynomial
namespace OperatorDerivativeRewrite.Foundation.GaussianCore
set_option backward.isDefEq.respectTransparency false

/-- Mathlib's integer probabilists' Hermite polynomial, mapped to real coefficients. -/
def hermitePolynomial (n : ℕ) : ℝ[X] :=
  (Polynomial.hermite n).map (Int.castRingHom ℝ)

@[simp] theorem hermitePolynomial_zero : hermitePolynomial 0 = 1 := by
  simp [hermitePolynomial]

/-- The raising recursion is exactly the original polynomial divergence. -/
theorem hermitePolynomial_succ (n : ℕ) :
    hermitePolynomial (n + 1) = divergencePolynomial (hermitePolynomial n) := by
  simp [hermitePolynomial, divergencePolynomial, derivative_map]

/-- The polynomial commutator, proved for the actual differential expression. -/
theorem derivative_divergencePolynomial (p : ℝ[X]) :
    (divergencePolynomial p).derivative = p + divergencePolynomial p.derivative := by
  simp only [divergencePolynomial, derivative_sub, derivative_mul, derivative_X, one_mul]
  ring

/-- The genuine lowering identity H'_{n+1} = (n+1) H_n. -/
theorem hermitePolynomial_derivative (n : ℕ) :
    (hermitePolynomial (n + 1)).derivative = (n + 1 : ℝ) • hermitePolynomial n := by
  induction n with
  | zero => simp [hermitePolynomial_succ, divergencePolynomial]
  | succ n ih =>
    rw [hermitePolynomial_succ, derivative_divergencePolynomial, ih]
    change hermitePolynomial (n + 1) +
      divergenceLinear ((n + 1 : ℝ) • hermitePolynomial n) = _
    rw [map_smul]
    change hermitePolynomial (n + 1) +
      (n + 1 : ℝ) • divergencePolynomial (hermitePolynomial n) = _
    rw [← hermitePolynomial_succ]
    push_cast
    module

/-- Monicity supplies a noncircular algebraic spanning argument. -/
theorem hermitePolynomial_monic (n : ℕ) : (hermitePolynomial n).Monic :=
  (Polynomial.hermite_monic n).map _

theorem hermitePolynomial_degree (n : ℕ) : (hermitePolynomial n).degree = n := by
  rw [hermitePolynomial, (Polynomial.hermite_monic n).degree_map, degree_hermite]

/-- One polynomial of each degree, using Mathlib's polynomial sequence infrastructure. -/
def hermiteSequence : Polynomial.Sequence ℝ where
  elems' := hermitePolynomial
  degree_eq' := hermitePolynomial_degree

/-- Every real polynomial is a finite algebraic Hermite expansion. -/
theorem hermitePolynomial_span :
    Submodule.span ℝ (Set.range hermitePolynomial) = ⊤ :=
  hermiteSequence.span (fun n => by
    change IsUnit (hermitePolynomial n).leadingCoeff
    rw [hermitePolynomial_monic]
    exact isUnit_one)

/-- Unnormalized Hermite vectors in Gaussian L²; integrability was already proved. -/
def hermiteVector (n : ℕ) : GaussianL2 := polynomialL2 (hermitePolynomial n)

private theorem hermite_inner_succ (n m : ℕ) :
    inner ℝ (hermiteVector (n + 1)) (hermiteVector (m + 1)) =
      (m + 1 : ℝ) * inner ℝ (hermiteVector n) (hermiteVector m) := by
  have h := polynomialL2_integration_by_parts
    (hermitePolynomial (m + 1)) (hermitePolynomial n)
  rw [hermitePolynomial_derivative, ← hermitePolynomial_succ] at h
  change inner ℝ (polynomialEmbedding ((m + 1 : ℝ) • hermitePolynomial m))
    (hermiteVector n) = inner ℝ (hermiteVector (m + 1)) (hermiteVector (n + 1)) at h
  rw [map_smul, real_inner_smul_left] at h
  change (m + 1 : ℝ) * inner ℝ (hermiteVector m) (hermiteVector n) =
    inner ℝ (hermiteVector (m + 1)) (hermiteVector (n + 1)) at h
  calc
    _ = inner ℝ (hermiteVector (m + 1)) (hermiteVector (n + 1)) := real_inner_comm _ _
    _ = _ := h.symm
    _ = _ := congrArg ((m + 1 : ℝ) * ·) (real_inner_comm _ _)

private theorem hermite_inner_succ_zero (n : ℕ) :
    inner ℝ (hermiteVector (n + 1)) (hermiteVector 0) = 0 := by
  have h := polynomialL2_integration_by_parts 1 (hermitePolynomial n)
  rw [← hermitePolynomial_succ] at h
  simpa [hermiteVector, hermitePolynomial_zero, polynomialL2,
    real_inner_comm] using h.symm

/-- Orthogonality and the exact squared norm ∫ H_n² dγ = n!. -/
theorem hermiteVector_inner (n m : ℕ) :
    inner ℝ (hermiteVector n) (hermiteVector m) =
      if n = m then (n.factorial : ℝ) else 0 := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero =>
      change inner ℝ (polynomialL2 (hermitePolynomial 0)) (polynomialL2 (hermitePolynomial 0)) = _
      rw [polynomialL2_inner]
      simp
    | succ m =>
      rw [real_inner_comm, hermite_inner_succ_zero]
      simp
  | succ n ih =>
    cases m with
    | zero => rw [hermite_inner_succ_zero]; simp
    | succ m =>
      rw [hermite_inner_succ, ih]
      by_cases h : n = m
      · subst m; simp [Nat.factorial_succ]
      · simp [h]

/-- H_n / √(n!), as an actual equivalence class in Gaussian L². -/
def normalizedHermite (n : ℕ) : GaussianL2 :=
  (Real.sqrt (n.factorial : ℝ))⁻¹ • hermiteVector n

/-- The normalization uses strictly positive Gaussian squared norms. -/
theorem hermite_normalizer_pos (n : ℕ) : 0 < Real.sqrt (n.factorial : ℝ) :=
  Real.sqrt_pos.2 (by exact_mod_cast Nat.factorial_pos n)

/-- The normalized Gaussian Hermite family is orthonormal. -/
theorem normalizedHermite_orthonormal : Orthonormal ℝ normalizedHermite := by
  rw [orthonormal_iff_ite]
  intro n m
  simp only [normalizedHermite, real_inner_smul_left, real_inner_smul_right,
    hermiteVector_inner]
  by_cases h : n = m
  · subst m
    simp only [ite_true]
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ n.factorial by positivity)
    have hn := ne_of_gt (hermite_normalizer_pos n)
    field_simp
    nlinarith
  · simp [h]

/-- The unnormalized Hermite span is exactly the original polynomial core. -/
theorem hermiteVector_span :
    Submodule.span ℝ (Set.range hermiteVector) = polynomialEmbedding.range := by
  have h : Set.range hermiteVector = polynomialEmbedding '' Set.range hermitePolynomial := by
    ext f; simp only [Set.mem_range, Set.mem_image]; constructor
    · rintro ⟨n, rfl⟩; exact ⟨hermitePolynomial n, ⟨n, rfl⟩, rfl⟩
    · rintro ⟨p, ⟨n, rfl⟩, rfl⟩; exact ⟨n, rfl⟩
  rw [h, Submodule.span_image, hermitePolynomial_span, Submodule.map_top]

/-- Normalization does not change the algebraic core. -/
theorem normalizedHermite_span :
    Submodule.span ℝ (Set.range normalizedHermite) = polynomialEmbedding.range := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨n, rfl⟩
    exact polynomialEmbedding.range.smul_mem _ ⟨hermitePolynomial n, rfl⟩
  · rw [← hermiteVector_span]
    apply Submodule.span_le.mpr
    rintro f ⟨n, rfl⟩
    have h : Real.sqrt (n.factorial : ℝ) • normalizedHermite n = hermiteVector n := by
      rw [normalizedHermite, smul_smul,
        mul_inv_cancel₀ (ne_of_gt (hermite_normalizer_pos n)), one_smul]
    rw [← h]
    exact (Submodule.span ℝ (Set.range normalizedHermite)).smul_mem _
      (Submodule.subset_span ⟨n, rfl⟩)

/-- Completeness follows from the already independently proved polynomial density. -/
theorem normalizedHermite_dense_span :
    Dense (Submodule.span ℝ (Set.range normalizedHermite) : Set GaussianL2) := by
  rw [normalizedHermite_span]
  exact polynomialEmbedding_dense

/-- The complete normalized Hermite Hilbert basis of Gaussian L². -/
def hermiteBasis : HilbertBasis ℕ ℝ GaussianL2 :=
  HilbertBasis.mk normalizedHermite_orthonormal
    (by
      rw [← eq_top_iff]
      exact Submodule.dense_iff_topologicalClosure_eq_top.mp normalizedHermite_dense_span)

@[simp] theorem hermiteBasis_apply (n : ℕ) : hermiteBasis n = normalizedHermite n := by
  rw [hermiteBasis, HilbertBasis.coe_mk]

/-- Hermite coefficients are actual Hilbert pairings, not independently prescribed data. -/
theorem hermiteBasis_coefficient (f : GaussianL2) (n : ℕ) :
    hermiteBasis.repr f n = inner ℝ (normalizedHermite n) f := by
  rw [HilbertBasis.repr_apply_apply, hermiteBasis_apply]

/-- Every Gaussian L² vector is the unconditionally convergent sum of its Hermite expansion. -/
theorem hermiteBasis_hasSum (f : GaussianL2) :
    HasSum (fun n => (inner ℝ (normalizedHermite n) f) • normalizedHermite n) f := by
  simpa only [hermiteBasis_coefficient, hermiteBasis_apply] using hermiteBasis.hasSum_repr f

/-- The factorial normalizers obey the positive square-root recursion. -/
theorem hermite_normalizer_succ (n : ℕ) :
    Real.sqrt ((n + 1).factorial : ℝ) =
      Real.sqrt (n + 1 : ℝ) * Real.sqrt (n.factorial : ℝ) := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Real.sqrt_mul (by positivity)]

/-- Actual derivative graph action on the normalized Hermite vectors. -/
theorem normalizedHermite_derivative_graph (n : ℕ) :
    (normalizedHermite (n + 1), Real.sqrt (n + 1 : ℝ) • normalizedHermite n) ∈
      polynomialDerivative.graph := by
  have h := polynomialDerivative.graph.smul_mem
    (Real.sqrt ((n + 1).factorial : ℝ))⁻¹
    (polynomialDerivative_polynomial (hermitePolynomial (n + 1)))
  rw [hermitePolynomial_derivative] at h
  change (_, (Real.sqrt ((n + 1).factorial : ℝ))⁻¹ •
    polynomialEmbedding ((n + 1 : ℝ) • hermitePolynomial n)) ∈ _ at h
  rw [map_smul, smul_smul] at h
  have hs : (Real.sqrt ((n + 1).factorial : ℝ))⁻¹ * (n + 1) =
      Real.sqrt (n + 1 : ℝ) * (Real.sqrt (n.factorial : ℝ))⁻¹ := by
    rw [hermite_normalizer_succ]
    have ha : Real.sqrt (n + 1 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
    have hb := ne_of_gt (hermite_normalizer_pos n)
    have hc := Real.sq_sqrt (show (0 : ℝ) ≤ n + 1 by positivity)
    field_simp
    nlinarith
  rw [hs] at h
  change ((Real.sqrt ((n + 1).factorial : ℝ))⁻¹ • hermiteVector (n + 1),
    (Real.sqrt (n + 1 : ℝ) * (Real.sqrt (n.factorial : ℝ))⁻¹) • hermiteVector n) ∈ _ at h
  simpa only [normalizedHermite, smul_smul] using h

/-- The constant Hermite vector has actual derivative zero. -/
theorem normalizedHermite_derivative_zero_graph :
    (normalizedHermite 0, 0) ∈ polynomialDerivative.graph := by
  have h := polynomialDerivative_polynomial 1
  have hz : polynomialL2 (0 : ℝ[X]) = 0 := polynomialEmbedding.map_zero
  rw [derivative_one, hz] at h
  simpa only [normalizedHermite, hermiteVector, hermitePolynomial_zero, Nat.factorial_zero,
    Nat.cast_one, Real.sqrt_one, inv_one, one_smul] using h

/-- Actual divergence graph action: δ₀ e_n = √(n+1) e_{n+1}. -/
theorem normalizedHermite_divergence_graph (n : ℕ) :
    (normalizedHermite n, Real.sqrt (n + 1 : ℝ) • normalizedHermite (n + 1)) ∈
      polynomialDivergence.graph := by
  have hp : (hermiteVector n, hermiteVector (n + 1)) ∈ polynomialDivergence.graph := by
    rw [polynomialDivergence_graph]
    refine ⟨hermitePolynomial n, ?_⟩
    change (polynomialL2 (hermitePolynomial n),
      polynomialL2 (divergencePolynomial (hermitePolynomial n))) = _
    rw [← hermitePolynomial_succ]; rfl
  have h := polynomialDivergence.graph.smul_mem (Real.sqrt (n.factorial : ℝ))⁻¹ hp
  have hs : (Real.sqrt (n.factorial : ℝ))⁻¹ =
      Real.sqrt (n + 1 : ℝ) * (Real.sqrt ((n + 1).factorial : ℝ))⁻¹ := by
    rw [hermite_normalizer_succ]
    have ha : Real.sqrt (n + 1 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
    have hb := ne_of_gt (hermite_normalizer_pos n)
    field_simp
  change ((Real.sqrt (n.factorial : ℝ))⁻¹ • hermiteVector n,
    (Real.sqrt (n.factorial : ℝ))⁻¹ • hermiteVector (n + 1)) ∈ _ at h
  nth_rw 2 [hs] at h
  simpa only [normalizedHermite, smul_smul] using h

end OperatorDerivativeRewrite.Foundation.GaussianCore
