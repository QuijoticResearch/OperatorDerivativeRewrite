import Foundation.FiniteGaussianCylinders
import Mathlib.MeasureTheory.Integral.Pi

/-! Independent finite Gaussian products and their orthonormal tensor Hermite family.
Completeness and multivariate polynomial density are not asserted in this module. -/
noncomputable section
open MeasureTheory Polynomial
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.FiniteGaussian
set_option backward.isDefEq.respectTransparency false

/-- Normalized real polynomial whose Gaussian L² class is the verified Hermite basis vector. -/
def normalizedHermitePolynomial (n : ℕ) : ℝ[X] :=
  (Real.sqrt (n.factorial : ℝ))⁻¹ • GaussianCore.hermitePolynomial n

theorem normalizedHermitePolynomial_L2 (n : ℕ) :
    GaussianCore.polynomialL2 (normalizedHermitePolynomial n) =
      GaussianCore.normalizedHermite n := by
  change GaussianCore.polynomialEmbedding
    ((Real.sqrt (n.factorial : ℝ))⁻¹ • GaussianCore.hermitePolynomial n) = _
  exact GaussianCore.polynomialEmbedding.map_smul _ _

/-- Gaussian integral orthogonality of actual normalized polynomial representatives. -/
theorem normalizedHermitePolynomial_integral (n m : ℕ) :
    (∫ x, (normalizedHermitePolynomial n).eval x *
      (normalizedHermitePolynomial m).eval x ∂GaussianCore.γ) = if n = m then 1 else 0 := by
  rw [← GaussianCore.polynomialL2_inner, normalizedHermitePolynomial_L2,
    normalizedHermitePolynomial_L2]
  exact orthonormal_iff_ite.mp GaussianCore.normalizedHermite_orthonormal n m

variable {ι : Type*} [Fintype ι]

/-- The independent finite product of the verified standard one-dimensional Gaussian. -/
abbrev productGaussian (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ : ι => GaussianCore.γ

/-- Actual tensor polynomial representative for a finite multi-index α. -/
def tensorHermiteFunction (α : ι → ℕ) (x : ι → ℝ) : ℝ :=
  ∏ i, (normalizedHermitePolynomial (α i)).eval (x i)

/-- Partial tensor products have all finite moments; Hölder uses doubled input exponents. -/
theorem tensorHermite_partial_memLp (α : ι → ℕ) (s : Finset ι)
    (r : ℝ≥0∞) (hr : r ≠ ∞) :
    MemLp (fun x : ι → ℝ => ∏ i ∈ s, (normalizedHermitePolynomial (α i)).eval (x i))
      r (productGaussian ι) := by
  classical
  induction s using Finset.induction_on generalizing r with
  | empty =>
    simpa using (memLp_const (1 : ℝ) :
      MemLp (fun _ : ι → ℝ => (1 : ℝ)) r (productGaussian ι))
  | insert i s hi ih =>
    have ht : 2 * r ≠ ∞ := ENNReal.mul_ne_top (by simp) hr
    have : ENNReal.HolderTriple (2 * r) (2 * r) r := doubled_holderTriple r
    have hf0 := GaussianCore.polynomial_memLp (normalizedHermitePolynomial (α i)) (2 * r) ht
    have hf := hf0.comp_measurePreserving
      (measurePreserving_eval (fun _ : ι => GaussianCore.γ) i)
    simpa [Finset.prod_insert, hi, Function.eval] using
      (mul_memLp (p := 2 * r) (q := 2 * r) (r := r) hf (ih (2 * r) ht))

/-- In particular, every tensor Hermite polynomial is genuinely square integrable. -/
theorem tensorHermite_memLp (α : ι → ℕ) (r : ℝ≥0∞) (hr : r ≠ ∞) :
    MemLp (tensorHermiteFunction α) r (productGaussian ι) :=
  tensorHermite_partial_memLp α Finset.univ r hr

/-- Tensor Hermite vectors in the actual product Gaussian L² space. -/
def tensorHermite (α : ι → ℕ) : Lp ℝ 2 (productGaussian ι) :=
  (tensorHermite_memLp α 2 (by simp)).toLp (tensorHermiteFunction α)

theorem tensorHermite_coeFn (α : ι → ℕ) :
    tensorHermite α =ᵐ[productGaussian ι] tensorHermiteFunction α := MemLp.coeFn_toLp _

/-- Independent tensor orthogonality follows from finite-product Fubini and one-dimensional IBP. -/
theorem tensorHermite_inner (α β : ι → ℕ) :
    inner ℝ (tensorHermite α) (tensorHermite β) = if α = β then 1 else 0 := by
  classical
  rw [L2_inner_eq_integral]
  have he : (fun x => inner ℝ (tensorHermite α x) (tensorHermite β x)) =ᵐ[productGaussian ι]
      fun x => ∏ i, ((normalizedHermitePolynomial (α i)).eval (x i) *
        (normalizedHermitePolynomial (β i)).eval (x i)) := by
    filter_upwards [tensorHermite_coeFn α, tensorHermite_coeFn β] with x hα hβ
    rw [hα, hβ, Real.inner_apply]
    exact (Finset.prod_mul_distrib).symm
  rw [integral_congr_ae he, productGaussian]
  rw [integral_fintype_prod_eq_prod (fun i (t : ℝ) =>
    (normalizedHermitePolynomial (α i)).eval t * (normalizedHermitePolynomial (β i)).eval t)]
  simp only [normalizedHermitePolynomial_integral]
  by_cases h : α = β
  · subst β; simp
  · simp only [h, ↓reduceIte]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- An orthonormal family; completeness is a separate, still outstanding density theorem. -/
theorem tensorHermite_orthonormal :
    Orthonormal ℝ (tensorHermite (ι := ι)) := by
  classical
  exact orthonormal_iff_ite.mpr tensorHermite_inner

end OperatorDerivativeRewrite.Foundation.FiniteGaussian
