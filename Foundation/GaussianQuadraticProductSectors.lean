import Foundation.GaussianSecondChaosFourthLower
import Foundation.GaussianPureQuadraticProduct
import Mathlib.Data.Fin.VecNotation

/-! Actual orthonormal quadratic cross-products are pure fourth chaos. -/
noncomputable section
open MeasureTheory MvPolynomial
namespace OperatorDerivativeRewrite.Foundation.GaussianQuadraticProductSectors
open InfiniteGaussian FiniteGaussian GaussianNumberSectors GaussianTimeSpaceHermite
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- A finite polynomial number eigenvector gives an actual completed chaos member. -/
theorem orthonormal_polynomial_mem_sector {I : Type*} [Fintype I]
    (h : I → CoefficientSpace) (hh : Orthonormal ℝ h)
    (p : MvPolynomial I ℝ) (n : ℕ)
    (hp : divergencePolynomial (gradientPolynomial p) = (n : ℝ) • p) :
    isonormalCylinderL2 h p ∈ sector n := by
  classical
  apply (mem_sector _ _).mpr
  refine ⟨polynomialDerivative (cylinderCore h p),
    closedCylindricalDerivative_core_graph (cylinderCore h p), ?_⟩
  have hg := cylindricalDivergence_field_graph (fun i => cylinderCore h (pderiv i p)) h
  have he : cylindricalDivergenceExpression (fun i => cylinderCore h (pderiv i p)) h =
      (n : ℝ) • isonormalCylinderL2 h p := by
    change (∑ i, rankDivergence (cylinderCore h (pderiv i p)) (h i)) = _
    simp only [orthonormal_rankDivergence h hh]
    change (∑ i, familyPolynomialEmbedding h (coordinateDivergencePolynomial i (pderiv i p))) = _
    rw [← map_sum]
    change familyPolynomialEmbedding h (divergencePolynomial (gradientPolynomial p)) = _
    rw [hp, map_smul]
    rfl
  rw [he, ← cylinder_gradient_expansion] at hg
  exact LinearPMap.le_graph_of_le cylindricalDivergence_le_hilbertDivergence hg

def crossPolynomial : MvPolynomial (Fin 2) ℝ := (X 0 ^ 2 - 1) * (X 1 ^ 2 - 1)

theorem crossPolynomial_number :
    divergencePolynomial (gradientPolynomial crossPolynomial) = (4 : ℝ) • crossPolynomial := by
  have hc2 : (C (2 : ℝ) : MvPolynomial (Fin 2) ℝ) = 2 := by
    convert C_eq_coe_nat (σ := Fin 2) (R := ℝ) 2 using 1
  have hc4 : (C (4 : ℝ) : MvPolynomial (Fin 2) ℝ) = 4 := by
    convert C_eq_coe_nat (σ := Fin 2) (R := ℝ) 4 using 1
  have hd (i : Fin 2) : pderiv i (2 : MvPolynomial (Fin 2) ℝ) = 0 := by
    rw [← hc2]; exact pderiv_C
  simp [divergencePolynomial, gradientPolynomial, coordinateDivergencePolynomial,
    crossPolynomial, Fin.sum_univ_two, Algebra.smul_def, hd, hc4]
  ring

theorem orthonormal_wick_product_eq_cylinder (h : Fin 2 → CoefficientSpace)
    (hh : Orthonormal ℝ h) :
    (polynomialProduct (wick (h 0) 2) (wick (h 1) 2) : GaussianL2) =
      isonormalCylinderL2 h crossPolynomial := by
  apply Lp.ext
  filter_upwards [polynomialProductL2_coeFn (wick (h 0) 2) (wick (h 1) 2),
    core_coeFn (h 0) (‖h 0‖^2) 2, core_coeFn (h 1) (‖h 1‖^2) 2,
    isonormalCylinderL2_coeFn h crossPolynomial] with ω hp h0 h1 hc
  change polynomialProductL2 (wick (h 0) 2) (wick (h 1) 2) ω = _
  rw [hp, hc]
  change (core (h 0) (‖h 0‖^2) 2 : GaussianL2) ω *
    (core (h 1) (‖h 1‖^2) 2 : GaussianL2) ω = _
  rw [h0, h1]
  simp [isonormalCylinder, crossPolynomial, value_two, hh.norm_eq_one]

theorem orthonormal_wick_product_mem_four (h : Fin 2 → CoefficientSpace)
    (hh : Orthonormal ℝ h) :
    (polynomialProduct (wick (h 0) 2) (wick (h 1) 2) : GaussianL2) ∈ sector 4 := by
  rw [orthonormal_wick_product_eq_cylinder h hh]
  exact orthonormal_polynomial_mem_sector h hh crossPolynomial 4 crossPolynomial_number

end OperatorDerivativeRewrite.Foundation.GaussianQuadraticProductSectors
