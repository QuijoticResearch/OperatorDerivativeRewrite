import Foundation.InfiniteGaussianProduct
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! The first Gaussian chaos as a genuine L² series of coordinate random variables.
The series is constructed by Mathlib's orthogonal Hilbert-sum isometry. -/
noncomputable section
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.InfiniteGaussian
set_option backward.isDefEq.respectTransparency false

/-- L² class of the actual nth evaluation random variable. -/
def coordinateL2 (n : ℕ) : GaussianL2 :=
  (coordinate_memLp n 2 (by simp)).toLp (coordinate n)

theorem coordinateL2_coeFn (n : ℕ) :
    coordinateL2 n =ᵐ[gaussianProduct] coordinate n :=
  (coordinate_memLp n 2 (by simp)).coeFn_toLp

/-- Every coordinate is centered. -/
theorem coordinate_integral (n : ℕ) : ∫ ω, coordinate n ω ∂gaussianProduct = 0 := by
  have h := integral_map (μ := gaussianProduct)
    (coordinate_measurePreserving n).measurable.aemeasurable
    (f := fun x : ℝ => x) (by fun_prop)
  simpa [coordinate_law, GaussianCore.γ, integral_id_gaussianReal] using h.symm

/-- Coordinate covariance, proved from independence and the one-dimensional Stein identity. -/
theorem coordinate_product_integral (n m : ℕ) :
    (∫ ω, coordinate n ω * coordinate m ω ∂gaussianProduct) = if n = m then 1 else 0 := by
  classical
  by_cases hnm : n = m
  · subst m
    have h := integral_map (μ := gaussianProduct)
      (coordinate_measurePreserving n).measurable.aemeasurable
      (f := fun x : ℝ => x * x) (by fun_prop)
    have hs := GaussianCore.polynomial_stein (Polynomial.X : ℝ[X])
    have hx : (∫ x : ℝ, x * x ∂GaussianCore.γ) = 1 := by simpa using hs
    simpa [coordinate_law, hx] using h.symm
  · rw [ite_eq_right hnm]
    have h := (coordinates_independent.indepFun hnm).integral_fun_mul_eq_mul_integral
      (coordinate_memLp n 2 (by simp)).aestronglyMeasurable
      (coordinate_memLp m 2 (by simp)).aestronglyMeasurable
    simpa [coordinate_integral] using h

/-- The actual evaluation classes form an orthonormal family in L². -/
theorem coordinateL2_orthonormal : Orthonormal ℝ coordinateL2 := by
  rw [orthonormal_iff_ite]
  intro n m
  rw [L2.inner_def]
  calc
    (∫ ω, inner ℝ (coordinateL2 n ω) (coordinateL2 m ω) ∂gaussianProduct) =
        ∫ ω, coordinate n ω * coordinate m ω ∂gaussianProduct := by
      apply integral_congr_ae
      filter_upwards [coordinateL2_coeFn n, coordinateL2_coeFn m] with ω hn hm
      simp [hn, hm, mul_comm]
    _ = _ := coordinate_product_integral n m

/-- Square-summable real coefficients, with their Hilbert space structure. -/
abbrev CoefficientSpace := lp (fun _ : ℕ => ℝ) 2

/-- Genuine Hilbert-space extension of finite linear Gaussian cylinders.
Gaussianity of arbitrary infinite series is not asserted in this module. -/
def firstChaosEmbedding : CoefficientSpace →ₗᵢ[ℝ] GaussianL2 :=
  coordinateL2_orthonormal.orthogonalFamily.linearIsometry

/-- Unconditional convergence in L² of the actual weighted coordinate classes. -/
theorem firstChaos_hasSum (h : CoefficientSpace) :
    HasSum (fun n => h n • coordinateL2 n) (firstChaosEmbedding h) := by
  simpa [firstChaosEmbedding, LinearIsometry.toSpanSingleton_apply] using
    coordinateL2_orthonormal.orthogonalFamily.hasSum_linearIsometry h

/-- The extension retains every original coordinate value. -/
theorem firstChaos_single (n : ℕ) (a : ℝ) :
    firstChaosEmbedding (lp.single 2 n a) = a • coordinateL2 n := by
  simp [firstChaosEmbedding, OrthogonalFamily.linearIsometry_apply_single,
    LinearIsometry.toSpanSingleton_apply]

/-- The L² inner product is exactly the coefficient-space inner product. -/
theorem firstChaos_inner (h k : CoefficientSpace) :
    inner ℝ (firstChaosEmbedding h) (firstChaosEmbedding k) = inner ℝ h k :=
  firstChaosEmbedding.inner_map_map h k

/-- There is no loss of norm in the infinite L² extension. -/
theorem firstChaos_norm (h : CoefficientSpace) : ‖firstChaosEmbedding h‖ = ‖h‖ :=
  firstChaosEmbedding.norm_map h

/-- Agreement with every finite linear combination of actual coordinate classes. -/
theorem firstChaos_finiteSum (s : Finset ℕ) (a : ℕ → ℝ) :
    firstChaosEmbedding (∑ n ∈ s, lp.single 2 n (a n)) =
      ∑ n ∈ s, a n • coordinateL2 n := by
  simp only [map_sum, firstChaos_single]

/-- Distinct square-summable coefficient vectors give distinct L² random variables. -/
theorem firstChaos_injective : Function.Injective firstChaosEmbedding :=
  firstChaosEmbedding.injective

end OperatorDerivativeRewrite.Foundation.InfiniteGaussian
