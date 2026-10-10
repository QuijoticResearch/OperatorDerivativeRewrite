import Foundation.GaussianHermiteDomains
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Finite-dimensional isonormal coordinates, including correlated and dependent families. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.FiniteGaussian
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The existing basis-independent standard Gaussian on the finite-dimensional Hilbert space. -/
abbrev gaussianMeasure (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] : Measure E := stdGaussian E

/-- The actual linear Gaussian coordinate W(h)(x)=⟨h,x⟩. -/
def coordinate (h : E) : E →L[ℝ] ℝ := innerSL ℝ h

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem coordinate_apply (h x : E) : coordinate h x = inner ℝ h x := rfl

/-- Standard Gaussian has full support; this is proved from its product-coordinate construction. -/
instance gaussianMeasure_openPos : (gaussianMeasure E).IsOpenPosMeasure := by
  have : (gaussianReal 0 1).IsOpenPosMeasure :=
    (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : NNReal) ≠ 0)).isOpenPosMeasure
  let b := stdOrthonormalBasis ℝ E
  rw [gaussianMeasure, stdGaussian_eq_map_pi_orthonormalBasis b]
  apply Continuous.isOpenPosMeasure_map (by fun_prop)
  intro x
  exact ⟨fun i => b.repr x i, b.sum_repr x⟩

/-- Continuous representatives equal a.e. under the ambient Gaussian agree everywhere. -/
theorem continuous_ae_eq {f g : E → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : f =ᵐ[gaussianMeasure E] g) : f = g :=
  Measure.eq_of_ae_eq h hf hg

/-- Every coordinate has all finite Lp moments, including the zero coordinate. -/
theorem coordinate_memLp (h : E) (r : ℝ≥0∞) (hr : r ≠ ∞) :
    MemLp (coordinate h) r (gaussianMeasure E) :=
  IsGaussian.memLp_dual _ (coordinate h) r hr

/-- The exact Gaussian marginal, allowing variance zero for h=0. -/
theorem coordinate_gaussian_law (h : E) :
    (gaussianMeasure E).map (coordinate h) =
      gaussianReal 0 (⟨‖h‖ ^ 2, sq_nonneg ‖h‖⟩ : NNReal) := by
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian]
  congr 1
  apply NNReal.eq
  simp [coordinate, innerSL_apply_norm]
  rfl

/-- Isonormal covariance; it imposes no orthogonality or linear independence on h and k. -/
theorem coordinate_covariance (h k : E) :
    cov[coordinate h, coordinate k; gaussianMeasure E] = inner ℝ h k := by
  change cov[fun x => inner ℝ h x, fun x => inner ℝ k x; stdGaussian E] = _
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian, innerSL_apply_apply]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The coordinate map respects genuine linear relations pointwise. -/
theorem coordinate_add (h k : E) : coordinate (h + k) = coordinate h + coordinate k := by
  ext x; simp [coordinate]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem coordinate_smul (a : ℝ) (h : E) : coordinate (a • h) = a • coordinate h := by
  ext x; simp [coordinate]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A vanishing finite linear combination gives a vanishing random-variable combination. -/
theorem coordinate_linear_relation {ι : Type*} [Fintype ι] (h : ι → E) (a : ι → ℝ)
    (ha : ∑ i, a i • h i = 0) (x : E) : ∑ i, a i * coordinate (h i) x = 0 := by
  have ht := congrArg (fun v => inner ℝ v x) ha
  simpa [sum_inner, real_inner_smul_left] using ht

/-- Independent-coordinate realization through any orthonormal basis, not just the chosen one. -/
theorem gaussianMeasure_eq_product_map {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) :
    gaussianMeasure E = (Measure.pi fun _ : ι => GaussianCore.γ).map
      (fun x => ∑ i, x i • b i) :=
  stdGaussian_eq_map_pi_orthonormalBasis b

/-- A finite coordinate family is an actual continuous linear Gaussian map. -/
def coordinateFamily {ι : Type*} [Fintype ι] (h : ι → E) : E →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun i => coordinate (h i)

/-- Its joint law is Gaussian without any rank, orthogonality, or nondegeneracy assumption. -/
instance coordinateFamily_isGaussian {ι : Type*} [Fintype ι] (h : ι → E) :
    IsGaussian ((gaussianMeasure E).map (coordinateFamily h)) := inferInstance

/-- Orthonormal coordinates have exactly the independent product law.
This conclusion is not asserted for an arbitrary correlated coordinate family. -/
theorem orthonormal_coordinates_joint_law {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) :
    (gaussianMeasure E).map (coordinateFamily b) = Measure.pi fun _ : ι => GaussianCore.γ := by
  classical
  rw [gaussianMeasure_eq_product_map b, Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (coordinateFamily b ∘ (fun x : ι → ℝ => ∑ i, x i • b i)) = id := by
    funext x
    ext j
    simp [coordinateFamily, coordinate, inner_sum, inner_smul_right,
      orthonormal_iff_ite.mp b.orthonormal]
  rw [he, Measure.map_id]

end OperatorDerivativeRewrite.Foundation.FiniteGaussian
