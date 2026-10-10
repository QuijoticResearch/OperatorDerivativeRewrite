import Foundation.FiniteGaussianDomains
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-! Countable product Gaussian probability space and faithful finite-cylinder embeddings.
This module does not assert infinite-dimensional Malliavin operators or cylinder density. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.InfiniteGaussian
set_option backward.isDefEq.respectTransparency false

/-- Sample space of real sequences, with its product measurable space. -/
abbrev SampleSpace := ℕ → ℝ

/-- Countable product of standard Gaussian probability measures. -/
def gaussianProduct : Measure SampleSpace :=
  Measure.infinitePi fun _ : ℕ => GaussianCore.γ

instance gaussianProduct_probability : IsProbabilityMeasure gaussianProduct := by
  unfold gaussianProduct
  infer_instance

/-- Scalar L² on the countable product probability space. -/
abbrev GaussianL2 := Lp ℝ 2 gaussianProduct

/-- Actual evaluation random variable; no independently prescribed coordinate data. -/
def coordinate (n : ℕ) (ω : SampleSpace) : ℝ := ω n

/-- Each coordinate projection preserves the standard Gaussian measure. -/
theorem coordinate_measurePreserving (n : ℕ) :
    MeasurePreserving (coordinate n) gaussianProduct GaussianCore.γ :=
  measurePreserving_eval_infinitePi (fun _ : ℕ => GaussianCore.γ) n

/-- The exact marginal distribution is standard Gaussian. -/
theorem coordinate_law (n : ℕ) :
    gaussianProduct.map (coordinate n) = GaussianCore.γ :=
  (coordinate_measurePreserving n).map_eq

/-- Gaussianity of each actual coordinate random variable. -/
theorem coordinate_hasGaussianLaw (n : ℕ) : HasGaussianLaw (coordinate n) gaussianProduct := by
  have h : HasLaw (coordinate n) GaussianCore.γ gaussianProduct :=
    ⟨(coordinate_measurePreserving n).measurable.aemeasurable, coordinate_law n⟩
  exact h.hasGaussianLaw

/-- All countably many coordinate random variables are jointly independent. -/
theorem coordinates_independent : iIndepFun coordinate gaussianProduct :=
  iIndepFun_infinitePi (X := fun _ : ℕ => (id : ℝ → ℝ)) (by fun_prop)

/-- Every coordinate has all finite Lp moments. -/
theorem coordinate_memLp (n : ℕ) (r : ℝ≥0∞) (hr : r ≠ ∞) :
    MemLp (coordinate n) r gaussianProduct :=
  (memLp_id_gaussianReal' r hr).comp_measurePreserving (coordinate_measurePreserving n)

/-- A finite set of coordinates, with the previously verified product Gaussian law. -/
def finiteProjection (s : Finset ℕ) (ω : SampleSpace) : s → ℝ := s.restrict ω

/-- Finite-dimensional distributions are exactly the verified finite product measures,
including the empty coordinate set. -/
theorem finiteProjection_measurePreserving (s : Finset ℕ) :
    MeasurePreserving (finiteProjection s) gaussianProduct
      (FiniteGaussian.productGaussian s) :=
  ⟨by unfold finiteProjection; fun_prop, Measure.infinitePi_map_restrict _⟩

/-- Isometric linear pullback of the actual finite-dimensional L² classes. -/
def finitePullback (s : Finset ℕ) :
    FiniteGaussian.ScalarGaussianL2 s →ₗᵢ[ℝ] GaussianL2 :=
  Lp.compMeasurePreservingₗᵢ ℝ (finiteProjection s) (finiteProjection_measurePreserving s)

/-- The pullback has its expected almost-everywhere representative. -/
theorem finitePullback_coeFn (s : Finset ℕ) (f : FiniteGaussian.ScalarGaussianL2 s) :
    finitePullback s f =ᵐ[gaussianProduct] fun ω => f (finiteProjection s ω) :=
  Lp.coeFn_compMeasurePreserving f (finiteProjection_measurePreserving s)

/-- Finite marginal pullbacks preserve all Hilbert inner products. -/
theorem finitePullback_inner (s : Finset ℕ) (f g : FiniteGaussian.ScalarGaussianL2 s) :
    inner ℝ (finitePullback s f) (finitePullback s g) = inner ℝ f g :=
  (finitePullback s).inner_map_map f g

/-- Actual finite polynomial cylinder representative. -/
def polynomialCylinder (s : Finset ℕ) (p : MvPolynomial s ℝ) (ω : SampleSpace) : ℝ :=
  MvPolynomial.eval (finiteProjection s ω) p

/-- Polynomial cylinders have every finite moment, by the finite marginal law. -/
theorem polynomialCylinder_memLp (s : Finset ℕ) (p : MvPolynomial s ℝ)
    (r : ℝ≥0∞) (hr : r ≠ ∞) : MemLp (polynomialCylinder s p) r gaussianProduct :=
  (FiniteGaussian.productPolynomial_memLp p r hr).comp_measurePreserving
    (finiteProjection_measurePreserving s)

/-- Linear embedding of genuine polynomial random variables into countable Gaussian L². -/
def polynomialCylinderEmbedding (s : Finset ℕ) : MvPolynomial s ℝ →ₗ[ℝ] GaussianL2 :=
  (finitePullback s).toLinearMap.comp FiniteGaussian.productPolynomialEmbedding

/-- The embedding represents the actual evaluated polynomial almost everywhere. -/
theorem polynomialCylinderEmbedding_coeFn (s : Finset ℕ) (p : MvPolynomial s ℝ) :
    polynomialCylinderEmbedding s p =ᵐ[gaussianProduct] polynomialCylinder s p := by
  have ha := (finiteProjection_measurePreserving s).quasiMeasurePreserving.ae_eq_comp
    (FiniteGaussian.productPolynomialL2_coeFn p)
  filter_upwards [finitePullback_coeFn s (FiniteGaussian.productPolynomialL2 p), ha]
    with ω h₁ h₂
  exact h₁.trans h₂

/-- No nonzero finite polynomial is lost by passing to an almost-everywhere L² class. -/
theorem polynomialCylinderEmbedding_injective (s : Finset ℕ) :
    Function.Injective (polynomialCylinderEmbedding s) :=
  (finitePullback s).injective.comp FiniteGaussian.productPolynomialEmbedding_injective

/-- Every finite Hermite family retains its orthonormality in the countable product. -/
theorem finiteHermite_orthonormal (s : Finset ℕ) :
    Orthonormal ℝ (fun α : s → ℕ => finitePullback s (FiniteGaussian.tensorHermite α)) := by
  rw [orthonormal_iff_ite]
  intro α β
  rw [finitePullback_inner]
  exact orthonormal_iff_ite.mp FiniteGaussian.tensorHermite_orthonormal α β

end OperatorDerivativeRewrite.Foundation.InfiniteGaussian
