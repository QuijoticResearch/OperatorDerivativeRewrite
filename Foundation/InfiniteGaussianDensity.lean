import Foundation.InfiniteGaussianPolynomials
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.PiSystem

/-! Density of actual polynomial cylinders in the full countable Gaussian L² space. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.InfiniteGaussian
set_option backward.isDefEq.respectTransparency false

/-- Vanishing integrals on finite measurable cylinders determine an integrable function.
The measurable-cylinder π-system generates the entire product sigma-algebra. -/
theorem ae_zero_of_cylinder_integrals (f : SampleSpace → ℝ) (hi : Integrable f gaussianProduct)
    (hc : ∀ (s : Finset ℕ) (S : Set (s → ℝ)), MeasurableSet S →
      (∫ ω in cylinder s S, f ω ∂gaussianProduct) = 0) : f =ᵐ[gaussianProduct] 0 := by
  have hu : (∫ ω, f ω ∂gaussianProduct) = 0 := by
    simpa [cylinder] using hc ∅ Set.univ MeasurableSet.univ
  have hall : ∀ A : Set SampleSpace, MeasurableSet A →
      (∫ ω in A, f ω ∂gaussianProduct) = 0 := by
    refine MeasurableSpace.induction_on_inter
      (C := fun A _ => (∫ ω in A, f ω ∂gaussianProduct) = 0)
      (generateFrom_measurableCylinders (α := fun _ : ℕ => ℝ)).symm
      isPiSystem_measurableCylinders (by simp) ?_ ?_ ?_
    · intro A hA
      obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders A).mp hA
      exact hc s S hS
    · intro A hA hz
      rw [setIntegral_compl hA hi, hu, hz, sub_self]
    · intro A hd hm hz
      rw [integral_iUnion hm hd hi.integrableOn]
      simp only [hz, tsum_zero]
  exact hi.ae_eq_zero_of_forall_setIntegral_eq_zero (fun A hA _ => hall A hA)

/-- Orthogonality to polynomial cylinders implies orthogonality to every actual
finite-coordinate L² class, by the verified finite-dimensional polynomial density theorem. -/
theorem orthogonal_finitePullback (f : GaussianL2)
    (hf : ∀ p : MvPolynomial ℕ ℝ, inner ℝ f (coordinatePolynomialL2 p) = 0)
    (s : Finset ℕ) (g : FiniteGaussian.ScalarGaussianL2 s) :
    inner ℝ f (finitePullback s g) = 0 := by
  have he : (fun g : FiniteGaussian.ScalarGaussianL2 s => inner ℝ f (finitePullback s g)) =
      fun _ => (0 : ℝ) := by
    apply Continuous.ext_on FiniteGaussian.productPolynomialEmbedding_dense
      (continuous_const.inner (finitePullback s).continuous) continuous_const
    rintro g ⟨p, rfl⟩
    change inner ℝ f (polynomialCylinderEmbedding s p) = 0
    rw [← coordinatePolynomialL2_rename]
    exact hf _
  exact congrFun he g

/-- All finite measurable-cylinder integrals of an orthogonal function vanish. -/
theorem orthogonal_cylinder_integral (f : GaussianL2)
    (hf : ∀ p : MvPolynomial ℕ ℝ, inner ℝ f (coordinatePolynomialL2 p) = 0)
    (s : Finset ℕ) (S : Set (s → ℝ)) (hS : MeasurableSet S) :
    (∫ ω in cylinder s S, f ω ∂gaussianProduct) = 0 := by
  have hz := orthogonal_finitePullback f hf s
    (indicatorConstLp 2 hS (measure_ne_top _ _) (1 : ℝ))
  change inner ℝ f (Lp.compMeasurePreserving (finiteProjection s)
    (finiteProjection_measurePreserving s) (indicatorConstLp 2 hS _ (1 : ℝ))) = 0 at hz
  rw [Lp.indicatorConstLp_compMeasurePreserving, real_inner_comm,
    L2.inner_indicatorConstLp_one] at hz
  exact hz

/-- The only L² function orthogonal to every polynomial cylinder is zero. -/
theorem eq_zero_of_coordinatePolynomial_orthogonal (f : GaussianL2)
    (hf : ∀ p : MvPolynomial ℕ ℝ, inner ℝ f (coordinatePolynomialL2 p) = 0) : f = 0 := by
  have hi : Integrable f gaussianProduct := (Lp.memLp f).integrable (by simp)
  have he := ae_zero_of_cylinder_integrals f hi (orthogonal_cylinder_integral f hf)
  apply Lp.ext
  exact he.trans (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := gaussianProduct)).symm

/-- Genuine polynomial cylinders are dense in the entire product L² space. -/
theorem coordinatePolynomialEmbedding_dense :
    Dense (coordinatePolynomialEmbedding.range : Set GaussianL2) := by
  have hbot : coordinatePolynomialEmbedding.range.topologicalClosureᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro f hf
    apply eq_zero_of_coordinatePolynomial_orthogonal f
    intro p
    exact coordinatePolynomialEmbedding.range.topologicalClosure.inner_left_of_mem_orthogonal
      (coordinatePolynomialEmbedding.range.le_topologicalClosure ⟨p, rfl⟩) hf
  have htop := Submodule.orthogonal_eq_bot_iff.mp hbot
  rw [dense_iff_closure_eq]
  change (coordinatePolynomialEmbedding.range.topologicalClosure : Set GaussianL2) = Set.univ
  rw [htop]
  rfl

/-- Equivalently, the actual union of finite-coordinate polynomial spaces is dense. -/
theorem polynomialCylinders_dense :
    Dense (⋃ s : Finset ℕ, ((polynomialCylinderEmbedding s).range : Set GaussianL2)) := by
  rw [← coordinatePolynomialEmbedding_range]
  exact coordinatePolynomialEmbedding_dense

/-- Approximation of every full-product L² random variable by one finite polynomial cylinder. -/
theorem exists_polynomialCylinder_approx (f : GaussianL2) (ε : ℝ) (hε : 0 < ε) :
    ∃ (s : Finset ℕ) (p : MvPolynomial s ℝ), ‖f - polynomialCylinderEmbedding s p‖ < ε := by
  obtain ⟨g, hg, he⟩ := Metric.mem_closure_iff.mp (polynomialCylinders_dense f) ε hε
  obtain ⟨s, p, rfl⟩ := Set.mem_iUnion.mp hg
  exact ⟨s, p, by simpa [dist_eq_norm] using he⟩

end OperatorDerivativeRewrite.Foundation.InfiniteGaussian
