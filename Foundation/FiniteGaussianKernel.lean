import Foundation.FiniteGaussianDomains

/-! The kernel of the genuine finite-dimensional closed Gaussian gradient.
The proof uses the already verified raising coefficients and tensor completeness,
including the zero-dimensional case. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.FiniteGaussian

variable {ι : Type*} [Fintype ι]

/-- The zero-degree tensor is the actual constant-one Gaussian class. -/
theorem tensorHermite_zero_coeFn :
    tensorHermite (fun _ : ι => 0) =ᵐ[productGaussian ι] fun _ => (1 : ℝ) := by
  filter_upwards [tensorHermite_coeFn (fun _ : ι => 0)] with x hx
  simpa [tensorHermiteFunction, normalizedHermitePolynomial,
    GaussianCore.hermitePolynomial_zero] using hx

/-- Every coefficient of the zero vector-valued Gaussian class is zero. -/
theorem vectorHermiteCoefficient_zero (i : ι) (α : ι → ℕ) :
    vectorHermiteCoefficient (0 : VectorGaussianL2 ι) i α = 0 := by
  have hz : vectorL2Component i (0 : VectorGaussianL2 ι) = 0 := by
    exact ((EuclideanSpace.proj (𝕜 := ℝ) i).compLpₗ 2 (productGaussian ι)).map_zero
  simp only [vectorHermiteCoefficient, hz, scalarHermiteCoefficient, inner_zero_right]

/-- Every nonconstant Hermite coefficient vanishes when the actual closed
gradient vanishes. No pointwise differentiability is assumed here. -/
theorem scalarHermiteCoefficient_zero_of_closedGradient_zero
    {f : ScalarGaussianL2 ι} (h : (f, (0 : VectorGaussianL2 ι)) ∈ closedGradient.graph)
    (α : ι → ℕ) (hα : α ≠ fun _ => 0) : scalarHermiteCoefficient f α = 0 := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hα
  obtain ⟨β, hβ⟩ := (mem_range_hermiteRaise i α).mpr hi
  change Function.update β i (β i + 1) = α at hβ
  have hc := (closedGradient_graph_iff f 0).mp h i β
  rw [vectorHermiteCoefficient_zero, gradientCoefficient, hβ] at hc
  have hw : Real.sqrt (β i + 1 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  exact (mul_eq_zero.mp hc.symm).resolve_left hw

/-- Exact kernel characterization by the vacuum coefficient of the complete
tensor basis. This also applies when the coordinate type is empty. -/
theorem closedGradient_zero_iff_vacuum (f : ScalarGaussianL2 ι) :
    (f, (0 : VectorGaussianL2 ι)) ∈ closedGradient.graph ↔
      f = scalarHermiteCoefficient f (fun _ => 0) • tensorHermite (fun _ : ι => 0) := by
  classical
  constructor
  · intro hf
    apply scalarHermiteCoefficient_ext
    intro α
    by_cases hα : α = fun _ => 0
    · subst α
      rw [scalarHermiteCoefficient, scalarHermiteCoefficient, real_inner_smul_right,
        tensorHermite_inner]
      simp
    · rw [scalarHermiteCoefficient_zero_of_closedGradient_zero hf α hα]
      simp [scalarHermiteCoefficient, real_inner_smul_right, tensorHermite_inner, hα]
  · intro hf
    apply (closedGradient_graph_iff f 0).mpr
    intro i α
    have hn : Function.update α i (α i + 1) ≠ fun _ : ι => 0 := by
      intro he
      have hi := congrFun he i
      simp at hi
    rw [hf]
    simp only [vectorHermiteCoefficient_zero, gradientCoefficient,
      scalarHermiteCoefficient, real_inner_smul_right, tensorHermite_inner,
      ite_eq_right hn, mul_zero]

/-- The kernel of the closed Gaussian gradient is exactly the constant classes. -/
theorem closedGradient_zero_iff_const (f : ScalarGaussianL2 ι) :
    (f, (0 : VectorGaussianL2 ι)) ∈ closedGradient.graph ↔
      ∃ c : ℝ, f = c • tensorHermite (fun _ : ι => 0) := by
  constructor
  · intro hf
    exact ⟨_, (closedGradient_zero_iff_vacuum f).mp hf⟩
  · rintro ⟨c, rfl⟩
    apply (closedGradient_zero_iff_vacuum _).mpr
    rw [scalarHermiteCoefficient, real_inner_smul_right, tensorHermite_inner]
    simp

end OperatorDerivativeRewrite.Foundation.FiniteGaussian
