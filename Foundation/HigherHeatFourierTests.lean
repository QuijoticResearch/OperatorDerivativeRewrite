import Foundation.HigherHeatComplexObstruction

/-! Fourier cylinder tests retain a grid-independent spectral bound despite supremum-norm failure. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.HigherHeatFourierTests
open SignedDensityIntegral HigherHeatCylinderFourier HigherHeatDyadicLaws

variable {X : Type*} [MeasurableSpace X]

theorem signed_integral_complex_mul (ν : SignedMeasure X) (g : X → ℂ)
    (hg : Measurable g) (C : ℝ) (hb : ∀ x, ‖g x‖ ≤ C) (a : ℂ) :
    (∫ᵛ x, a*g x ∂<•ν)=a*(∫ᵛ x, g x ∂<•ν) := by
  have hmul : Measurable (fun x => a*g x) := measurable_const.mul hg
  have hmb : ∀ x, ‖a*g x‖ ≤ ‖a‖*C := fun x => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)
  conv_lhs => rw [← ν.toSignedMeasure_toJordanDecomposition]
  conv_rhs => rw [← ν.toSignedMeasure_toJordanDecomposition]
  rw [JordanDecomposition.toSignedMeasure]
  rw [VectorMeasure.integral_sub_vectorMeasure
    (bounded_signed_integrable _ _ hmul _ hmb) (bounded_signed_integrable _ _ hmul _ hmb),
    VectorMeasure.integral_sub_vectorMeasure
    (bounded_signed_integrable _ _ hg C hb) (bounded_signed_integrable _ _ hg C hb)]
  simp_rw [VectorMeasure.integral_toSignedMeasure,integral_const_mul]
  ring

variable {ι : Type*} [Fintype ι]

def polynomial (n : ℕ) (a : ι → ℂ) (ξ : ι → Grid n) (y : Grid n) : ℂ :=
  ∑ k, a k*configurationPhase (ξ k) y

theorem polynomial_continuous (n : ℕ) (a : ι → ℂ) (ξ : ι → Grid n) :
    Continuous (polynomial n a ξ) := by
  unfold polynomial configurationPhase
  fun_prop

theorem polynomial_bound (n : ℕ) (a : ι → ℂ) (ξ : ι → Grid n) (y : Grid n) :
    ‖polynomial n a ξ y‖ ≤ ∑ k, ‖a k‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [norm_mul,configurationPhase_norm,mul_one]

theorem polynomial_expectation (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (a : ι → ℂ) (ξ : ι → Grid n) :
    (∫ᵛ y : Grid n, polynomial n a ξ y ∂<•HigherHeatDyadicLaws.law m hm T hT n)=
      ∑ k, a k * ∏ j : Fin (gridSize n), HigherHeatL2.symbol m (duration T n)
        (∑ i ∈ Finset.univ.filter (fun i => j ≤ i), ξ k i) := by
  have hi k : (HigherHeatDyadicLaws.law m hm T hT n).Integrable
      (fun y => a k*configurationPhase (ξ k) y) := by
    apply bounded_signed_integrable _ _
      (measurable_const.mul (configurationPhase_measurable _)) ‖a k‖
    intro y
    change ‖a k*configurationPhase (ξ k) y‖ ≤ ‖a k‖
    rw [norm_mul,configurationPhase_norm,mul_one]
  unfold polynomial
  rw [VectorMeasure.integral_finsetSum _ (fun k _ => hi k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [signed_integral_complex_mul _ _ (configurationPhase_measurable _) 1
    (fun y => by rw [configurationPhase_norm])]
  rw [HigherHeatDyadicLaws.law,positionLaw_fourier]

theorem spectral_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (a : ι → ℂ) (ξ : ι → Grid n) :
    ‖∫ᵛ y : Grid n, polynomial n a ξ y ∂<•HigherHeatDyadicLaws.law m hm T hT n‖ ≤
      ∑ k, ‖a k‖ := by
  rw [polynomial_expectation]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [norm_mul,norm_prod]
  apply mul_le_of_le_one_right (norm_nonneg _)
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => HigherHeatL2.symbol_norm_le _ _ _)

theorem actual_path_test_bound (n : ℕ) (a : ι → ℂ) (ξ : ι → Grid n) :
    Continuous (fun ω : HigherHeatContinuousCylinders.Path =>
      polynomial n a ξ (HigherHeatContinuousCylinders.sample n ω)) ∧
    ∀ ω : HigherHeatContinuousCylinders.Path,
      ‖polynomial n a ξ (HigherHeatContinuousCylinders.sample n ω)‖ ≤ ∑ k, ‖a k‖ :=
  ⟨(polynomial_continuous n a ξ).comp (HigherHeatContinuousCylinders.sample_continuous n),
    fun ω => polynomial_bound n a ξ _⟩

end OperatorDerivativeRewrite.Foundation.HigherHeatFourierTests
