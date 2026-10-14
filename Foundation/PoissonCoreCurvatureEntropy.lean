import Foundation.PoissonCoreEntropyObstruction
import Foundation.PoissonDivergenceRecovery

/-! On the actual finite-support core, integrated generator Gamma equals
source energy, so positive pointwise curvature coexists with entropy failure. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.PoissonCoreCurvatureEntropy
open PoissonDifferenceCore PoissonDifferenceOperators PoissonMaximalOperators PoissonJumpCurvature

theorem finite_generator_eq_neg_number (rate : ℝ≥0) (f : ℕ →₀ ℝ) (n : ℕ) :
    jumpGenerator rate f n=-(finsuppDivergence rate (finsuppDifference f)) n := by
  cases n <;> simp [jumpGenerator,jumpGradient,finsuppDivergence_apply,poissonDivergenceExpr,
    backwardWeighted,finsuppDifference_apply,Nat.cast_add,Nat.cast_one] <;> ring

theorem finite_generator_integrable (rate : ℝ≥0) (f : ℕ →₀ ℝ) :
    Integrable (jumpGenerator rate f) (poissonLaw rate) := by
  change Integrable (fun n => jumpGenerator rate f n) (poissonLaw rate)
  simp_rw [finite_generator_eq_neg_number]
  exact (integrable_of_finite_support rate _ (finsuppDivergence rate (finsuppDifference f)).hasFiniteSupport).neg

theorem finite_generator_integral_zero (rate : ℝ≥0) (hr : 0<rate) (f : ℕ →₀ ℝ) :
    (∫ n, jumpGenerator rate f n ∂poissonLaw rate)=0 := by
  have hδ := coreDivergence_finsupp_graph rate hr (finsuppDifference f)
  have hz := (PoissonDivergenceRecovery.exists_divergence_iff_centered rate hr
    (scalarFinsupp rate (finsuppDivergence rate (finsuppDifference f)))).mp
      ⟨fieldFinsupp rate (finsuppDifference f),LinearPMap.le_graph_of_le (coreDivergence_le_maximal rate hr) hδ⟩
  rw [integral_congr_ae (scalarFinsupp_coeFn rate (finsuppDivergence rate (finsuppDifference f)))] at hz
  simp_rw [finite_generator_eq_neg_number]
  rw [integral_neg,hz,neg_zero]

theorem finite_gamma_decomposition (rate : ℝ≥0) (f : ℕ →₀ ℝ) (n : ℕ) :
    gamma rate f n=(1/2 : ℝ)*jumpGenerator rate ((f*f : ℕ →₀ ℝ) : ℕ → ℝ) n+
      f n*(finsuppDivergence rate (finsuppDifference f)) n := by
  have hm : (f*f : ℕ →₀ ℝ)=(fun k => f k*f k : ℕ → ℝ) := by
    funext k; simp
  unfold gamma carre
  change (1/2 : ℝ)*(jumpGenerator rate (fun k => f k*f k) n-
    f n*jumpGenerator rate f n-f n*jumpGenerator rate f n) = _
  rw [← hm,finite_generator_eq_neg_number rate f n]
  ring

theorem finite_gamma_integrable (rate : ℝ≥0) (f : ℕ →₀ ℝ) :
    Integrable (gamma rate f) (poissonLaw rate) := by
  change Integrable (fun n => gamma rate f n) (poissonLaw rate)
  simp_rw [finite_gamma_decomposition]
  exact ((finite_generator_integrable rate (f*f)).const_mul (1/2)).add
    (integrable_of_finite_support rate _ (pairing_hasFiniteSupport f _))

theorem finite_gamma_integral_source_energy (rate : ℝ≥0) (hr : 0<rate) (f : ℕ →₀ ℝ) :
    (∫ n, gamma rate f n ∂poissonLaw rate)=‖fieldFinsupp rate (finsuppDifference f)‖^2 := by
  simp_rw [finite_gamma_decomposition]
  rw [integral_add ((finite_generator_integrable rate (f*f)).const_mul (1/2))
    (integrable_of_finite_support rate _ (pairing_hasFiniteSupport f _)),integral_const_mul,
    finite_generator_integral_zero rate hr (f*f),mul_zero,zero_add,
    ← real_inner_self_eq_norm_sq,fieldFinsupp_inner]
  have he := poisson_difference_ibp_finsupp rate f (finsuppDifference f)
  simpa only [finsuppDifference_apply,finsuppDivergence_apply,forwardDifference] using he.symm

theorem positive_curvature_bounded_core_entropy_failure (rate : ℝ≥0) (hr : 0<rate)
    (C : ℝ) (hC : 0≤C) :
    ∃ f : ℕ →₀ ℝ, Integrable (gamma rate f) (poissonLaw rate) ∧
      (∀ n, (1/2 : ℝ)*gamma rate f n≤gamma2 rate f n) ∧
      C*(∫ n, gamma rate f n ∂poissonLaw rate)<entropySq (poissonLaw rate) f := by
  obtain ⟨f,hf⟩ := PoissonCoreEntropyObstruction.finite_core_entropy_counterexample rate hr C hC
  refine ⟨f,finite_gamma_integrable rate f,fun n => gamma2_half_lower rate f n, ?_⟩
  rw [finite_gamma_integral_source_energy rate hr f]
  exact hf

end OperatorDerivativeRewrite.Foundation.PoissonCoreCurvatureEntropy


