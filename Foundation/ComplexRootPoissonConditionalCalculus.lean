import Foundation.ComplexRootPoissonMarginals

/-! Native conditional expectation calculus on the actual compound-root trajectory law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Preorder Finset
open scoped NNReal BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.ComplexRootPoissonConditionalCalculus
open ComplexRootPoissonTrajectory ComplexRootPoissonSemigroup ComplexRootPoissonKernel

abbrev past (n : ℕ) : MeasurableSpace Sample :=
  MeasurableSpace.comap (frestrictLe n : Sample → History n) inferInstance

theorem observable_integrable (a : ℝ) (δ : ℝ≥0) (n : ℕ)
    (f : ComplexRootTransitionOperator.Test) :
    Integrable (fun ω => f (coordinate n ω)) (law a δ) := by
  apply Integrable.of_bound
    (f.continuous.comp (continuous_apply n)).aestronglyMeasurable ‖f‖
  exact Filter.Eventually.of_forall (fun ω => f.norm_coe_le_norm _)

theorem conditional_transition (a : ℝ) (δ : ℝ≥0) (n : ℕ)
    (f : ComplexRootTransitionOperator.Test) :
    (law a δ)[fun ω => f (coordinate (n+1) ω) | past n]
      =ᵐ[law a δ] fun ω => transition a δ f (coordinate n ω) := by
  have he := condExp_ae_eq_integral_condDistrib
    (μ := law a δ) (measurable_frestrictLe n)
    (coordinate_measurable (n+1)).aemeasurable f.continuous.stronglyMeasurable
    (observable_integrable a δ (n+1) f)
  have hk := ae_of_ae_map (measurable_frestrictLe n).aemeasurable
    (conditional_next a δ n)
  filter_upwards [he, hk] with ω he hk
  change _ = transition a δ f (coordinate n ω)
  rw [he, hk, historyKernel_apply, kernel_integral]
  rfl

end OperatorDerivativeRewrite.Foundation.ComplexRootPoissonConditionalCalculus
