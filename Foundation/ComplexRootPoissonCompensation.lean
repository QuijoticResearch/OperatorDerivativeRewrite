import Foundation.ComplexRootPoissonConditionalCalculus

/-! Actual integrable, conditionally centered increments of bounded observables. -/
noncomputable section
open MeasureTheory ProbabilityTheory Preorder Finset
open scoped NNReal BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.ComplexRootPoissonCompensation
open ComplexRootPoissonTrajectory ComplexRootPoissonSemigroup
open ComplexRootPoissonConditionalCalculus

def gain (a : ℝ) (δ : ℝ≥0) (f : ComplexRootTransitionOperator.Test)
    (n : ℕ) (ω : Sample) : ℂ :=
  f (coordinate (n+1) ω) - transition a δ f (coordinate n ω)

theorem gain_integrable (a : ℝ) (δ : ℝ≥0) (f : ComplexRootTransitionOperator.Test) (n : ℕ) :
    Integrable (gain a δ f n) (law a δ) :=
  (observable_integrable a δ (n+1) f).sub
    (observable_integrable a δ n (transition a δ f))

theorem predicted_past_measurable (a : ℝ) (δ : ℝ≥0)
    (f : ComplexRootTransitionOperator.Test) (n : ℕ) :
    StronglyMeasurable[past n] (fun ω => transition a δ f (coordinate n ω)) := by
  have hm : Measurable (fun h : History n => h ⟨n, by simp⟩) :=
    measurable_pi_apply (X := fun _ : ↥(Iic n) => ℂ) ⟨n, by simp⟩
  have hp : @Measurable Sample (History n) (past n) inferInstance (frestrictLe n) :=
    measurable_iff_comap_le.mpr le_rfl
  exact ((transition a δ f).continuous.measurable.comp hm).comp hp |>.stronglyMeasurable

theorem gain_conditional_zero (a : ℝ) (δ : ℝ≥0)
    (f : ComplexRootTransitionOperator.Test) (n : ℕ) :
    (law a δ)[gain a δ f n | past n] =ᵐ[law a δ] 0 := by
  have hm : past n ≤ (inferInstance : MeasurableSpace Sample) :=
    (measurable_frestrictLe n).comap_le
  have hp := condExp_of_stronglyMeasurable (μ := law a δ) hm
    (predicted_past_measurable a δ f n)
    (observable_integrable a δ n (transition a δ f))
  have hs := condExp_sub (observable_integrable a δ (n+1) f)
    (observable_integrable a δ n (transition a δ f)) (past n)
  filter_upwards [hs, conditional_transition a δ n f] with ω hs ht
  change _ = (0 : ℂ)
  change (law a δ)[fun ω => f (coordinate (n+1) ω) -
    transition a δ f (coordinate n ω) | past n] ω = 0
  calc
    _ = (law a δ)[fun ω => f (coordinate (n+1) ω) | past n] ω -
        (law a δ)[fun ω => transition a δ f (coordinate n ω) | past n] ω := hs
    _ = 0 := by rw [hp]; exact sub_eq_zero.mpr ht

theorem gain_integral_zero (a : ℝ) (δ : ℝ≥0)
    (f : ComplexRootTransitionOperator.Test) (n : ℕ) :
    (∫ ω, gain a δ f n ω ∂law a δ) = 0 := by
  rw [← integral_condExp (m := past n) (measurable_frestrictLe n).comap_le]
  exact (integral_congr_ae (gain_conditional_zero a δ f n)).trans (integral_zero _ _)

end OperatorDerivativeRewrite.Foundation.ComplexRootPoissonCompensation
