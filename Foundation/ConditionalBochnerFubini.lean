import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-! Conditional Fubini with an explicit jointly measurable conditional representative. -/
noncomputable section
open MeasureTheory Filter
namespace OperatorDerivativeRewrite.Foundation.ConditionalBochnerFubini

variable {Ω T E : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] [mT : MeasurableSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem conditional_integral (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure T) [SFinite ν] (hm : m ≤ mΩ)
    (F G : Ω × T → E) (hF : Integrable F (μ.prod ν)) (hG : Integrable G (μ.prod ν))
    (hGm : StronglyMeasurable[m.prod mT] G)
    (hCE : ∀ᵐ t ∂ν, μ[fun ω => F (ω, t) | m] =ᵐ[μ] fun ω => G (ω, t)) :
    μ[fun ω => ∫ t, F (ω, t) ∂ν | m] =ᵐ[μ] fun ω => ∫ t, G (ω, t) ∂ν := by
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hF.integral_prod_left
    (fun A _ _ => hG.integral_prod_left.integrableOn)
  · intro A hA _
    have hFr : Integrable F ((μ.restrict A).prod ν) := by
      rw [Measure.restrict_prod_eq_prod_univ]
      exact hF.restrict
    have hGr : Integrable G ((μ.restrict A).prod ν) := by
      rw [Measure.restrict_prod_eq_prod_univ]
      exact hG.restrict
    rw [integral_integral_swap (f := fun ω t => G (ω,t)) hGr,
      integral_integral_swap (f := fun ω t => F (ω,t)) hFr]
    apply integral_congr_ae
    filter_upwards [hCE,hF.prod_left_ae] with t ht hft
    calc
      (∫ ω in A, G (ω,t) ∂μ) = ∫ ω in A, μ[fun ω => F (ω,t) | m] ω ∂μ :=
        integral_congr_ae (ae_restrict_of_ae ht.symm)
      _ = ∫ ω in A, F (ω,t) ∂μ := setIntegral_condExp hm hft hA
  · let : MeasurableSpace Ω := m
    exact hGm.integral_prod_right'.aestronglyMeasurable

end OperatorDerivativeRewrite.Foundation.ConditionalBochnerFubini
