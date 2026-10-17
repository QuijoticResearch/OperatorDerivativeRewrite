import Foundation.GaussianCorrectedConditional

/-! The actual terminal density has conditional expectation one before the delayed step. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianPastDensityConditional
open InfiniteGaussian GaussianTimeProcess GaussianRandomTerminalMeasure
  GaussianCorrectedHistoryLaw GaussianCorrectedConditional
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure Q := Q_probability

theorem Q_eq_P_on_past {s : Set SampleSpace}
    (hs : MeasurableSet[naturalFiltration 1] s) : Q s = gaussianProduct s := by
  rw [natural_eq_history_comap] at hs
  rcases hs with ⟨t, ht, rfl⟩
  calc
    Q (past ⁻¹' t) = (Q.map past) t := (Measure.map_apply past_measurable ht).symm
    _ = pastLaw t := congrArg (fun μ : Measure History => μ t)
      GaussianCorrectedHistoryLaw.past_law_Q.map_eq
    _ = gaussianProduct (past ⁻¹' t) := Measure.map_apply past_measurable ht

theorem density_setIntegral {s : Set SampleSpace} (hs : MeasurableSet s) :
    (∫ ω in s, density ω ∂gaussianProduct) = Q.real s := by
  have h : ENNReal.ofReal (∫ ω in s, density ω ∂gaussianProduct) = Q s := by
    rw [Q, withDensity_apply _ hs]
    exact ofReal_integral_eq_lintegral_ofReal density_integrable.integrableOn
      (Filter.Eventually.of_forall (fun ω => (density_positive ω).le))
  have hp : 0 ≤ ∫ ω in s, density ω ∂gaussianProduct :=
    integral_nonneg (fun ω => (density_positive ω).le)
  simpa only [ENNReal.toReal_ofReal hp, measureReal_def] using congrArg ENNReal.toReal h

theorem density_condExp_one :
    gaussianProduct[density | naturalFiltration 1] =ᵐ[gaussianProduct] fun _ => 1 := by
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (naturalFiltration.le 1) density_integrable
  · intro s hs hfin
    exact (integrable_const (1 : ℝ)).integrableOn
  · intro s hs hfin
    rw [density_setIntegral (naturalFiltration.le 1 s hs)]
    simp only [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, Q_eq_P_on_past hs]
  · exact stronglyMeasurable_const.aestronglyMeasurable

theorem density_condExp_before {t : ℝ≥0} (ht : t ≤ 1) :
    gaussianProduct[density | naturalFiltration t] =ᵐ[gaussianProduct] fun _ => 1 := by
  have h := condExp_condExp_of_le (naturalFiltration.mono ht) (naturalFiltration.le 1)
    (f := density) (μ := gaussianProduct)
  have hc := condExp_congr_ae (m := naturalFiltration t) density_condExp_one
  exact h.symm.trans (hc.trans (Filter.Eventually.of_forall (fun ω => by
    rw [condExp_const (naturalFiltration.le t)])))

end OperatorDerivativeRewrite.Foundation.GaussianPastDensityConditional
