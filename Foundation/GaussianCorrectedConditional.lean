import Foundation.GaussianCorrectedHistoryLaw
import Mathlib.Probability.ConditionalExpectation

/-! Conditional terminal correction on the actual raw natural filtration under Q. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianCorrectedConditional
open InfiniteGaussian GaussianTimeProcess GaussianCore GaussianRandomTerminalMeasure
  GaussianCorrectedTerminalLaw GaussianCorrectedHistoryLaw
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure Q := Q_probability

theorem natural_eq_history_comap :
    naturalFiltration 1 = MeasurableSpace.comap past inferInstance :=
  Filtration.natural_eq_comap process process_stronglyMeasurable 1

theorem noise_measurable : Measurable noise :=
  ((process_stronglyMeasurable 2).measurable.sub
    (process_stronglyMeasurable 1).measurable).add
      (Real.measurable_sin.comp (process_stronglyMeasurable 1).measurable)

theorem noise_integrable : Integrable noise Q :=
  (noise_law_Q.memLp (memLp_id_gaussianReal 2)).integrable (by norm_num)

theorem noise_integral : (∫ ω, noise ω ∂Q) = 0 := by
  rw [noise_law_Q.integral_eq]
  exact integral_id_gaussianReal

theorem noise_indep_natural :
    Indep (MeasurableSpace.comap noise inferInstance) (naturalFiltration 1) Q := by
  rw [natural_eq_history_comap]
  exact (IndepFun_iff_Indep _ _ _).mp whole_past_independent.symm

theorem noise_condExp_zero : Q[noise | naturalFiltration 1] =ᵐ[Q] fun _ => 0 := by
  have h := condExp_indep_eq noise_measurable.comap_le (naturalFiltration.le 1)
    (comap_measurable noise).stronglyMeasurable noise_indep_natural
  simpa only [noise_integral] using h

def correctedTerminal (ω : SampleSpace) : ℝ := process 1 ω + noise ω

theorem correctedTerminal_eq (ω : SampleSpace) :
    correctedTerminal ω = process 2 ω + Real.sin (process 1 ω) := by
  dsimp [correctedTerminal, noise]
  ring

theorem past_integrable : Integrable (process 1) Q :=
  (GaussianCorrectedTerminalLaw.past_law_Q.memLp (memLp_id_gaussianReal 2)).integrable
    (by norm_num)

theorem correctedTerminal_integrable : Integrable correctedTerminal Q :=
  past_integrable.add noise_integrable

theorem coefficient_integrable : Integrable (VolterraRandomStepDrift.coefficient process) Q :=
  (VolterraRandomStepDrift.coefficient_memLp process
    (fun t => (process_stronglyMeasurable t).measurable)).integrable (by norm_num)

theorem coefficient_past :
    StronglyMeasurable[naturalFiltration 1] (VolterraRandomStepDrift.coefficient process) :=
  (Real.measurable_sin.comp (process_stronglyAdapted 1).measurable).stronglyMeasurable

theorem originalTerminal_integrable : Integrable (process 2) Q := by
  have he : process 2 = correctedTerminal - VolterraRandomStepDrift.coefficient process := by
    funext ω
    change process 2 ω = correctedTerminal ω - VolterraRandomStepDrift.coefficient process ω
    rw [correctedTerminal_eq]
    simp only [VolterraRandomStepDrift.coefficient, add_sub_cancel_right]
  rw [he]
  exact correctedTerminal_integrable.sub coefficient_integrable

theorem corrected_condExp :
    Q[correctedTerminal | naturalFiltration 1] =ᵐ[Q] process 1 := by
  change Q[process 1 + noise | naturalFiltration 1] =ᵐ[Q] process 1
  have hp := condExp_of_stronglyMeasurable (naturalFiltration.le 1)
    (process_stronglyAdapted 1) past_integrable
  have ha := condExp_add past_integrable noise_integrable (naturalFiltration 1)
  filter_upwards [ha, noise_condExp_zero] with ω hω hn
  simpa only [correctedTerminal, hp, Pi.add_apply, hn, add_zero] using hω

theorem original_condExp : Q[process 2 | naturalFiltration 1] =ᵐ[Q]
    fun ω => process 1 ω - VolterraRandomStepDrift.coefficient process ω := by
  have he : process 2 = correctedTerminal - VolterraRandomStepDrift.coefficient process := by
    funext ω
    change process 2 ω = correctedTerminal ω - VolterraRandomStepDrift.coefficient process ω
    rw [correctedTerminal_eq]
    simp only [VolterraRandomStepDrift.coefficient, add_sub_cancel_right]
  have hc := condExp_of_stronglyMeasurable (naturalFiltration.le 1)
    coefficient_past coefficient_integrable
  have hs := condExp_sub correctedTerminal_integrable coefficient_integrable
    (naturalFiltration 1)
  rw [he]
  filter_upwards [hs, corrected_condExp] with ω hω ht
  simpa only [Pi.sub_apply, hc, ht] using hω

theorem original_not_martingale_step :
    ¬ Q[process 2 | naturalFiltration 1] =ᵐ[Q] process 1 := by
  intro h
  have hz : VolterraRandomStepDrift.coefficient process =ᵐ[Q] fun _ => 0 := by
    filter_upwards [original_condExp, h] with ω he hh
    have ht := he.symm.trans hh
    linarith
  exact VolterraRandomStepDrift.coefficient_not_constant process
    GaussianCorrectedTerminalLaw.past_law_Q 0 hz

end OperatorDerivativeRewrite.Foundation.GaussianCorrectedConditional
