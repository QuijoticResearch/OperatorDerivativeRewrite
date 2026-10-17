import Foundation.GaussianPastKernelTransport
import Foundation.GaussianCorrectedTerminalLaw

/-! The corrected terminal increment is independent of the entire raw time-one history. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianCorrectedHistoryLaw
open InfiniteGaussian GaussianTimeProcess GaussianCore GaussianRandomDensityKernel
  GaussianRandomTerminalMeasure GaussianCorrectedTerminalLaw
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure Q := Q_probability

abbrev History := Set.Iic (1 : ℝ≥0) → ℝ

def past : SampleSpace → History := GaussianPredictableStep.pastProcess process 1

def pastLaw : Measure History := gaussianProduct.map past

def coefficient : History → ℝ := VolterraRandomStepDrift.pastFunction

def historyCoordinates (ω : SampleSpace) : History × ℝ :=
  (past ω, process 2 ω-process 1 ω)

def correctedHistoryCoordinates (ω : SampleSpace) : History × ℝ := (past ω, noise ω)

theorem past_measurable : Measurable past :=
  measurable_pi_iff.mpr (fun r => (process_stronglyMeasurable r.val).measurable)

theorem coefficient_measurable : Measurable coefficient :=
  VolterraRandomStepDrift.pastFunction_measurable

theorem past_hasLaw : HasLaw past pastLaw gaussianProduct :=
  hasLaw_map past_measurable.aemeasurable

instance pastLaw_probability : IsProbabilityMeasure pastLaw :=
  past_hasLaw.isProbabilityMeasure_iff.mp inferInstance

theorem past_future_independent :
    IndepFun past (fun ω => process 2 ω-process 1 ω) gaussianProduct := by
  have hi := (process_isPreBrownian.indepFun_shift 1).symm.comp measurable_id
    (measurable_pi_apply (2 - 1 : ℝ≥0))
  change IndepFun (fun ω (r : Set.Iic (1 : ℝ≥0)) => process r.val ω) _ gaussianProduct
  simpa only [Function.comp_def, add_tsub_cancel_of_le (show (1 : ℝ≥0) ≤ 2 by norm_num),
    id_eq] using hi

theorem history_joint_law :
    HasLaw historyCoordinates (pastLaw.prod γ) gaussianProduct :=
  past_future_independent.hasLaw_prod past_hasLaw future_law

theorem historyCoordinates_measurable : Measurable historyCoordinates :=
  past_measurable.prodMk
    ((process_stronglyMeasurable 2).measurable.sub (process_stronglyMeasurable 1).measurable)

theorem correctedHistoryCoordinates_measurable : Measurable correctedHistoryCoordinates :=
  past_measurable.prodMk
    ((process_stronglyMeasurable 2).measurable.sub (process_stronglyMeasurable 1).measurable |>.add
      (Real.measurable_sin.comp (process_stronglyMeasurable 1).measurable))

theorem history_lintegral (f : History × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (correctedHistoryCoordinates ω) ∂Q)=∫⁻ p, f p ∂pastLaw.prod γ := by
  have hm : Measurable (fun p =>
      ENNReal.ofReal (GaussianPastKernelTransport.likelihood coefficient p) *
        f (GaussianPastKernelTransport.shift coefficient p)) :=
    (GaussianPastKernelTransport.likelihood_measurable coefficient_measurable).ennreal_ofReal.mul
      (hf.comp (GaussianPastKernelTransport.shift_measurable coefficient_measurable))
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (density ω)*f (correctedHistoryCoordinates ω) ∂gaussianProduct :=
      lintegral_withDensity_eq_lintegral_mul gaussianProduct density_measurable.ennreal_ofReal
        (hf.comp correctedHistoryCoordinates_measurable)
    _ = ∫⁻ p, ENNReal.ofReal (GaussianPastKernelTransport.likelihood coefficient p) *
        f (GaussianPastKernelTransport.shift coefficient p) ∂pastLaw.prod γ :=
      history_joint_law.lintegral_comp hm.aemeasurable
    _ = _ := GaussianPastKernelTransport.weighted_lintegral pastLaw coefficient
      coefficient_measurable f hf

theorem corrected_history_hasLaw :
    HasLaw correctedHistoryCoordinates (pastLaw.prod γ) Q := by
  refine ⟨correctedHistoryCoordinates_measurable.aemeasurable, ?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf correctedHistoryCoordinates_measurable]
  exact history_lintegral f hf

theorem past_law_Q : HasLaw past pastLaw Q := by
  have hf : HasLaw (Prod.fst : History × ℝ → History) pastLaw (pastLaw.prod γ) :=
    ⟨measurable_fst.aemeasurable, by simp⟩
  exact hf.comp corrected_history_hasLaw

theorem whole_past_independent : IndepFun past noise Q := by
  apply (indepFun_iff_hasLaw_prodMk_prod past_law_Q noise_law_Q).mpr
  exact corrected_history_hasLaw

end OperatorDerivativeRewrite.Foundation.GaussianCorrectedHistoryLaw
