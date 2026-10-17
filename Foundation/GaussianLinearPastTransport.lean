import Foundation.GaussianTiltBrownianDomain
import Foundation.GaussianCorrectedConditional

/-! The linear tilt preserves the full time-one past, while terminal half-density loses it. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianLinearPastTransport
open InfiniteGaussian GaussianTimeProcess GaussianCore GaussianCriticalExponential
  GaussianLinearTiltLaw GaussianTiltL2Domain GaussianTiltHalfDensity
  GaussianCorrectedHistoryLaw GaussianCorrectedConditional GaussianPastKernelTransport
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure Qlinear := Qlinear_probability

def historyPair : SampleSpace → History × ℝ :=
  shift GaussianUnboundedDelayedStep.evaluation ∘ historyCoordinates

theorem historyPair_measurable : Measurable historyPair :=
  (shift_measurable GaussianUnboundedDelayedStep.evaluation_measurable).comp
    historyCoordinates_measurable

theorem historyPair_eq (ω : SampleSpace) : historyPair ω = (past ω, process 2 ω) := by
  ext <;> simp [historyPair, shift, historyCoordinates,
    GaussianUnboundedDelayedStep.evaluation, past, GaussianPredictableStep.pastProcess]

theorem history_lintegral (f : History × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (historyPair ω) ∂Qlinear) = ∫⁻ p, f p ∂pastLaw.prod γ := by
  have hm : Measurable (fun p =>
      ENNReal.ofReal (likelihood GaussianUnboundedDelayedStep.evaluation p)*
        f (shift GaussianUnboundedDelayedStep.evaluation p)) :=
    (likelihood_measurable GaussianUnboundedDelayedStep.evaluation_measurable).ennreal_ofReal.mul
      (hf.comp (shift_measurable GaussianUnboundedDelayedStep.evaluation_measurable))
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (linearDensity ω)*f (historyPair ω) ∂gaussianProduct :=
      lintegral_withDensity_eq_lintegral_mul gaussianProduct
        linearDensity_measurable.ennreal_ofReal (hf.comp historyPair_measurable)
    _ = ∫⁻ p, ENNReal.ofReal (likelihood GaussianUnboundedDelayedStep.evaluation p)*
        f (shift GaussianUnboundedDelayedStep.evaluation p) ∂pastLaw.prod γ :=
      history_joint_law.lintegral_comp hm.aemeasurable
    _ = _ := weighted_lintegral pastLaw GaussianUnboundedDelayedStep.evaluation
      GaussianUnboundedDelayedStep.evaluation_measurable f hf

theorem history_hasLaw : HasLaw historyPair (pastLaw.prod γ) Qlinear := by
  refine ⟨historyPair_measurable.aemeasurable, ?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf historyPair_measurable]
  exact history_lintegral f hf

theorem past_law_linear : HasLaw past pastLaw Qlinear := by
  have hf : HasLaw (Prod.fst : History × ℝ → History) pastLaw (pastLaw.prod γ) :=
    ⟨measurable_fst.aemeasurable, by simp⟩
  exact hf.comp history_hasLaw

theorem whole_past_independent_linear : IndepFun past (process 2) Qlinear := by
  apply (indepFun_iff_hasLaw_prodMk_prod past_law_linear second_law).mpr
  exact history_hasLaw.congr
    (Filter.Eventually.of_forall (fun ω => (historyPair_eq ω).symm))

theorem Qlinear_eq_P_on_past {s : Set SampleSpace}
    (hs : MeasurableSet[naturalFiltration 1] s) : Qlinear s = gaussianProduct s := by
  rw [natural_eq_history_comap] at hs
  rcases hs with ⟨t, ht, rfl⟩
  calc
    Qlinear (past ⁻¹' t) = (Qlinear.map past) t := (Measure.map_apply past_measurable ht).symm
    _ = pastLaw t := congrArg (fun μ : Measure History => μ t) past_law_linear.map_eq
    _ = gaussianProduct (past ⁻¹' t) := Measure.map_apply past_measurable ht

theorem trim_eq : Qlinear.trim (naturalFiltration.le 1) =
    gaussianProduct.trim (naturalFiltration.le 1) := by
  apply @Measure.ext SampleSpace (naturalFiltration 1)
  intro s hs
  rw [trim_measurableSet_eq _ hs, trim_measurableSet_eq _ hs]
  exact Qlinear_eq_P_on_past hs

theorem past_lintegral {f : SampleSpace → ℝ≥0∞}
    (hf : Measurable[naturalFiltration 1] f) :
    (∫⁻ ω, f ω ∂Qlinear) = ∫⁻ ω, f ω ∂gaussianProduct := by
  calc
    _ = ∫⁻ ω, f ω ∂Qlinear.trim (naturalFiltration.le 1) :=
      (lintegral_trim (naturalFiltration.le 1) hf).symm
    _ = ∫⁻ ω, f ω ∂gaussianProduct.trim (naturalFiltration.le 1) := by rw [trim_eq]
    _ = _ := lintegral_trim (naturalFiltration.le 1) hf

theorem past_memLp_iff {f : SampleSpace → ℝ} (hf : Measurable[naturalFiltration 1] f) :
    MemLp f 2 Qlinear ↔ MemLp f 2 gaussianProduct := by
  have hm : Measurable f := hf.mono (naturalFiltration.le 1) le_rfl
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable,
    memLp_two_iff_integrable_sq hm.aestronglyMeasurable,
    ← lintegral_ofReal_ne_top_iff_integrable (hm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => sq_nonneg (f ω))),
    ← lintegral_ofReal_ne_top_iff_integrable (hm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => sq_nonneg (f ω))),
    past_lintegral (hf.pow_const 2).ennreal_ofReal]

theorem rootDensity_not_past : ¬ Measurable[naturalFiltration 1] rootDensity := by
  intro h
  exact rootDensity_not_memLp_Q ((past_memLp_iff h).mpr rootDensity_memLp_P)

theorem no_past_representative : ¬ ∃ f : SampleSpace → ℝ,
    Measurable[naturalFiltration 1] f ∧ f =ᵐ[gaussianProduct] rootDensity := by
  rintro ⟨f, hf, he⟩
  have hP : MemLp f 2 gaussianProduct := rootDensity_memLp_P.ae_eq he.symm
  have hQ : MemLp f 2 Qlinear := (past_memLp_iff hf).mpr hP
  exact rootDensity_not_memLp_Q (hQ.ae_eq (Qlinear_ac_P.ae_le he))

theorem transport_one : transport (fun _ => 1) = rootDensity := by
  funext ω
  exact mul_one _

theorem transport_one_not_past :
    ¬ Measurable[naturalFiltration 1] (transport (fun _ => 1)) := by
  rw [transport_one]
  exact rootDensity_not_past

end OperatorDerivativeRewrite.Foundation.GaussianLinearPastTransport
