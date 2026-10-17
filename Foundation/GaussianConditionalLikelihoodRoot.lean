import Foundation.GaussianLikelihoodRootKernel
import Foundation.GaussianLinearPastTransport

/-! Exact conditional expectation of the terminal likelihood root on the full time-one past. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.GaussianConditionalLikelihoodRoot
open InfiniteGaussian GaussianTimeProcess GaussianCore GaussianCriticalExponential
open GaussianRandomDensityKernel GaussianLikelihoodRootKernel GaussianTiltL2Domain
open GaussianCorrectedHistoryLaw GaussianCorrectedConditional GaussianUnboundedDelayedStep
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def historyRoot (p : History × ℝ) : ℝ := rootKernel (evaluation p.1) p.2
def historyMean (h : History) : ℝ := Real.exp (-(evaluation h)^2/8)
def meanPast (ω : SampleSpace) : ℝ := historyMean (past ω)

theorem historyRoot_measurable : Measurable historyRoot :=
  rootKernel_continuous.measurable.comp
    ((evaluation_measurable.comp measurable_fst).prodMk measurable_snd)

theorem historyMean_measurable : Measurable historyMean :=
  Real.measurable_exp.comp ((evaluation_measurable.pow_const 2).neg.div_const 8)

theorem historyRoot_comp (ω : SampleSpace) : historyRoot (historyCoordinates ω) = rootDensity ω := by
  rw [historyRoot, rootKernel_eq_sqrt]
  rfl

theorem historyRoot_integrable : Integrable historyRoot (pastLaw.prod γ) := by
  rw [← history_joint_law.map_eq]
  apply (integrable_map_measure historyRoot_measurable.aestronglyMeasurable
    historyCoordinates_measurable.aemeasurable).mpr
  simpa only [Function.comp_def, historyRoot_comp] using
    (rootDensity_memLp_P.integrable (by norm_num))

theorem historyRoot_setIntegral (t : Set History) (ht : MeasurableSet t) :
    (∫ p in Prod.fst ⁻¹' t, historyRoot p ∂pastLaw.prod γ) =
      ∫ h in t, historyMean h ∂pastLaw := by
  classical
  rw [← integral_indicator (measurable_fst ht),
    integral_prod _ (historyRoot_integrable.indicator (measurable_fst ht)),
    ← integral_indicator ht]
  apply integral_congr_ae
  filter_upwards [] with h
  by_cases hh : h ∈ t
  · simp [Set.indicator, hh, historyRoot, historyMean, rootKernel_integral]
  · simp [Set.indicator, hh]

theorem meanPast_eq (ω : SampleSpace) : meanPast ω = Real.exp (-(process 1 ω)^2/8) := rfl

theorem meanPast_measurable : Measurable meanPast :=
  historyMean_measurable.comp past_measurable

theorem meanPast_past : Measurable[naturalFiltration 1] meanPast :=
  Real.measurable_exp.comp (((process_stronglyAdapted 1).measurable.pow_const 2).neg.div_const 8)

theorem meanPast_integrable : Integrable meanPast gaussianProduct := by
  apply (integrable_const (1 : ℝ)).mono' meanPast_measurable.aestronglyMeasurable
  filter_upwards [] with ω
  rw [meanPast_eq, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact fiber_mean_le_one _

theorem rootDensity_setIntegral (t : Set History) (ht : MeasurableSet t) :
    (∫ ω in past ⁻¹' t, rootDensity ω ∂gaussianProduct) =
      ∫ ω in past ⁻¹' t, meanPast ω ∂gaussianProduct := by
  calc
    _ = ∫ p in Prod.fst ⁻¹' t, historyRoot p ∂pastLaw.prod γ := by
      rw [← history_joint_law.map_eq,
        setIntegral_map (measurable_fst ht) historyRoot_measurable.aestronglyMeasurable
          historyCoordinates_measurable.aemeasurable]
      apply integral_congr_ae
      filter_upwards [] with ω
      exact (historyRoot_comp ω).symm
    _ = ∫ h in t, historyMean h ∂pastLaw := historyRoot_setIntegral t ht
    _ = _ := by
      rw [← past_hasLaw.map_eq,
        setIntegral_map ht historyMean_measurable.aestronglyMeasurable
          past_measurable.aemeasurable]
      rfl

theorem rootDensity_condExp :
    gaussianProduct[rootDensity | naturalFiltration 1] =ᵐ[gaussianProduct] meanPast := by
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (naturalFiltration.le 1)
    (rootDensity_memLp_P.integrable (by norm_num))
  · intro s _ _
    exact meanPast_integrable.integrableOn
  · intro s hs _
    rw [natural_eq_history_comap] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact (rootDensity_setIntegral t ht).symm
  · exact meanPast_past.stronglyMeasurable.aestronglyMeasurable

theorem rootDensity_condExp_exp :
    gaussianProduct[rootDensity | naturalFiltration 1] =ᵐ[gaussianProduct]
      fun ω => Real.exp (-(process 1 ω)^2/8) := rootDensity_condExp

end OperatorDerivativeRewrite.Foundation.GaussianConditionalLikelihoodRoot
