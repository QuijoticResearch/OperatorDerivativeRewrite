import Foundation.GaussianLinearPastTransport
import Foundation.GaussianConditionalClarkOcone

/-! Finite-horizon representation and conditional-transport failure for the likelihood root. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianTiltFiniteHorizon
open InfiniteGaussian GaussianTimeProcess GaussianRandomDensityKernel
  GaussianTiltL2Domain GaussianTiltBrownianDomain GaussianLinearPastTransport
  GaussianPredictableFull GaussianPredictableAdjoint GaussianPredictableCutoff
  GaussianConditionalIto GaussianConditionalClarkOcone GaussianLinearTiltLaw GaussianTiltHalfDensity
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

theorem rootDensity_past_two : Measurable[naturalFiltration 2] rootDensity := by
  have h1 := ((process_stronglyAdapted 1).mono
    (naturalFiltration.mono (show (1 : ℝ≥0) ≤ 2 by norm_num))).measurable
  have h2 := (process_stronglyAdapted 2).measurable
  exact Real.continuous_sqrt.measurable.comp
    (kernel_continuous.measurable.comp (h1.prodMk (h2.sub h1)))

theorem terminalValue_past_two : terminalValue ∈ pastL2 2 :=
  rootDensity_past_two.stronglyMeasurable.aestronglyMeasurable.congr terminalValue_coeFn.symm

theorem terminalValue_not_past_one : terminalValue ∉ pastL2 1 := by
  intro h
  have hm : AEStronglyMeasurable[naturalFiltration 1] terminalValue gaussianProduct := h
  apply no_past_representative
  exact ⟨hm.mk terminalValue, hm.stronglyMeasurable_mk.measurable,
    hm.ae_eq_mk.symm.trans terminalValue_coeFn⟩

theorem terminal_projection_two : pastProjection 2 terminalValue = terminalValue :=
  Submodule.starProjection_eq_self_iff.mpr terminalValue_past_two

theorem terminal_projection_one_ne : pastProjection 1 terminalValue ≠ terminalValue := by
  intro h
  exact terminalValue_not_past_one (Submodule.starProjection_eq_self_iff.mp h)

theorem representer_cut_two :
    predictableCut 2 (predictableAdjoint terminalValue) = predictableAdjoint terminalValue :=
  past_representer_supported 2 terminalValue terminalValue_past_two

theorem finite_horizon_representation : ∃! U : fullPredictable,
    itoIntegral U = terminalValue - (∫ ω, terminalValue ω ∂gaussianProduct) • gaussianOne ∧
      predictableCut 2 U = U :=
  GaussianConditionalClarkOcone.finite_horizon_representation 2 terminalValue terminalValue_past_two

theorem future_representer_nonzero :
    predictableAdjoint terminalValue - predictableCut 1 (predictableAdjoint terminalValue) ≠ 0 := by
  intro h
  have he := conditional_representation 1 terminalValue terminalValue_brownian
  rw [h, map_zero] at he
  exact terminal_projection_one_ne (sub_eq_zero.mp he).symm

theorem conditional_error_positive : 0 < ‖terminalValue-pastProjection 1 terminalValue‖^2 := by
  have hn : terminalValue-pastProjection 1 terminalValue ≠ 0 := by
    intro h
    exact terminal_projection_one_ne (sub_eq_zero.mp h).symm
  exact sq_pos_of_pos (norm_pos_iff.mpr hn)

theorem future_energy_positive :
    0 < ‖predictableAdjoint terminalValue -
      predictableCut 1 (predictableAdjoint terminalValue)‖^2 := by
  rw [← conditional_variance_identity 1 terminalValue terminalValue_brownian]
  exact conditional_error_positive

theorem root_condExp_not_self :
    ¬ gaussianProduct[rootDensity | naturalFiltration 1] =ᵐ[gaussianProduct] rootDensity := by
  intro h
  apply no_past_representative
  exact ⟨gaussianProduct[rootDensity | naturalFiltration 1],
    stronglyMeasurable_condExp.measurable, h⟩

theorem terminal_transport_not_conditional_intertwiner :
    ¬ gaussianProduct[transport (fun _ => (1 : ℝ)) | naturalFiltration 1] =ᵐ[gaussianProduct]
      transport (Qlinear[fun _ => (1 : ℝ) | naturalFiltration 1]) := by
  letI : IsProbabilityMeasure Qlinear := Qlinear_probability
  simpa only [condExp_const (naturalFiltration.le 1), transport_one] using root_condExp_not_self

end OperatorDerivativeRewrite.Foundation.GaussianTiltFiniteHorizon
