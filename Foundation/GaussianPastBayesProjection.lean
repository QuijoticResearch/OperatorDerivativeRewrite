import Foundation.GaussianUnitaryConditionalFormula

/-! Bayes' formula on the preserved past and the resulting weighted P-level projection. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianPastBayesProjection
open InfiniteGaussian GaussianTimeProcess GaussianLinearTiltLaw GaussianCriticalExponential
open GaussianTiltL2Domain GaussianTiltHalfDensity GaussianHalfDensityUnitary
open GaussianLinearPastTransport GaussianTransportedPastProjection GaussianUnitaryConditionalFormula
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure Qlinear := Qlinear_probability

theorem past_setIntegral_eq {f : SampleSpace → ℝ}
    (hf : StronglyMeasurable[naturalFiltration 1] f) {s : Set SampleSpace}
    (hs : MeasurableSet[naturalFiltration 1] s) :
    (∫ ω in s, f ω ∂Qlinear) = ∫ ω in s, f ω ∂gaussianProduct := by
  calc
    _ = ∫ ω in s, f ω ∂Qlinear.trim (naturalFiltration.le 1) :=
      setIntegral_trim (naturalFiltration.le 1) hf hs
    _ = ∫ ω in s, f ω ∂gaussianProduct.trim (naturalFiltration.le 1) := by rw [trim_eq]
    _ = _ := (setIntegral_trim (naturalFiltration.le 1) hf hs).symm

theorem density_weighted_integrable (u : QSpace) :
    Integrable (fun ω => linearDensity ω * u ω) gaussianProduct := by
  have h := rootDensity_memLp_P.integrable_mul (forward_memLp u)
  convert h using 1
  funext ω
  change linearDensity ω * u ω = rootDensity ω * (rootDensity ω * u ω)
  rw [← rootDensity_sq]
  ring

theorem density_setIntegral (u : QSpace) {s : Set SampleSpace} (hs : MeasurableSet s) :
    (∫ ω in s, u ω ∂Qlinear) = ∫ ω in s, linearDensity ω * u ω ∂gaussianProduct := by
  classical
  rw [← integral_indicator hs, ← integral_indicator hs]
  change (∫ ω, s.indicator (fun z => u z) ω ∂gaussianProduct.withDensity
    (fun z => ENNReal.ofReal (linearDensity z))) = _
  rw [integral_withDensity_eq_integral_toReal_smul linearDensity_measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [ENNReal.toReal_ofReal (linearDensity_positive ω).le]
  by_cases h : ω ∈ s <;> simp [Set.indicator, h, smul_eq_mul]

theorem qConditional_memLp_P (u : QSpace) :
    MemLp (Qlinear[u | naturalFiltration 1]) 2 gaussianProduct := by
  apply (past_memLp_iff stronglyMeasurable_condExp.measurable).mp
  exact (Lp.memLp ((qPast 1).starProjection u)).ae_eq (qProjection_ae 1 u)

theorem bayes_past (u : QSpace) :
    Qlinear[u | naturalFiltration 1] =ᵐ[gaussianProduct]
      gaussianProduct[(fun ω => linearDensity ω * u ω) | naturalFiltration 1] := by
  apply ae_eq_condExp_of_forall_setIntegral_eq (naturalFiltration.le 1)
    (density_weighted_integrable u)
  · intro s _ _
    exact ((qConditional_memLp_P u).integrable (by norm_num)).integrableOn
  · intro s hs _
    calc
      _ = ∫ ω in s, Qlinear[u | naturalFiltration 1] ω ∂Qlinear :=
        (past_setIntegral_eq stronglyMeasurable_condExp hs).symm
      _ = ∫ ω in s, u ω ∂Qlinear :=
        setIntegral_condExp (naturalFiltration.le 1) ((Lp.memLp u).integrable (by norm_num)) hs
      _ = _ := density_setIntegral u (naturalFiltration.le 1 s hs)
  · exact stronglyMeasurable_condExp.aestronglyMeasurable

theorem inverse_weight (v : InfiniteGaussian.GaussianL2) :
    (fun ω => linearDensity ω * unitary.symm v ω) =ᵐ[gaussianProduct]
      fun ω => rootDensity ω * v ω := by
  filter_upwards [P_ac_Qlinear.ae_le (unitary_symm_coeFn v)] with ω hω
  rw [hω]
  change linearDensity ω * (v ω / rootDensity ω) = rootDensity ω * v ω
  rw [← rootDensity_sq]
  field_simp [(rootDensity_positive ω).ne']

theorem root_weighted_integrable (v : InfiniteGaussian.GaussianL2) :
    Integrable (fun ω => rootDensity ω * v ω) gaussianProduct :=
  rootDensity_memLp_P.integrable_mul (Lp.memLp v)

theorem pureP_projection_formula (v : InfiniteGaussian.GaussianL2) :
    transportedProjection 1 v =ᵐ[gaussianProduct]
      fun ω => rootDensity ω *
        gaussianProduct[(fun z => rootDensity z * v z) | naturalFiltration 1] ω := by
  rw [transportedProjection_apply]
  have hq : (qPast 1).starProjection (unitary.symm v) =ᵐ[gaussianProduct]
      Qlinear[unitary.symm v | naturalFiltration 1] :=
    P_ac_Qlinear.ae_le (qProjection_ae 1 (unitary.symm v))
  have hp := hq.trans ((bayes_past (unitary.symm v)).trans
      (condExp_congr_ae (m := naturalFiltration 1) (inverse_weight v)))
  filter_upwards [unitary_coeFn ((qPast 1).starProjection (unitary.symm v)), hp] with ω hu hω
  rw [hu]
  change rootDensity ω * (qPast 1).starProjection (unitary.symm v) ω = _
  rw [hω]

theorem weighted_projection_memLp (v : InfiniteGaussian.GaussianL2) :
    MemLp (fun ω => rootDensity ω *
      gaussianProduct[(fun z => rootDensity z * v z) | naturalFiltration 1] ω)
        2 gaussianProduct :=
  (Lp.memLp (transportedProjection 1 v)).ae_eq (pureP_projection_formula v)

end OperatorDerivativeRewrite.Foundation.GaussianPastBayesProjection
