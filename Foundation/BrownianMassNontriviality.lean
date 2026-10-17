import Foundation.BrownianMassStieltjesSupport

/-! Nontriviality of the constructed zero-supported mass, obtained from the
actual nondegenerate Brownian law and the centered native sign integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianMassNontriviality
open InfiniteGaussian GaussianTimeProcess IBMConstructedSources
open BrownianTanakaApproximation BrownianMassContinuousLimit BrownianMassLimitIdentification
open BrownianMassStieltjesSupport

theorem absoluteValue_ae_pos (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂gaussianProduct, 0 < absoluteValue T ω := by
  let _ : NullSingletonClass (gaussianReal 0 T) := nullSingletonClass_gaussianReal (ne_of_gt hT)
  have hn : ∀ᵐ ω ∂gaussianProduct, process T ω ≠ 0 :=
    ((process_hasLaw T).ae_iff (by fun_prop)).mpr ((gaussianReal 0 T).ae_ne 0)
  filter_upwards [absoluteValue_coeFn T, clockPath_coordinate_ae T, hn] with ω ha hb hn
  rw [ha, hb]
  exact abs_pos.mpr hn

theorem expected_mass_eq (T : ℝ≥0) :
    (∫ ω, limitPath ω T ∂gaussianProduct) = ∫ ω, absoluteValue T ω ∂gaussianProduct := by
  rw [integral_congr_ae (coordinate_ae T)]
  have he : BrownianTanakaResidual.mass T =ᵐ[gaussianProduct]
      fun ω => absoluteValue T ω - BrownianSignIntegral.terminal T ω := Lp.coeFn_sub _ _
  rw [integral_congr_ae he,
    integral_sub ((Lp.memLp (absoluteValue T)).integrable (by norm_num))
      ((Lp.memLp (BrownianSignIntegral.terminal T)).integrable (by norm_num)),
    BrownianSignIntegral.terminal_centered, sub_zero]

theorem expected_mass_pos (T : ℝ≥0) (hT : 0 < T) :
    0 < ∫ ω, limitPath ω T ∂gaussianProduct := by
  rw [expected_mass_eq]
  have hp := absoluteValue_ae_pos T hT
  have hi := (Lp.memLp (absoluteValue T)).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hn := hp.mono (fun _ h => h.le)
  by_contra! hle
  have hz := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp
    (le_antisymm hle (integral_nonneg_of_ae hn))
  have hf : ∀ᵐ ω ∂gaussianProduct, False := by
    filter_upwards [hp, hz] with ω hp hz
    exact (ne_of_gt hp) hz
  have hzμ : gaussianProduct = 0 := by simpa using hf
  have hm := congrArg (fun μ : Measure SampleSpace => μ univ) hzμ
  simpa using hm

theorem horizon_mass_identity : ∀ᵐ ω ∂gaussianProduct, ∀ T : ℝ≥0,
    (massMeasure ω (Ioc 0 T)).toReal = limitPath ω T := by
  filter_upwards [massMeasure_Ioc, limitPath_properties] with ω hm hp T
  rw [hm, hp.1, sub_zero, ENNReal.toReal_ofReal (hp.2.2 T)]

theorem expected_horizon_mass_pos (T : ℝ≥0) (hT : 0 < T) :
    0 < ∫ ω, (massMeasure ω (Ioc 0 T)).toReal ∂gaussianProduct := by
  rw [integral_congr_ae (horizon_mass_identity.mono (fun _ h => h T))]
  exact expected_mass_pos T hT

end OperatorDerivativeRewrite.Foundation.BrownianMassNontriviality
