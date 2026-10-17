import Foundation.BrownianMassClockStoppingTime
import Foundation.GaussianHermiteMartingale

/-! Actual continuous versions remain martingales after ambient null augmentation.
No strong Markov or sticky occupation assertion is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianAugmentedMartingales
open InfiniteGaussian GaussianTimeProcess IBMConstructedSources
open BrownianMassContinuousLimit BrownianMassClockStoppingTime AmbientNullAugmentation

theorem brownian_coordinate_measurable (t : ℝ≥0) :
    Measurable (fun ω => clockPath ω t) :=
  (ContinuousMap.measurable_eval t).comp clockPath_measurable

theorem brownian_integrable (t : ℝ≥0) :
    Integrable (fun ω => clockPath ω t) gaussianProduct := by
  have h := GaussianHermiteMartingale.hermite_integrable 1 t
  simp only [GaussianTimeSpaceHermite.value_one] at h
  exact h.congr (clockPath_coordinate_ae t).symm

theorem brownian_stronglyAdapted :
    StronglyAdapted augmentedPast (fun t ω => clockPath ω t) := by
  intro t
  exact (measurable_of_raw_aestronglyMeasurable (naturalFiltration t) gaussianProduct
    (brownian_coordinate_measurable t)
    ((process_stronglyAdapted t).aestronglyMeasurable.congr
      (clockPath_coordinate_ae t).symm)).stronglyMeasurable

theorem brownian_martingale :
    Martingale (fun t ω => clockPath ω t) augmentedPast gaussianProduct := by
  refine ⟨brownian_stronglyAdapted, ?_⟩
  intro s t hst
  have h := GaussianHermiteMartingale.hermite_condExp 1 s t hst
  simp only [GaussianTimeSpaceHermite.value_one] at h
  exact (condExp_unchanged s _ (brownian_integrable t)).symm.trans
    ((condExp_congr_ae (clockPath_coordinate_ae t)).trans
      (h.trans (clockPath_coordinate_ae s).symm))

def signIntegralPath (ω : SampleSpace) : C(ℝ≥0, ℝ) :=
  ⟨fun t => |clockPath ω t| - limitPath ω t,
    (clockPath ω).continuous.abs.sub (limitPath ω).continuous⟩

theorem signIntegral_coordinate_ae (t : ℝ≥0) :
    (fun ω => signIntegralPath ω t) =ᵐ[gaussianProduct] BrownianSignIntegral.terminal t := by
  filter_upwards [BrownianMassLimitIdentification.tanaka_ae t] with ω h
  change |clockPath ω t| - limitPath ω t = _
  linarith

theorem signIntegral_coordinate_measurable (t : ℝ≥0) :
    Measurable (fun ω => signIntegralPath ω t) :=
  (continuous_abs.measurable.comp (brownian_coordinate_measurable t)).sub
    ((ContinuousMap.measurable_eval t).comp limitPath_measurable)

theorem signIntegral_integrable (t : ℝ≥0) :
    Integrable (fun ω => signIntegralPath ω t) gaussianProduct :=
  ((Lp.memLp (BrownianSignIntegral.terminal t)).integrable (by norm_num)).congr
    (signIntegral_coordinate_ae t).symm

theorem signIntegral_stronglyAdapted :
    StronglyAdapted augmentedPast (fun t ω => signIntegralPath ω t) := by
  intro t
  have h := BrownianSignConditional.terminal_past t
  change AEStronglyMeasurable[naturalFiltration t]
    (BrownianSignIntegral.terminal t) gaussianProduct at h
  exact (measurable_of_raw_aestronglyMeasurable (naturalFiltration t) gaussianProduct
    (signIntegral_coordinate_measurable t)
    (h.congr (signIntegral_coordinate_ae t).symm)).stronglyMeasurable

theorem signIntegral_martingale :
    Martingale (fun t ω => signIntegralPath ω t) augmentedPast gaussianProduct := by
  refine ⟨signIntegral_stronglyAdapted, ?_⟩
  intro s t hst
  exact (condExp_unchanged s _ (signIntegral_integrable t)).symm.trans
    ((condExp_congr_ae (signIntegral_coordinate_ae t)).trans
      ((BrownianSignConditional.conditional_expectation s t hst).trans
        (signIntegral_coordinate_ae s).symm))

theorem tanaka_all (ω : SampleSpace) (t : ℝ≥0) :
    |clockPath ω t| = signIntegralPath ω t + limitPath ω t := by
  change |clockPath ω t| = (|clockPath ω t| - limitPath ω t) + limitPath ω t
  ring

end OperatorDerivativeRewrite.Foundation.BrownianAugmentedMartingales
