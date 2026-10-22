import Foundation.IBMRawEnergyMeasureObstruction
import Mathlib.Probability.ConditionalExpectation

/-! Actual whole-past prediction of the positive Brownian scenery.
This is the deterministic spatial forecasting step for the IBM germ question. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialSceneryForecast
open InfiniteGaussian IBMConstructedSources IBMContinuousScenery IBMRandomTimeHilbert
set_option backward.isDefEq.respectTransparency false

def scenery (r : ℝ≥0) (ω : SampleSpace) : ℝ := sceneryPath ω r

theorem scenery_measurable (r : ℝ≥0) : Measurable (scenery r) :=
  (ContinuousMap.measurable_eval (r : ℝ)).comp sceneryPath_measurable

def history : Filtration ℝ≥0 (inferInstance : MeasurableSpace SampleSpace) :=
  Filtration.natural scenery (fun r => (scenery_measurable r).stronglyMeasurable)

theorem scenery_adapted : StronglyAdapted history scenery :=
  Filtration.stronglyAdapted_natural (fun r => (scenery_measurable r).stronglyMeasurable)

theorem scenery_memLp (r : ℝ≥0) : MemLp (scenery r) 2 gaussianProduct :=
  positiveScenery_isBrownian.1.isGaussianProcess.hasGaussianLaw_eval r |>.memLp_two

theorem future_prediction {δ r : ℝ≥0} (hδr : δ ≤ r) :
    gaussianProduct[scenery r | history δ] =ᵐ[gaussianProduct] scenery δ := by
  have hi := positiveScenery_isBrownian.1.indepFun_shift δ |>.comp
    (measurable_pi_apply (r-δ)) measurable_id
  have hind : Indep (MeasurableSpace.comap (fun ω => scenery r ω - scenery δ ω) inferInstance)
      (history δ) gaussianProduct := by
    rw [history, Filtration.natural_eq_comap]
    simpa only [Function.comp_def, add_tsub_cancel_of_le hδr, id_eq, scenery,
      IndepFun, Kernel.IndepFun, Indep] using hi
  have hc := condExp_indep_eq ((scenery_measurable r).sub (scenery_measurable δ)).comap_le
    (history.le δ) (comap_measurable (fun ω => scenery r ω - scenery δ ω)).stronglyMeasurable hind
  have hmean := GaussianPredictableStep.integral_increment
    positiveScenery_isBrownian.1 δ r
  change (∫ ω, scenery r ω - scenery δ ω ∂gaussianProduct) = 0 at hmean
  rw [hmean] at hc
  have hs := condExp_of_stronglyMeasurable (history.le δ) (scenery_adapted δ)
    ((scenery_memLp δ).integrable (by norm_num))
  have hd := condExp_sub ((scenery_memLp r).integrable (by norm_num))
    ((scenery_memLp δ).integrable (by norm_num)) (history δ)
  filter_upwards [hc, hd] with ω hz he
  have h := he.symm.trans hz
  change gaussianProduct[scenery r | history δ] ω -
    gaussianProduct[scenery δ | history δ] ω = 0 at h
  rw [hs] at h
  exact sub_eq_zero.mp h

theorem prediction (δ r : ℝ≥0) :
    gaussianProduct[scenery r | history δ] =ᵐ[gaussianProduct] scenery (min r δ) := by
  rcases le_total r δ with h | h
  · rw [min_eq_left h]
    exact EventuallyEq.of_eq (condExp_of_stronglyMeasurable (history.le δ)
      ((scenery_adapted r).mono (history.mono h))
      ((scenery_memLp r).integrable (by norm_num)))
  · simpa only [min_eq_right h] using future_prediction h

theorem scenery_class_ae (r : ℝ≥0) :
    sourceScenery r =ᵐ[gaussianProduct] scenery r :=
  (sceneryPath_coordinate_ae (r : ℝ)).symm

theorem prediction_class (δ r : ℝ≥0) :
    (condExpL2 ℝ ℝ (history.le δ) (sourceScenery r) : GaussianL2) = sourceScenery (min r δ) := by
  apply Lp.ext
  have he := (Lp.memLp (sourceScenery r)).condExpL2_ae_eq_condExp (𝕜 := ℝ) (history.le δ)
  simpa only [Lp.toLp_coeFn, NNReal.coe_min] using he.trans
    ((condExp_congr_ae (scenery_class_ae r)).trans
      ((prediction δ r).trans (scenery_class_ae (min r δ)).symm))

theorem prediction_energy (δ r : ℝ≥0) :
    ‖(condExpL2 ℝ ℝ (history.le δ) (sourceScenery r) : GaussianL2)‖ ^ 2 = (min r δ : ℝ≥0) := by
  rw [prediction_class, sourceScenery_norm_sq]
  exact abs_of_nonneg (min r δ).coe_nonneg

theorem prediction_bound (δ r : ℝ≥0) :
    ‖(condExpL2 ℝ ℝ (history.le δ) (sourceScenery r) : GaussianL2)‖ ^ 2 ≤ (δ : ℝ) := by
  rw [prediction_energy]
  exact_mod_cast min_le_right r δ

end OperatorDerivativeRewrite.Foundation.IBMSpatialSceneryForecast
