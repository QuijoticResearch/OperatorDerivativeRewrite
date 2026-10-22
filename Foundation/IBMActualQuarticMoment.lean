import Foundation.IBMOneTimeMixture
import Foundation.IBMClockEighthMoment
import Foundation.IBMClockInnovationObstruction

/-! Genuine L2 fourth-power IBM observations and their conditional moments.
These are actual continuous-process classes, not polynomial replacements. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMActualQuarticMoment
open InfiniteGaussian IBMConstructedSources IBMTimeAveragedObservable
open SeparableHilbertEmbedding FractionalSpectralKernel FractionalSpectralGeometry
attribute [local instance] spectralSpace_secondCountable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ibmValue clockPath

def sceneryDirection (r : ℝ) : CoefficientSpace :=
  hilbertEmbedding SpectralSpace (normalized (1 / 2) (by norm_num) (by norm_num) r)

theorem sceneryDirection_norm_sq (r : ℝ) : ‖sceneryDirection r‖ ^ 2 = |r| := by
  rw [sceneryDirection, LinearIsometry.norm_map]
  simpa only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one] using
    normalized_norm_sq (1 / 2) (by norm_num) (by norm_num) r

theorem scenery_firstChaos_ae (r : ℝ) :
    (fun ω => sceneryPath ω r) =ᵐ[gaussianProduct] firstChaosEmbedding (sceneryDirection r) :=
  sceneryPath_coordinate_ae r

theorem scenery_memLp (r : ℝ) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun ω => sceneryPath ω r) p gaussianProduct :=
  ((firstChaos_hasGaussianLaw (sceneryDirection r)).memLp hp).ae_eq
    (scenery_firstChaos_ae r).symm

theorem scenery_fourth (r : ℝ) :
    (∫ ω, (sceneryPath ω r) ^ 4 ∂gaussianProduct) = 3 * r ^ 2 := by
  rw [integral_congr_ae ((scenery_firstChaos_ae r).mono fun ω h => congrArg (fun x => x ^ 4) h),
    IBMSourceMoments.firstChaos_fourth, sceneryDirection_norm_sq, sq_abs]

theorem scenery_eighth (r : ℝ) :
    (∫ ω, (sceneryPath ω r) ^ 8 ∂gaussianProduct) = 105 * r ^ 4 := by
  rw [integral_congr_ae ((scenery_firstChaos_ae r).mono fun ω h => congrArg (fun x => x ^ 8) h),
    IBMClockEighthMoment.firstChaos_eighth_integral]
  rw [show ‖sceneryDirection r‖ ^ 8 = (‖sceneryDirection r‖ ^ 2) ^ 4 by ring,
    sceneryDirection_norm_sq, (show Even 4 by decide).pow_abs]

theorem actual_conditional_fourth (t : ℝ≥0) (ω : SampleSpace) :
    (∫ ξ, (ibmValue t (ξ, ω)) ^ 4 ∂gaussianProduct) = 3 * (clockPath ω t) ^ 2 := by
  simp only [ibmValue_eq]
  rw [scenery_fourth, sq_abs]

theorem actual_conditional_eighth (t : ℝ≥0) (ω : SampleSpace) :
    (∫ ξ, (ibmValue t (ξ, ω)) ^ 8 ∂gaussianProduct) = 105 * (clockPath ω t) ^ 4 := by
  simp only [ibmValue_eq]
  rw [scenery_eighth, (show Even 4 by decide).pow_abs]

theorem actual_eighth_integrable (t : ℝ≥0) :
    Integrable (fun ω => (ibmValue t ω) ^ 8) IBMSourceLaws.jointMeasure := by
  have hm := (IBMNaturalFiltrationObstruction.point_stronglyMeasurable t).measurable.pow_const 8
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall fun ω => ?_, ?_⟩
  · simpa only [ibmValue_eq, Real.norm_eq_abs, (show Even 8 by decide).pow_abs] using
      (scenery_memLp |clockPath ω t| 8 (by norm_num)).integrable_norm_pow'
  · have he (ω : SampleSpace) :
        (∫ ξ, ‖(ibmValue t (ξ, ω)) ^ 8‖ ∂gaussianProduct) = 105 * (clockPath ω t) ^ 4 := by
      calc
        _ = ∫ ξ, (ibmValue t (ξ, ω)) ^ 8 ∂gaussianProduct :=
          integral_congr_ae (ae_of_all _ fun ξ => Real.norm_of_nonneg (by positivity))
        _ = _ := actual_conditional_eighth t ω
    simp_rw [he]
    have hc : MemLp (fun ω => clockPath ω t) 4 gaussianProduct :=
      (GaussianTimeProcess.process_memLp t 4 (by norm_num)).ae_eq (clockPath_coordinate_ae t).symm
    have hi : Integrable (fun ω => (clockPath ω t) ^ 4) gaussianProduct := by
      simpa only [Real.norm_eq_abs, (show Even 4 by decide).pow_abs] using hc.integrable_norm_pow'
    exact hi.const_mul 105

theorem fourth_memLp (t : ℝ≥0) :
    MemLp (fun ω => (ibmValue t ω) ^ 4) 2 IBMSourceLaws.jointMeasure := by
  apply (memLp_two_iff_integrable_sq_norm
    ((IBMNaturalFiltrationObstruction.point_stronglyMeasurable t).pow 4).aestronglyMeasurable).mpr
  simpa only [Real.norm_eq_abs, sq_abs, Pi.pow_apply, ← pow_mul] using actual_eighth_integrable t

def fourthClass (t : ℝ≥0) : JointL2 := (fourth_memLp t).toLp _

theorem fourthClass_ae (t : ℝ≥0) : fourthClass t =ᵐ[IBMSourceLaws.jointMeasure]
    fun ω => (ibmValue t ω) ^ 4 := (fourth_memLp t).coeFn_toLp

theorem fourthClass_mem_past {t T : ℝ≥0} (ht : t ≤ T) :
    fourthClass t ∈ IBMNaturalFiltrationObstruction.past T := by
  have hm := ((IBMNaturalFiltrationObstruction.point_stronglyAdapted t).mono
    (IBMNaturalFiltrationObstruction.naturalFiltration.mono ht)).pow 4
  exact hm.aestronglyMeasurable.congr (fourthClass_ae t).symm

end OperatorDerivativeRewrite.Foundation.IBMActualQuarticMoment
