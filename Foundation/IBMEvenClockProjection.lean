import Foundation.IBMActualQuarticMoment
import Foundation.GaussianHermiteMartingale

/-! A nonzero EVEN clock channel in the actual IBM natural past.
Nontriviality is proved from an exact fourth-power IBM observation pairing. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMEvenClockProjection
open InfiniteGaussian IBMConstructedSources IBMTimeAveragedObservable
open IBMNaturalFiltrationObstruction IBMClockConditionalCorrection IBMActualQuarticMoment
open GaussianTimeSpaceHermite GaussianTimeHilbert SeparableHilbertEmbedding
attribute [local instance] timeHilbert_secondCountable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ibmValue clockPath

def clockQuadratic (t : ℝ≥0) : JointL2 := clockLift (brownianCore t 2 : GaussianL2)

theorem clockQuadratic_ae (t : ℝ≥0) :
    clockQuadratic t =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => (clockPath ω.2 t) ^ 2 - t := by
  filter_upwards [clockLift_coeFn (brownianCore t 2 : GaussianL2),
    (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
      (brownianCore_coeFn t 2),
    (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
      (clockPath_coordinate_ae t)] with ω hl hh hc
  simp only [Function.comp_def, value_two] at hh hc
  change clockLift (brownianCore t 2 : GaussianL2) ω = _
  rw [hl, hh, ← hc]

theorem clock_second (t : ℝ≥0) :
    (∫ ω, (clockPath ω t) ^ 2 ∂gaussianProduct) = t := by
  have h := (IBMOneTimeMixture.clock_law t).integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
  exact h.trans (IBMConditionalMoments.gaussian_zero_second t)

theorem clock_fourth (t : ℝ≥0) :
    (∫ ω, (clockPath ω t) ^ 4 ∂gaussianProduct) = 3 * (t : ℝ) ^ 2 := by
  rw [integral_congr_ae ((clockPath_coordinate_ae t).mono fun ω h => congrArg (fun x => x ^ 4) h)]
  change (∫ ω, (firstChaosEmbedding (hilbertEmbedding TimeHilbert (timeVector t)) ω) ^ 4
    ∂gaussianProduct) = _
  rw [IBMSourceMoments.firstChaos_fourth, LinearIsometry.norm_map, timeVector_norm_sq]

theorem quadratic_fourth_pairing (t : ℝ≥0) :
    inner ℝ (clockQuadratic t) (fourthClass t) = 6 * (t : ℝ) ^ 2 := by
  have he : (fun ω => inner ℝ (clockQuadratic t ω) (fourthClass t ω)) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => ((clockPath ω.2 t) ^ 2 - t) * (ibmValue t ω) ^ 4 := by
    filter_upwards [clockQuadratic_ae t, fourthClass_ae t] with ω hq hz
    rw [hq, hz, Real.inner_apply]
  have hi := (L2.integrable_inner (clockQuadratic t) (fourthClass t)).congr he
  rw [L2.inner_def, integral_congr_ae he]
  calc
    _ = ∫ ω, ∫ ξ, ((clockPath ω t) ^ 2 - t) * (ibmValue t (ξ, ω)) ^ 4
        ∂gaussianProduct ∂gaussianProduct := integral_prod_symm _ hi
    _ = ∫ ω, ((clockPath ω t) ^ 2 - t) * (3 * (clockPath ω t) ^ 2) ∂gaussianProduct := by
      apply integral_congr_ae
      exact ae_of_all _ fun ω => by
        change (∫ ξ, ((clockPath ω t) ^ 2 - t) * (ibmValue t (ξ, ω)) ^ 4
          ∂gaussianProduct) = ((clockPath ω t) ^ 2 - t) * (3 * (clockPath ω t) ^ 2)
        rw [integral_const_mul, actual_conditional_fourth]
    _ = _ := by
      have hc (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp (fun ω => clockPath ω t) p gaussianProduct :=
        (GaussianTimeProcess.process_memLp t p hp).ae_eq (clockPath_coordinate_ae t).symm
      have h2 := (hc 2 (by norm_num)).integrable_sq
      have h4 : Integrable (fun ω => (clockPath ω t) ^ 4) gaussianProduct := by
        simpa only [Real.norm_eq_abs, (show Even 4 by decide).pow_abs] using
          (hc 4 (by norm_num)).integrable_norm_pow'
      have hp (x : ℝ) : (x ^ 2 - t) * (3 * x ^ 2) = 3 * x ^ 4 - (3 * t) * x ^ 2 := by ring
      simp_rw [hp]
      rw [integral_sub (h4.const_mul 3) (h2.const_mul (3 * t)),
        integral_const_mul, integral_const_mul, clock_fourth, clock_second]
      ring

theorem conditional_quadratic_ne_zero (T t : ℝ≥0) (ht : 0 < t) (hT : t ≤ T) :
    (condExpL2 ℝ ℝ (naturalFiltration.le T) (clockQuadratic t) : JointL2) ≠ 0 := by
  intro hz
  let : CompleteSpace (past T) := (past_closed T).completeSpace_coe
  have hf := fourthClass_mem_past hT
  have he : inner ℝ (condExpL2 ℝ ℝ (naturalFiltration.le T) (clockQuadratic t) : JointL2)
      (fourthClass t) = inner ℝ (clockQuadratic t) (fourthClass t) :=
    (past T).inner_orthogonalProjectionOnto_eq_of_mem_right ⟨fourthClass t, hf⟩ (clockQuadratic t)
  rw [hz, inner_zero_left, quadratic_fourth_pairing] at he
  have hp : 0 < 6 * (t : ℝ) ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos (show 0 < (t : ℝ) from ht))
  linarith

end OperatorDerivativeRewrite.Foundation.IBMEvenClockProjection
