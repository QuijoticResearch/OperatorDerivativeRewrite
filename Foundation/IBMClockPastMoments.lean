import Foundation.IBMSpatialPointClockObstruction
import Foundation.IBMSourceMoments

/-! Actual future Brownian powers against arbitrary integrable raw-past
coefficients. These are inputs to a fourth-moment estimate, not its assumption. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockPastMoments
open InfiniteGaussian GaussianTimeProcess GaussianPredictableStep

def delta (a b : ℝ≥0) (Y : SampleSpace) : ℝ := process b Y-process a Y

theorem power_integrable (a b : ℝ≥0) (k : ℕ) :
    Integrable (fun Y => delta a b Y ^ k) gaussianProduct := by
  have hm := (process_memLp b (k : ℝ≥0∞) (by simp)).sub
    (process_memLp a (k : ℝ≥0∞) (by simp))
  apply (integrable_norm_iff (hm.aestronglyMeasurable.pow k)).mp
  simpa only [norm_pow, Real.norm_eq_abs, delta, Pi.pow_apply, Pi.sub_apply, abs_pow]
    using hm.integrable_norm_pow'

theorem past_power (a b : ℝ≥0) (hab : a ≤ b) (k : ℕ) (A : SampleSpace → ℝ)
    (hA : Measurable[naturalFiltration a] A) (hi : Integrable A gaussianProduct) :
    Integrable (fun Y => A Y*delta a b Y^k) gaussianProduct ∧
      (∫ Y, A Y*delta a b Y^k ∂gaussianProduct) =
        (∫ Y, A Y ∂gaussianProduct)*(∫ Y, delta a b Y^k ∂gaussianProduct) := by
  obtain ⟨f,hf,he⟩ := (measurable_natural_iff_exists_pastCoefficient
    (fun t => (process_stronglyMeasurable t).measurable) a A).mp hA
  have hind : IndepFun A (fun Y => delta a b Y^k) gaussianProduct := by
    rw [he]
    exact (pastCoefficient_indep_increment process_isPreBrownian hab hf).comp
      measurable_id (measurable_id.pow_const k)
  exact ⟨hind.integrable_mul hi (power_integrable a b k),
    hind.integral_fun_mul_eq_mul_integral hi.aestronglyMeasurable
      (power_integrable a b k).aestronglyMeasurable⟩

theorem delta_first (a b : ℝ≥0) : (∫ Y, delta a b Y ∂gaussianProduct) = 0 :=
  integral_increment process_isPreBrownian a b

theorem delta_second (a b : ℝ≥0) (hab : a ≤ b) :
    (∫ Y, delta a b Y^2 ∂gaussianProduct) = (b : ℝ)-a :=
  integral_increment_sq process_isPreBrownian hab

theorem delta_third (a b : ℝ≥0) : (∫ Y, delta a b Y^3 ∂gaussianProduct) = 0 := by
  have hl := process_increment_hasLaw a b
  have hn := gaussianReal_neg hl
  have hp := hl.integral_comp (f := fun x : ℝ => x^3) (by fun_prop)
  have hm := hn.integral_comp (f := fun x : ℝ => x^3) (by fun_prop)
  simp only [neg_zero] at hm
  have he : (fun Y => (-(process b Y-process a Y))^3) =
      fun Y => -(process b Y-process a Y)^3 := funext fun Y => by ring
  change (∫ Y, (-(process b Y-process a Y))^3 ∂gaussianProduct) = _ at hm
  rw [he, integral_neg] at hm
  change (∫ Y, (process b Y-process a Y)^3 ∂gaussianProduct) = _ at hp
  change (∫ Y, (process b Y-process a Y)^3 ∂gaussianProduct) = 0
  linarith

theorem delta_fourth (a b : ℝ≥0) (hab : a ≤ b) :
    (∫ Y, delta a b Y^4 ∂gaussianProduct) = 3*((b : ℝ)-a)^2 :=
  IBMSourceMoments.clockBase_increment_fourth a b hab

end OperatorDerivativeRewrite.Foundation.IBMClockPastMoments
