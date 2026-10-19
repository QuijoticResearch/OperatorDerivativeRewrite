import Foundation.IBMFullSchwartzHeatFubini
import Foundation.BrownianClockWeightedEnergy

/-! Actual source-L2-valued clock curvature, its time/clock Fubini domain,
and the heat identity for the genuine clock mean. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMFullSchwartzClockMean
open InfiniteGaussian IBMConstructedSources IBMClockHeatPotential IBMFullSchwartzHeatHalfLine
open IBMFullSchwartzHeatFubini IBMReflectedClockMean IBMFullSchwartzTerminal
open IBMSchwartzSourceSecondDerivative IBMSchwartzSourceContinuity IBMSchwartzSecondProjection

variable (g : SchwartzMap ℝ ℝ) (a : ℝ)

def clockValue (n : ℕ) (t : ℝ≥0) (ω : SampleSpace) : GaussianL2 :=
  (mollifiedClass g a n |clockPath ω t|)

def timeValue (n : ℕ) (p : ℝ × SampleSpace) : GaussianL2 := clockValue g a n p.1.toNNReal p.2

theorem timeValue_stronglyMeasurable (n : ℕ) : StronglyMeasurable (timeValue g a n) :=
  (IBMSchwartzSourceContinuity.mollifiedClass_continuous g a n).stronglyMeasurable.comp_measurable
    (continuous_abs.measurable.comp BrownianClockWeightedEnergy.sigma_measurable)

theorem clockValue_integrable (n : ℕ) (t : ℝ≥0) : Integrable (clockValue g a n t) gaussianProduct := by
  obtain ⟨C,hC,hc⟩ := IBMSchwartzBochnerDomain.mollified_growth g a n
  apply (((IBMClockCubicJointL2.clock_cubic_growth_memLp t).integrable (by norm_num)).const_mul C).mono'
    ((IBMSchwartzSourceContinuity.mollifiedClass_continuous g a n).stronglyMeasurable.comp_measurable
      (IBMQuarticClockTerminal.clockPosition_measurable t)).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    have hh := hc |clockPath ω t|
    rw [abs_abs] at hh
    have hp : (1+|clockPath ω t|)^2 ≤ (1+|clockPath ω t|)^3 :=
      pow_le_pow_right₀ (by linarith [abs_nonneg (clockPath ω t)]) (by norm_num)
    exact hh.trans (mul_le_mul_of_nonneg_left hp hC)

theorem clockValue_mean (n : ℕ) (t : ℝ≥0) (ht : 0 < t) :
    (∫ ω, clockValue g a n t ω ∂gaussianProduct) = ∫ r in Ioi 0, heatValue g a n (t,r) := by
  have he := reflected_clock_integral
    (fun r => (mollifiedClass g a n r))
    (IBMSchwartzSourceContinuity.mollifiedClass_continuous g a n).stronglyMeasurable t ht (clockValue_integrable g a n t)
  have hh : (fun r => heatValue g a n (t,r)) = fun r => (2 : ℝ) •
      (heatKernel t r • (mollifiedClass g a n r)) := by
    funext r
    exact mul_smul _ _ _
  rw [hh, integral_smul]
  exact he

theorem clockValue_norm_mean (n : ℕ) (t : ℝ≥0) (ht : 0 < t) :
    (∫ ω, ‖clockValue g a n t ω‖ ∂gaussianProduct) = ∫ r in Ioi 0, ‖heatValue g a n (t,r)‖ := by
  have he := reflected_clock_integral
    (fun r => ‖(mollifiedClass g a n r)‖)
    (IBMSchwartzSourceContinuity.mollifiedClass_continuous g a n).norm.stronglyMeasurable t ht
    (clockValue_integrable g a n t).norm
  have hh (r : ℝ) : ‖heatValue g a n (t,r)‖ = 2 * (heatKernel t r *
      ‖(mollifiedClass g a n r)‖) := by
    rw [heatValue, norm_smul, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (IBMClockHeatOccupation.heatKernel_nonneg _ _))]
    ring
  simp_rw [hh]
  rw [integral_const_mul]
  simpa only [clockValue, smul_eq_mul] using he

theorem timeValue_integrable (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    Integrable (timeValue g a n) ((volume.restrict (Ioc 0 (T : ℝ))).prod gaussianProduct) := by
  apply (integrable_prod_iff (timeValue_stronglyMeasurable g a n).aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall fun s => clockValue_integrable g a n s.toNNReal, ?_⟩
  apply (heatValue_integrable g a n T hT).norm.integral_prod_left.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have he := clockValue_norm_mean g a n s.toNNReal (Real.toNNReal_pos.mpr hs.1)
  rw [Real.coe_toNNReal s hs.1.le] at he
  exact he.symm

def integratedValue (n : ℕ) (T : ℝ≥0) (ω : SampleSpace) : GaussianL2 :=
  ∫ s in 0..(T : ℝ), clockValue g a n s.toNNReal ω

theorem integratedValue_integrable (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    Integrable (integratedValue g a n T) gaussianProduct := by
  have hi := (timeValue_integrable g a n T hT).integral_prod_right
  change Integrable (fun ω => ∫ s in 0..(T : ℝ), clockValue g a n s.toNNReal ω) gaussianProduct
  simpa only [timeValue, intervalIntegral.integral_of_le T.coe_nonneg] using hi

/-- All integrals are actual Bochner integrals of constructed clock
curvature. The heat formula is proved by genuine product Fubini. -/
theorem clock_mean_eq_spatial (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    (∫ ω, integratedValue g a n T ω ∂gaussianProduct) =
      ∫ r in Ioi 0, potential T r •
        (mollifiedClass g a n r) := by
  have hs := integral_integral_swap (f := fun s ω => timeValue g a n (s,ω)) (timeValue_integrable g a n T hT)
  simp only [timeValue] at hs
  change (∫ ω, (∫ s in 0..(T : ℝ), clockValue g a n s.toNNReal ω) ∂gaussianProduct) = _
  simp_rw [intervalIntegral.integral_of_le T.coe_nonneg]
  rw [← hs]
  rw [← time_space_identity g a n T hT]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s ht
  have he := clockValue_mean g a n s.toNNReal (Real.toNNReal_pos.mpr ht.1)
  rw [Real.coe_toNNReal s ht.1.le] at he
  exact he

def correctedMean (n : ℕ) (T : ℝ≥0) : GaussianL2 :=
  (∫ ω, BrownianMassLimitIdentification.coordinateClass T ω ∂gaussianProduct) •
      spatialSlope g a n 0 +
    (1/2 : ℝ) • ∫ ω, integratedValue g a n T ω ∂gaussianProduct

theorem correctedMean_eq_terminal (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    correctedMean g a n T = terminal g a n T-spatial g a n 0 := by
  rw [correctedMean, clock_mean_eq_spatial g a n T hT]
  exact halfline_origin_cancellation g a n T hT

theorem correctedMean_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => correctedMean g a n T) atTop (𝓝 (terminalLimit g a T-g a • gaussianOne)) := by
  simp_rw [correctedMean_eq_terminal g a _ T hT]
  exact difference_tendsto g a T

end OperatorDerivativeRewrite.Foundation.IBMFullSchwartzClockMean
