import Foundation.IBMQuarticSourceGrowth
import Foundation.IBMClockSixthMoment

/-! Actual eighth clock moments and the finite-horizon majorant needed
for the unprojected quartic source correction. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMClockEighthMoment
open InfiniteGaussian IBMConstructedSources IBMQuarticSourceGrowth GaussianQuarticWick
open GaussianTimeHilbert SeparableHilbertEmbedding GaussianHilbertProcess
attribute [local instance] timeHilbert_secondCountable

theorem firstChaos_eighth_integral (h : CoefficientSpace) :
    (∫ ω, (firstChaosEmbedding h ω)^8 ∂gaussianProduct) = 105*‖h‖^8 := by
  rw [← quartic_norm_sq, ← real_inner_self_eq_norm_sq, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [quartic_coeFn h] with ω hω
  rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, hω]
  ring

theorem clock_eighth_integral (t : ℝ≥0) :
    (∫ ω, |clockPath ω t|^8 ∂gaussianProduct) = 105*(t : ℝ)^4 := by
  rw [integral_congr_ae ((clockPath_coordinate_ae t).mono
    fun ω hω => congrArg (fun x : ℝ => |x|^8) hω)]
  simp only [(show Even 8 by decide).pow_abs]
  change (∫ ω, (firstChaosEmbedding (hilbertEmbedding TimeHilbert (timeVector t)) ω)^8
    ∂gaussianProduct) = _
  rw [firstChaos_eighth_integral, LinearIsometry.norm_map,
    show ‖timeVector t‖^8 = (‖timeVector t‖^2)^4 by ring, timeVector_norm_sq]

theorem clock_memLp_eight (t : ℝ≥0) : MemLp (fun ω => clockPath ω t) 8 gaussianProduct :=
  (GaussianTimeProcess.process_memLp t 8 (by norm_num)).ae_eq (clockPath_coordinate_ae t).symm

theorem clock_fourth_growth_memLp (t : ℝ≥0) :
    MemLp (fun ω => (1+|clockPath ω t|)^4) 2 gaussianProduct := by
  have hf : MemLp (fun ω => 1+|clockPath ω t|) 8 gaussianProduct := by
    have hn : MemLp (fun ω => |clockPath ω t|) 8 gaussianProduct := by
      simpa only [Real.norm_eq_abs] using (clock_memLp_eight t).norm
    exact (memLp_const (1 : ℝ)).add hn
  have hp := hf.norm_rpow_div (4 : ℝ≥0∞)
  norm_num at hp
  convert hp using 1
  · funext ω
    rw [abs_of_nonneg (by positivity : 0 ≤ 1+|clockPath ω t|)]
  · rw [show (8 : ℝ≥0∞) = 2*4 by norm_num, div_eq_mul_inv, mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]

theorem one_add_abs_eighth_bound (x : ℝ) : (1+|x|)^8 ≤ 256*(1+|x|^8) := by
  by_cases h : |x| ≤ 1
  · have hp : (1+|x|)^8 ≤ (2 : ℝ)^8 := by gcongr <;> linarith
    nlinarith [pow_nonneg (abs_nonneg x) 8]
  · have hp : (1+|x|)^8 ≤ (2*|x|)^8 := by gcongr <;> linarith
    nlinarith

theorem clock_growth_eighth_integral_le (t : ℝ≥0) :
    (∫ ω, (1+|clockPath ω t|)^8 ∂gaussianProduct) ≤ 256*(1+105*(t : ℝ)^4) := by
  have hi : Integrable (fun ω => (1+|clockPath ω t|)^8) gaussianProduct := by
    simpa only [← pow_mul] using (clock_fourth_growth_memLp t).integrable_sq
  have hj : Integrable (fun ω => |clockPath ω t|^8) gaussianProduct :=
    (clock_memLp_eight t).integrable_norm_pow (by norm_num)
  have he := integral_mono hi (((integrable_const (1 : ℝ)).add hj).const_mul 256)
    (fun ω => one_add_abs_eighth_bound (clockPath ω t))
  simpa only [Pi.add_apply, integral_const_mul, integral_add (integrable_const (1 : ℝ)) hj,
    integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul,
    clock_eighth_integral] using he

theorem horizon_growth_integrable (T : ℝ≥0) :
    Integrable (fun p : ℝ × SampleSpace => (1+|clockPath p.2 p.1.toNNReal|)^8)
      ((volume.restrict (Set.Ioc 0 (T : ℝ))).prod gaussianProduct) := by
  have hm : Measurable (fun p : ℝ × SampleSpace => (1+|clockPath p.2 p.1.toNNReal|)^8) :=
    (measurable_const.add
      (continuous_abs.measurable.comp BrownianClockWeightedEnergy.sigma_measurable)).pow_const 8
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall fun s => ?_, ?_⟩
  · simpa only [← pow_mul] using (clock_fourth_growth_memLp s.toNNReal).integrable_sq
  · have hc : Continuous (fun s : ℝ => 256*(1+105*(s.toNNReal : ℝ)^4)) := by fun_prop
    apply hc.integrableOn_Ioc.mono' hm.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
    exact Eventually.of_forall fun s => by
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      have he : (∫ ω, ‖(1+|clockPath ω s.toNNReal|)^8‖ ∂gaussianProduct) =
          ∫ ω, (1+|clockPath ω s.toNNReal|)^8 ∂gaussianProduct :=
        integral_congr_ae (Eventually.of_forall fun ω => Real.norm_of_nonneg (by positivity))
      rw [he]
      exact clock_growth_eighth_integral_le s.toNNReal

end OperatorDerivativeRewrite.Foundation.IBMClockEighthMoment
