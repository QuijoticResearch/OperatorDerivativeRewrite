import Foundation.IBMClockCubicJointL2

/-! Actual sixth clock moments and a finite-horizon polynomial majorant. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.IBMClockSixthMoment
open InfiniteGaussian IBMGaussianSteinMoments GaussianCubicGrowth
open GaussianTimeHilbert SeparableHilbertEmbedding GaussianHilbertProcess
attribute [local instance] timeHilbert_secondCountable

theorem firstChaos_sixth_integral (h : CoefficientSpace) :
    (∫ ω, (firstChaosEmbedding h ω)^6 ∂gaussianProduct)=15*‖h‖^6 := by
  rw [← cube_norm_sq,← real_inner_self_eq_norm_sq,L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [cube_coeFn h] with ω hω
  rw [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs,hω]
  ring

theorem clock_sixth_integral (t : ℝ≥0) :
    (∫ ω, |IBMConstructedSources.clockPath ω t|^6 ∂gaussianProduct)=15*(t : ℝ)^3 := by
  rw [integral_congr_ae ((IBMConstructedSources.clockPath_coordinate_ae t).mono
    fun ω hω => congrArg (fun x : ℝ => |x|^6) hω)]
  simp only [(show Even 6 by decide).pow_abs]
  change (∫ ω, (firstChaosEmbedding (hilbertEmbedding TimeHilbert (timeVector t)) ω)^6
    ∂gaussianProduct)= _
  rw [firstChaos_sixth_integral,LinearIsometry.norm_map,
    show ‖timeVector t‖^6=(‖timeVector t‖^2)^3 by ring,timeVector_norm_sq]

theorem one_add_abs_sixth_bound (x : ℝ) : (1+|x|)^6 ≤ 64*(1+|x|^6) := by
  by_cases h : |x| ≤ 1
  · have hp : (1+|x|)^6 ≤ (2 : ℝ)^6 := by gcongr <;> linarith
    nlinarith [pow_nonneg (abs_nonneg x) 6]
  · have h1 : 1 ≤ |x| := le_of_lt (lt_of_not_ge h)
    have hp : (1+|x|)^6 ≤ (2*|x|)^6 := by gcongr <;> linarith
    nlinarith

theorem clock_growth_sixth_integral_le (t : ℝ≥0) :
    (∫ ω, (1+|IBMConstructedSources.clockPath ω t|)^6 ∂gaussianProduct) ≤
      64*(1+15*(t : ℝ)^3) := by
  have hi : Integrable (fun ω => (1+|IBMConstructedSources.clockPath ω t|)^6) gaussianProduct := by
    have h := (IBMClockCubicJointL2.clock_cubic_growth_memLp t).integrable_sq
    simpa only [← pow_mul] using h
  have hj : Integrable (fun ω => |IBMConstructedSources.clockPath ω t|^6) gaussianProduct :=
    (IBMClockCubicJointL2.clock_memLp_six t).integrable_norm_pow (by norm_num)
  have hb := integral_mono hi (((integrable_const (1 : ℝ)).add hj).const_mul 64)
    (fun ω => one_add_abs_sixth_bound (IBMConstructedSources.clockPath ω t))
  simpa only [Pi.add_apply,integral_const_mul,integral_add (integrable_const (1 : ℝ)) hj,
    integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul,clock_sixth_integral] using hb

end OperatorDerivativeRewrite.Foundation.IBMClockSixthMoment
