import Foundation.IBMQuarticHeatBoundary
import Foundation.BrownianMassNontriviality
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! Identify the actual Tanaka-mass mean with the origin coefficient in
the verified half-line heat boundary formula. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMClockOriginMean
open InfiniteGaussian IBMClockGaussianTail IBMClockHeatPotential

theorem density_even (x : ℝ) : density (-x) = density x := by
  simp [density, gaussianPDFReal]

theorem density_atTop : Tendsto density atTop (𝓝 0) := by
  have hp : Tendsto (fun x : ℝ => x^2/2) atTop atTop :=
    (tendsto_pow_atTop (by decide : 2 ≠ 0)).atTop_div_const (by norm_num)
  have he := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hp).const_mul
    ((Real.sqrt (2*Real.pi))⁻¹)
  change Tendsto (fun x : ℝ => density x) atTop (𝓝 0)
  simpa only [density, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero,
    neg_div, Function.comp_def, mul_zero] using he

theorem density_first_half_moment : (∫ x in Ioi 0, x*density x) = density 0 := by
  have he := integral_Ioi_of_hasDerivAt_of_nonpos'
    (fun x (_ : x ∈ Ici (0 : ℝ)) => density_hasDerivAt x)
    (fun x (hx : x ∈ Ioi (0 : ℝ)) =>
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx.le) (gaussianPDFReal_nonneg _ _ _))
    density_atTop
  simp only [neg_mul, integral_neg, zero_sub] at he
  linarith

theorem standard_absolute_mean : (∫ x, |x| ∂gaussianReal 0 1) = 2*density 0 := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  have he : (fun x : ℝ => gaussianPDFReal 0 1 x • |x|) =
      fun x => |x| * density |x| := by
    funext x
    simp only [smul_eq_mul, density]
    have hd : gaussianPDFReal 0 1 |x| = gaussianPDFReal 0 1 x := by
      simp [gaussianPDFReal, sq_abs]
    rw [hd, mul_comm]
  rw [he]
  exact (_root_.integral_comp_abs (f := fun y : ℝ => y*density y)).trans
    (by rw [density_first_half_moment])

theorem clock_absolute_mean (T : ℝ≥0) :
    (∫ ω, |IBMConstructedSources.clockPath ω T| ∂gaussianProduct) =
      2*Real.sqrt T*density 0 := by
  have hl : HasLaw (fun x : ℝ => Real.sqrt T*x) (gaussianReal 0 T) (gaussianReal 0 1) := by
    refine ⟨by fun_prop, ?_⟩
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · apply NNReal.eq
      simpa using Real.sq_sqrt T.coe_nonneg
  have hm : AEStronglyMeasurable (fun x : ℝ => |x|) (gaussianReal 0 T) := by fun_prop
  calc
    _ = ∫ x : ℝ, |x| ∂gaussianReal 0 T := (clock_hasLaw T).integral_comp hm
    _ = ∫ x : ℝ, |Real.sqrt T*x| ∂gaussianReal 0 1 := (hl.integral_comp hm).symm
    _ = 2*Real.sqrt T*density 0 := by
      simp only [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [integral_const_mul, standard_absolute_mean]
      ring

theorem coordinateMass_mean (T : ℝ≥0) :
    (∫ ω, BrownianMassLimitIdentification.coordinateClass T ω ∂gaussianProduct) =
      2*Real.sqrt T*density 0 := by
  unfold BrownianMassLimitIdentification.coordinateClass
  rw [integral_congr_ae (MemLp.coeFn_toLp (BrownianMassLimitIdentification.coordinate_memLp T)),
    BrownianMassNontriviality.expected_mass_eq,
    integral_congr_ae (BrownianTanakaApproximation.absoluteValue_coeFn T)]
  exact clock_absolute_mean T

theorem origin_coefficient_eq_mass_mean (T : ℝ≥0) :
    potential T 0/2 = ∫ ω,
      BrownianMassLimitIdentification.coordinateClass T ω ∂gaussianProduct := by
  rw [potential_zero, coordinateMass_mean]
  ring

/-- Exact actual origin normalization, with the finite-radius endpoint
still retained. This is not yet a random clock occupation identity. -/
theorem actual_origin_finite_cancellation (n : ℕ) (T : ℝ≥0) (hT : 0 < T) (R : ℝ) :
    (∫ ω, BrownianMassLimitIdentification.coordinateClass T ω ∂gaussianProduct) •
        IBMQuarticSecondPrimitive.slope n 0 +
      (1/2 : ℝ) • (∫ r in 0..R, potential T r •
        GaussianNumberSectors.projection 2 (IBMQuarticSecondGeometry.spatialQuartic n r)) =
      (2 : ℝ) • (∫ r in 0..R, heatKernel T r • IBMQuarticSecondPrimitive.primitive n r) -
        IBMQuarticSecondPrimitive.primitive n 0 +
        (1/2 : ℝ) • IBMQuarticHeatBoundary.endpoint n T R := by
  rw [← origin_coefficient_eq_mass_mean]
  exact IBMQuarticHeatBoundary.finite_origin_cancellation n (NNReal.coe_pos.mpr hT) R

end OperatorDerivativeRewrite.Foundation.IBMClockOriginMean
