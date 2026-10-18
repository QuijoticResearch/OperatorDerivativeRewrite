import Foundation.IBMQuarticSecondChaos
import Foundation.IBMOriginalBoundaryResidual

/-! The verified second-source quartic kernel specializes to the actual
IBM covariance geometry, retaining the finite origin layer. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.IBMQuarticSecondGeometry
open InfiniteGaussian IBMQuarticSecondChaos GaussianNumberSectors GaussianTimeSpaceHermite
open IBMEvenCorrectionProjection IBMGaussianSteinMoments IBMContinuousScenery IBMMollifier

def spatialQuartic (n : ℕ) (r : ℝ) : GaussianL2 :=
  quarticCorrection (tripleCoefficient n r 0) (tripleCoefficient n r 1) (tripleCoefficient n r 2)

theorem spatialQuartic_coeFn (n : ℕ) (r : ℝ) :
    spatialQuartic n r =ᵐ[gaussianProduct] fun ω =>
      (1/2 : ℝ)*(IBMDyadicExtension.field n 0 ω r)^2*(IBMDyadicExtension.field n 1 ω r)^2 +
        (1/6 : ℝ)*(IBMDyadicExtension.field n 0 ω r)^3*IBMDyadicExtension.field n 2 ω r := by
  filter_upwards [quarticCorrection_coeFn (tripleCoefficient n r 0) (tripleCoefficient n r 1)
    (tripleCoefficient n r 2), IBMDyadicExtension.field_coordinate_ae n 0 r,
    IBMDyadicExtension.field_coordinate_ae n 1 r, IBMDyadicExtension.field_coordinate_ae n 2 r]
      with ω hc h0 h1 h2
  rw [h0, h1, h2, gaussianTriple_eq_firstChaos, gaussianTriple_eq_firstChaos,
    gaussianTriple_eq_firstChaos]
  exact hc

theorem coefficient_variance (n : ℕ) (r : ℝ) :
    ‖tripleCoefficient n r 0‖^2 = IBMVarianceClockGeometry.variance n r := by
  rw [← real_inner_self_eq_norm_sq, IBMOriginalBoundaryResidual.triple_inner]
  simp only [IBMJointMollifierGaussian.derivativeKernel, ite_true,
    real_inner_self_eq_norm_sq, IBMVarianceClockGeometry.variance, wholeLineVariance]

theorem coefficient_slope (n : ℕ) (r : ℝ) :
    2*inner ℝ (tripleCoefficient n r 0) (tripleCoefficient n r 1) =
      deriv (IBMVarianceClockGeometry.variance n) r := by
  rw [IBMVarianceClockGeometry.variance, wholeLineVariance_deriv (kernel n)
    (kernel_compactSupport n) ((kernel_smooth n).of_le (by norm_num)) r,
    IBMOriginalBoundaryResidual.triple_inner]
  simp [IBMJointMollifierGaussian.derivativeKernel]

theorem spatialQuartic_projection_two (n : ℕ) (r : ℝ) :
    projection 2 (spatialQuartic n r) =
      (kernel n r / 2) • (wick (tripleCoefficient n r 0) 2 : GaussianL2) +
      deriv (IBMVarianceClockGeometry.variance n) r •
        cross (tripleCoefficient n r 0) (tripleCoefficient n r 1) +
      (IBMVarianceClockGeometry.variance n r / 2) •
        ((wick (tripleCoefficient n r 1) 2 : GaussianL2) +
          cross (tripleCoefficient n r 0) (tripleCoefficient n r 2)) := by
  rw [spatialQuartic, quarticCorrection_projection_two,
    IBMOriginalBoundaryResidual.actual_bracket, coefficient_variance, coefficient_slope]

theorem positive_bulk_projection_two (n : ℕ) (r : ℝ) (hr : (bump n).rOut < r) :
    projection 2 (spatialQuartic n r) =
      cross (tripleCoefficient n r 0) (tripleCoefficient n r 1) +
      (IBMVarianceClockGeometry.variance n r / 2) •
        ((wick (tripleCoefficient n r 1) 2 : GaussianL2) +
          cross (tripleCoefficient n r 0) (tripleCoefficient n r 2)) := by
  have hk : kernel n r = 0 := by
    have hs : r ∉ Function.support (kernel n) := by
      rw [show Function.support (kernel n) = Metric.ball 0 (bump n).rOut from
        (bump n).support_normed_eq]
      simp only [Metric.mem_ball, Real.dist_eq, sub_zero,
        abs_of_pos (lt_trans (bump n).rOut_pos hr)]
      exact not_lt_of_ge hr.le
    simpa only [Function.mem_support, not_not] using hs
  rw [spatialQuartic_projection_two, hk, zero_div, zero_smul, zero_add,
    IBMVarianceClockGeometry.variance, IBMOffsetTranslation.concrete_wholeLineVariance_deriv n r hr,
    one_smul]

end OperatorDerivativeRewrite.Foundation.IBMQuarticSecondGeometry
