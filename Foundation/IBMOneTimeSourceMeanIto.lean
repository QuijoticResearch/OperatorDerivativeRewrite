import Foundation.GaussianDampedReflectedIto
import Foundation.IBMRawStepSources
import Foundation.IBMFourierRidgeCoefficients

/-! Physical-clock Ito identity for the ACTUAL scenery mean of a one-time IBM
Fourier observation. The process is B(|W|). This is a hidden-clock identity,
not an Ito formula for the unaveraged IBM observation or its observed filtration.
The equality is almost everywhere for each fixed horizon, not simultaneously
at all horizons. No new probability space or stochastic integral is introduced. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMOneTimeSourceMeanIto
open InfiniteGaussian GaussianTimeProcess GaussianPredictableFull

def sourceMean (a : ℝ) (T : ℝ≥0) (Y : SampleSpace) : ℝ :=
  ∫ X, Real.cos (a * IBMConstructedSources.ibmValue T (X,Y)) ∂gaussianProduct

theorem sourceMean_actual (a : ℝ) (T : ℝ≥0) :
    sourceMean a T =ᵐ[gaussianProduct] fun Y =>
      Real.exp (-(a ^ 2 / 2) * |IBMConstructedSources.clockPath Y T|) := by
  filter_upwards [IBMUnmollifiedSourceDerivative.actual_section_ae T,
    IBMConstructedSources.clockPath_coordinate_ae T] with Y hY hw
  have hmean := IBMFourierRidgeCoefficients.mode_mean 0 (a • IBMRawStepSources.clockDirection T Y)
  have hs : firstChaosEmbedding (a • IBMRawStepSources.clockDirection T Y) =
      a • firstChaosEmbedding (IBMRawStepSources.clockDirection T Y) := by
    simp
  have he : sourceMean a T Y =
      ∫ X, IBMFourierRidgeCoefficients.mode 0
        (firstChaosEmbedding (a • IBMRawStepSources.clockDirection T Y) X) ∂gaussianProduct := by
    apply integral_congr_ae
    filter_upwards [hY,
      Lp.coeFn_smul a (firstChaosEmbedding (IBMRawStepSources.clockDirection T Y))]
      with X hx hm
    change IBMConstructedSources.ibmValue T (X,Y) =
      firstChaosEmbedding (IBMRawStepSources.clockDirection T Y) X at hx
    rw [hs, hm]
    change Real.cos (a * IBMConstructedSources.ibmValue T (X,Y)) =
      Real.cos (0 + a * firstChaosEmbedding (IBMRawStepSources.clockDirection T Y) X)
    simpa only [zero_add] using congrArg (fun z : ℝ => Real.cos (a*z)) hx
  rw [he, hmean]
  simp only [Real.cos_zero, one_mul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    IBMRawStepSources.direction_norm_sq, ← hw]
  congr 1
  ring

def running (a : ℝ) (T : ℝ≥0) : fullPredictable :=
  GaussianDampedReflectedIto.running (a ^ 2 / 2) (by positivity) T

theorem sourceMean_ito (a : ℝ) (T : ℝ≥0) :
    (fun Y => sourceMean a T Y - 1) =ᵐ[gaussianProduct] fun Y =>
      itoIntegral (running a T) Y -
        (a ^ 2 / 2) * BrownianMassContinuousLimit.limitPath Y T +
        (a ^ 4 / 8) * ∫ s in (0 : ℝ)..(T : ℝ),
          Real.exp (-(a ^ 2 / 2) * |IBMConstructedSources.clockPath Y s.toNNReal|) := by
  filter_upwards [sourceMean_actual a T,
    GaussianDampedReflectedIto.actual_ito (a ^ 2 / 2) (by positivity) T] with Y hm hi
  rw [hm]
  change _ = itoIntegral (running a T) Y - _ + _ at hi
  have hrate : (a ^ 2 / 2) ^ 2 / 2 = a ^ 4 / 8 := by ring
  rw [hrate] at hi
  exact hi

end OperatorDerivativeRewrite.Foundation.IBMOneTimeSourceMeanIto
