import Foundation.IBMAveragedBulkClock
import Foundation.GaussianChaosDecomposition

/-! Strong whole-clock L² closure of the full scenery-averaged Schwartz
correction. Joint time/scenery Fubini is not silently assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSceneryAveragedCorrectionLimit
open InfiniteGaussian IBMCorrectionStein IBMOriginalBoundaryResidual IBMAveragedBulkClock
open IBMBoundaryAveragedCoefficient IBMConstructedSources IBMGaussianSteinMoments

def bulkClass (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) : GaussianL2 :=
  clockClass (sourceAverage_continuous (shiftedJet_lipschitz g a 4) n)
    (IBMBoundaryLayerRemainder.sourceAverage_bound (shiftedJet_lipschitz g a 4)
      (shiftedJet_bound g a 4) n) T

def bulkLimit (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) : GaussianL2 :=
  clockClass (baseAverage_continuous (shiftedJet_lipschitz g a 4))
    (baseAverage_bound (shiftedJet_lipschitz g a 4) (shiftedJet_bound g a 4)) T

def averagedClass (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) : GaussianL2 :=
  (originalPathIntegral_memLp g a n T).toLp _ + (1/4 : ℝ) • bulkClass g a n T

def averagedLimit (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) : GaussianL2 :=
  jet g 2 a • BrownianMassLimitIdentification.coordinateClass T + (1/4 : ℝ) • bulkLimit g a T

def averagedPath (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0)
    (ω : SampleSpace) : ℝ :=
  ∫ t in 0..(T : ℝ), correction g a
    (tripleCoefficient n |clockPath ω t.toNNReal| 0)
    (tripleCoefficient n |clockPath ω t.toNNReal| 1)
    (tripleCoefficient n |clockPath ω t.toNNReal| 2)

theorem averagedPath_decomposition (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    (T : ℝ≥0) (ω : SampleSpace) :
    averagedPath g a n T ω = originalPathIntegral g a n T ω +
      (1/4 : ℝ) * clockIntegral (sourceAverage (shiftedJet_lipschitz g a 4) n) T ω := by
  have he (r : ℝ) : correction g a (tripleCoefficient n r 0) (tripleCoefficient n r 1)
      (tripleCoefficient n r 2) = originalResidual g a n r +
      (1/4 : ℝ) * sourceAverage (shiftedJet_lipschitz g a 4) n r := by
    rw [originalResidual, sourceAverage_eq_integral]
    ring
  have hc : Continuous (fun t : ℝ => |clockPath ω t.toNNReal|) :=
    continuous_abs.comp ((clockPath ω).continuous.comp continuous_real_toNNReal)
  have hr : Continuous (originalResidual g a n) := by
    have heq : originalResidual g a n =
        IBMBoundaryResidualLimit.coefficient (shiftedJet_lipschitz g a 2)
          (shiftedJet_lipschitz g a 4) n := by funext r; exact originalResidual_identity g a n r
    rw [heq]
    exact IBMBoundaryResidualLimit.coefficient_continuous _ _ _
  have hi₁ : IntervalIntegrable (fun t : ℝ => originalResidual g a n |clockPath ω t.toNNReal|)
      volume 0 T := (hr.comp hc).intervalIntegrable 0 T
  have hi₂ : IntervalIntegrable (fun t : ℝ => (1/4 : ℝ) *
      sourceAverage (shiftedJet_lipschitz g a 4) n |clockPath ω t.toNNReal|) volume 0 T :=
    (continuous_const.mul ((sourceAverage_continuous _ _).comp hc)).intervalIntegrable 0 T
  unfold averagedPath
  simp_rw [he]
  rw [intervalIntegral.integral_add hi₁ hi₂, intervalIntegral.integral_const_mul]
  rfl

theorem averagedClass_coeFn (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    averagedClass g a n T =ᵐ[gaussianProduct] averagedPath g a n T := by
  filter_upwards [Lp.coeFn_add ((originalPathIntegral_memLp g a n T).toLp _)
    ((1/4 : ℝ) • bulkClass g a n T), (originalPathIntegral_memLp g a n T).coeFn_toLp,
    Lp.coeFn_smul (1/4 : ℝ) (bulkClass g a n T),
    clockClass_coeFn (sourceAverage_continuous (shiftedJet_lipschitz g a 4) n)
      (IBMBoundaryLayerRemainder.sourceAverage_bound (shiftedJet_lipschitz g a 4)
        (shiftedJet_bound g a 4) n) T] with ω hs hr hc hb
  change averagedClass g a n T ω = _
  rw [averagedClass, hs, Pi.add_apply, hc, Pi.smul_apply, smul_eq_mul, hr]
  change originalPathIntegral g a n T ω + (1/4 : ℝ) * bulkClass g a n T ω = _
  rw [bulkClass, hb, averagedPath_decomposition]

theorem averagedPath_memLp (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    MemLp (averagedPath g a n T) 2 gaussianProduct :=
  (Lp.memLp (averagedClass g a n T)).ae_eq (averagedClass_coeFn g a n T)

theorem averagedClass_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => averagedClass g a n T) atTop (𝓝 (averagedLimit g a T)) :=
  (originalPathIntegral_tendsto g a T).add
    ((bulkClass_tendsto (shiftedJet_lipschitz g a 4) (shiftedJet_bound g a 4) T).const_smul (1/4 : ℝ))

theorem clockProjection_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) (j : ℕ) :
    Tendsto (fun n => GaussianNumberSectors.projection j (averagedClass g a n T)) atTop
      (𝓝 (GaussianNumberSectors.projection j (averagedLimit g a T))) :=
  (GaussianNumberSectors.projection j).continuous.tendsto _ |>.comp (averagedClass_tendsto g a T)

end OperatorDerivativeRewrite.Foundation.IBMSceneryAveragedCorrectionLimit
