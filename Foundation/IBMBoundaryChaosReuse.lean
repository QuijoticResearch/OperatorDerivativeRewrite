import Foundation.IBMBoundaryClockLimit
import Foundation.GaussianChaosDecomposition
import Foundation.IBMSpatialOverlap

/-! Direct reuse of the existing Gaussian projections for the actual IBM
boundary-clock limit. No joint bidegree construction or new chaos foundation
is introduced. The reflection test uses genuine scenery covariances. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMBoundaryChaosReuse
open InfiniteGaussian IBMBoundaryClockLimit GaussianNumberSectors

/-- Every existing clock chaos projection inherits the genuine L² limit. -/
theorem boundary_projection_tendsto (r : ℕ) (T : ℝ≥0) :
    Tendsto (fun n => projection r (clockMass n T)) atTop
      (𝓝 (projection r (BrownianTanakaResidual.mass T))) :=
  (projection r).continuous.tendsto _ |>.comp (clockMass_tendsto T)

/-- Project the actual Bochner time integral; no spatial occupation formula
or local-time field is assumed in this interchange. -/
theorem boundary_projection_integral (r n : ℕ) (T : ℝ≥0) :
    projection r (clockMass n T) =
      (1/2 : ℝ) • ∫ t in 0..(T : ℝ), projection r (curvatureValue n t.toNNReal) := by
  rw [clockMass, map_smul]
  congr 1
  have hc := (GaussianC2TimeWeighted.curvature_continuous
    (IBMVarianceClockGeometry.variance n) (IBMVarianceClockGeometry.variance_smooth n)
    (curvatureBound n) (curvature_bound n)).comp continuous_real_toNNReal
  exact ((projection r).intervalIntegral_comp_comm (hc.intervalIntegrable 0 T)).symm

theorem boundary_projection_error (r n : ℕ) (T : ℝ≥0) :
    ‖projection r (clockMass n T) - projection r (BrownianTanakaResidual.mass T)‖ ≤
      ‖clockMass n T - BrownianTanakaResidual.mass T‖ := by
  rw [← map_sub]
  exact projection_norm_le r _

/-- Fixed-scale clock expansion: completeness is reused, not postulated. -/
theorem boundary_clock_hasSum (n : ℕ) (T : ℝ≥0) :
    HasSum (fun r => projection r (clockMass n T)) (clockMass n T) :=
  projection_hasSum _

theorem boundary_limit_hasSum (T : ℝ≥0) :
    HasSum (fun r => projection r (BrownianTanakaResidual.mass T))
      (BrownianTanakaResidual.mass T) := projection_hasSum _

theorem boundary_limit_parseval (T : ℝ≥0) :
    HasSum (fun r => ‖projection r (BrownianTanakaResidual.mass T)‖^2)
      (‖BrownianTanakaResidual.mass T‖^2) := projection_hasSum_norm_sq _

/-- Explicit genuine-source test: the unreflected and reflected clock
conventions do not preserve the two-time covariance kernel. -/
theorem scenery_reflection_covariance_test :
    ProbabilityTheory.covariance (IBMSourceLaws.sceneryBase 1)
        (IBMSourceLaws.sceneryBase (-1)) gaussianProduct = 0 ∧
      ProbabilityTheory.covariance (IBMSourceLaws.sceneryBase |(1 : ℝ)|)
        (IBMSourceLaws.sceneryBase |(-1 : ℝ)|) gaussianProduct = 1 := by
  constructor <;> norm_num [IBMSourceLaws.sceneryBase_covariance]

end OperatorDerivativeRewrite.Foundation.IBMBoundaryChaosReuse
