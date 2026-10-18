import Foundation.IBMOriginalBoundaryResidual
import Foundation.GaussianChaosDecomposition

/-! Reuse the existing projections for the actual weighted Schwartz F2
residual. This does not identify a physical multiple-Wiener kernel. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzBoundaryChaosReuse
open InfiniteGaussian GaussianNumberSectors IBMOriginalBoundaryResidual IBMCorrectionStein

/-- Every fixed clock sector inherits the already proved genuine F2 limit. -/
theorem residual_projection_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) (k : ℕ) :
    Tendsto (fun n => projection k ((originalPathIntegral_memLp g a n T).toLp _)) atTop
      (𝓝 (jet g 2 a • projection k (BrownianMassLimitIdentification.coordinateClass T))) := by
  have he := (projection k).continuous.tendsto _ |>.comp (originalPathIntegral_tendsto g a T)
  simpa only [Function.comp_def, map_smul] using he

/-- Retain the one-half coefficient of the Itô--Tanaka curvature term. -/
theorem half_residual_projection_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) (k : ℕ) :
    Tendsto (fun n => projection k ((1/2 : ℝ) •
      (originalPathIntegral_memLp g a n T).toLp _)) atTop
      (𝓝 ((jet g 2 a / 2) • projection k (BrownianMassLimitIdentification.coordinateClass T))) := by
  have he := (projection k).continuous.tendsto _ |>.comp
    (half_originalPathIntegral_tendsto g a T)
  simpa only [Function.comp_def, map_smul] using he

/-- No extra sector estimate is needed for this fixed-sector passage. -/
theorem residual_projection_error (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) (k : ℕ) :
    ‖projection k ((originalPathIntegral_memLp g a n T).toLp _) -
      jet g 2 a • projection k (BrownianMassLimitIdentification.coordinateClass T)‖ ≤
      ‖(originalPathIntegral_memLp g a n T).toLp _ -
        jet g 2 a • BrownianMassLimitIdentification.coordinateClass T‖ := by
  rw [← map_smul, ← map_sub]
  exact projection_norm_le k _

end OperatorDerivativeRewrite.Foundation.IBMSchwartzBoundaryChaosReuse
