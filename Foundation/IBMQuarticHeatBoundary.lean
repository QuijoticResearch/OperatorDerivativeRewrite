import Foundation.IBMClockHeatOccupation
import Foundation.IBMQuarticSpatialWeakLimit

/-! Exact finite-radius boundary accounting for the actual quartic second
source channel. No decay at infinity or clock/source Fubini is presumed. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.IBMQuarticHeatBoundary
open InfiniteGaussian IBMClockGaussianTail IBMClockHeatPotential
open IBMQuarticSecondPrimitive IBMQuarticSecondGeometry IBMQuarticPrimitiveLimit
open IBMQuarticSpatialWeakLimit

def weightSlope (T r : ℝ) : ℝ := -4*tail (r/Real.sqrt T)

theorem potential_continuous {T : ℝ} (hT : 0 < T) : Continuous (potential T) :=
  continuous_iff_continuousAt.mpr fun r => (potential_spatial_hasDerivAt hT r).continuousAt

theorem weightSlope_continuous (T : ℝ) : Continuous (weightSlope T) :=
  (tail_continuous.comp (continuous_id.div_const _)).const_mul _

theorem heatKernel_spatial_continuous (T : ℝ) : Continuous (heatKernel T) :=
  (density_continuous.comp (continuous_id.div_const _)).div_const _

/-- The exact endpoint left over after two spatial integrations by parts. -/
def endpoint (n : ℕ) (T R : ℝ) : GaussianL2 :=
  potential T R • slope n R - weightSlope T R • primitive n R

theorem weighted_curvature_eq (n : ℕ) {T : ℝ} (hT : 0 < T) (R : ℝ) :
    (∫ r in 0..R, potential T r • GaussianNumberSectors.projection 2 (spatialQuartic n r)) =
      endpoint n T R - potential T 0 • slope n 0 - (2 : ℝ) • primitive n 0 +
        (4 : ℝ) • ∫ r in 0..R, heatKernel T r • primitive n r := by
  have hd : ∀ r, HasDerivAt (potential T) (weightSlope T r) r :=
    fun r => potential_spatial_hasDerivAt hT r
  have hdd : ∀ r, HasDerivAt (weightSlope T) (4*heatKernel T r) r :=
    fun r => slope_spatial_hasDerivAt hT r
  have h₁ := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (potential_continuous hT).continuousOn (slope_continuous n).continuousOn
    (fun r _ => hd r) (fun r _ => slope_hasDerivAt n r)
    ((weightSlope_continuous T).intervalIntegrable 0 R)
    ((projected_continuous n).intervalIntegrable 0 R)
  have h₂ := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (weightSlope_continuous T).continuousOn (primitive_continuous n).continuousOn
    (fun r _ => hdd r) (fun r _ => primitive_hasDerivAt n r)
    (((heatKernel_spatial_continuous T).const_mul 4).intervalIntegrable 0 R)
    ((slope_continuous n).intervalIntegrable 0 R)
  rw [h₁, h₂]
  have hz : weightSlope T 0 = -2 := by norm_num [weightSlope, tail_zero]
  simp only [hz, mul_smul, intervalIntegral.integral_smul]
  unfold endpoint
  module

/-- The origin cancels exactly at finite radius, retaining the infinity
endpoint explicitly rather than declaring it zero. -/
theorem finite_origin_cancellation (n : ℕ) {T : ℝ} (hT : 0 < T) (R : ℝ) :
    (potential T 0/2) • slope n 0 +
      (1/2 : ℝ) • (∫ r in 0..R,
        potential T r • GaussianNumberSectors.projection 2 (spatialQuartic n r)) =
      (2 : ℝ) • (∫ r in 0..R, heatKernel T r • primitive n r) - primitive n 0 +
        (1/2 : ℝ) • endpoint n T R := by
  rw [weighted_curvature_eq n hT R]
  module

end OperatorDerivativeRewrite.Foundation.IBMQuarticHeatBoundary
