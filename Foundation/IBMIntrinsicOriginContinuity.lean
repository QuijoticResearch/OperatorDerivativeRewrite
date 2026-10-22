import Foundation.IBMIntrinsicQuadraticMartingale

/-! The actual intrinsic IBM martingale DOES satisfy strong L2 continuity at
the origin. A generic continuous-observation counterexample cannot refute this. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicOriginContinuity
open IBMIntrinsicQuadraticMartingale IBMTimeAveragedObservable
set_option backward.isDefEq.respectTransparency false

theorem origin_norm_bound (t : ℝ≥0) : ‖(valueClass t : JointL2)‖ ≤ 2 * (t : ℝ) := by
  have h := valueClass_bound_sq t
  change ‖(valueClass t : JointL2)‖ ^ 2 ≤ 2 * (t : ℝ) ^ 2 at h
  nlinarith [norm_nonneg (valueClass t : JointL2), t.coe_nonneg]

theorem origin_tendsto :
    Tendsto (fun t : ℝ≥0 => (valueClass t : JointL2)) (𝓝 0) (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := squeeze_zero (fun t => norm_nonneg _) origin_norm_bound
    (by simpa using (NNReal.continuous_coe.tendsto (0 : ℝ≥0)).const_mul (2 : ℝ))
  simpa only [sub_zero] using ht

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicOriginContinuity
