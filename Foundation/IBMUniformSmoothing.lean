import Foundation.IBMConcreteMollifier
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! Uniform Gaussian L² spatial approximation by the explicit IBM bumps. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace OperatorDerivativeRewrite.Foundation.IBMContinuousScenery
open IBMMollifier

theorem concreteMollifier_uniform_norm_le (n : ℕ) (x : ℝ) :
    ‖wholeLineScenery (kernel n) x - sourceScenery x‖ ≤
      Real.sqrt (bump n).rOut := by
  have hs := concreteMollifier_error_sq_le n x
  nlinarith [Real.sq_sqrt (bump n).rOut_pos.le,
    norm_nonneg (wholeLineScenery (kernel n) x - sourceScenery x),
    Real.sqrt_nonneg (bump n).rOut]

/-- The mollified Gaussian L² fields converge uniformly over all spatial
points, hence in particular over every compact set. This is uniform L²
convergence, not uniform convergence of sample paths. -/
theorem concreteMollifier_tendstoUniformly :
    TendstoUniformly (fun n x => wholeLineScenery (kernel n) x)
      sourceScenery atTop := by
  have hroot : Tendsto (fun n : ℕ => Real.sqrt (bump n).rOut)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp bump_outer_tendsto_zero
  refine Metric.tendstoUniformly_iff.2 ?_
  intro ε hε
  filter_upwards [hroot.eventually (eventually_lt_nhds hε)] with n hn x
  have hb := concreteMollifier_uniform_norm_le n x
  simpa only [dist_eq_norm, norm_sub_rev] using lt_of_le_of_lt hb hn

end OperatorDerivativeRewrite.Foundation.IBMContinuousScenery
