import Foundation.IBMMollifiedProcess
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-! A concrete normalized smooth spatial approximate identity for the
conditional mollified IBM construction. -/
noncomputable section
open MeasureTheory Filter
open scoped Convolution Topology NNReal ContDiff

namespace OperatorDerivativeRewrite.Foundation.IBMMollifier
open InfiniteGaussian

/-- Smooth bump of inner radius `1/(n+1)` and outer radius `2/(n+1)`. -/
def bump (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := 1 / ((n : ℝ) + 1)
  rOut := 2 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : 0 < (n : ℝ) + 1 := by positivity
    exact (div_lt_div_iff₀ h h).2 (by nlinarith)

/-- Normalized nonnegative smooth compactly supported kernel. -/
def kernel (n : ℕ) : ℝ → ℝ := (bump n).normed volume

theorem kernel_nonneg (n : ℕ) (x : ℝ) : 0 ≤ kernel n x :=
  (bump n).nonneg_normed x

theorem kernel_integral (n : ℕ) : ∫ x, kernel n x = 1 :=
  (bump n).integral_normed

theorem kernel_smooth (n : ℕ) : ContDiff ℝ ∞ (kernel n) :=
  (bump n).contDiff_normed

theorem kernel_compactSupport (n : ℕ) : HasCompactSupport (kernel n) :=
  (bump n).hasCompactSupport_normed

theorem bump_outer_tendsto_zero :
    Tendsto (fun n : ℕ => (bump n).rOut) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  simpa [bump, div_eq_mul_inv, mul_comm] using h

/-- For each continuous scenery path, its normalized convolution converges
at every fixed spatial point. -/
theorem convolution_tendsto (X : ℝ → ℝ) (hX : Continuous X) (r : ℝ) :
    Tendsto (fun n : ℕ => IBMMollifiedScenery.U (kernel n) X r) atTop (𝓝 (X r)) := by
  exact ContDiffBump.convolution_tendsto_right_of_continuous
    (φ := bump) bump_outer_tendsto_zero hX r

/-- Pointwise convergence of the random-time mollified composition to the
supplied continuous source composition, at each fixed time and sample. -/
theorem process_tendsto (S : ℝ → SampleSpace → ℝ)
    (C : ℝ≥0 → SampleSpace → ℝ)
    (hS : ∀ w : SampleSpace, Continuous (fun r => S r w))
    (t : ℝ≥0) (w : IBMSourceLaws.JointSample) :
    Tendsto (fun n : ℕ => IBMMollifiedProcess.Z (kernel n) S C t w)
      atTop (𝓝 (S |C t w.2| w.1)) := by
  exact convolution_tendsto (fun r => S r w.1) (hS w.1) |C t w.2|

end OperatorDerivativeRewrite.Foundation.IBMMollifier

