import Foundation.IBMSchwartzSourceZeroJoint
import Foundation.GaussianPredictableChaosCore

/-! Uniform eventual clock-chaos tails for the actual whole source-zero
component, and convergence of its sum with the verified (2,0) block. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzSourceZeroTails
open InfiniteGaussian GaussianNumberSectors IBMSceneryAveragedCorrectionLimit
open IBMSchwartzSourceZeroJoint
open IBMQuarticJointRealization (jointMeasure jointSourceSector sourceSigma_le sourceLift)

theorem truncation_remainder_le (N : ℕ) (f h : GaussianL2) :
    ‖f-truncation N f‖ ≤ 2*‖f-h‖+‖h-truncation N h‖ := by
  have he : f-truncation N f = (f-h)+(h-truncation N h)+truncation N (h-f) := by
    rw [map_sub]
    abel
  rw [he]
  have hn := GaussianPredictableChaosCore.scalar_truncation_norm_le N (h-f)
  rw [norm_sub_rev h f] at hn
  exact (norm_add₃_le).trans (by linarith)

theorem averaged_uniform_clock_tail (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N0 n0 : ℕ, ∀ N ≥ N0, ∀ n ≥ n0,
      ‖(1/2 : ℝ) • averagedClass g a n T-
        truncation N ((1/2 : ℝ) • averagedClass g a n T)‖ < ε := by
  let h : GaussianL2 := (1/2 : ℝ) • averagedLimit g a T
  have hs := (averagedClass_tendsto g a T).const_smul (1/2 : ℝ)
  obtain ⟨n0,hn⟩ := Metric.tendsto_atTop.mp hs (ε/4) (by positivity)
  obtain ⟨N0,hN⟩ := Metric.tendsto_atTop.mp (truncation_tendsto h) (ε/2) (by positivity)
  refine ⟨N0,n0,fun N hNN n hnn => ?_⟩
  have h1 : ‖(1/2 : ℝ) • averagedClass g a n T-h‖ < ε/4 := by
    simpa only [dist_eq_norm] using hn n hnn
  have h2 : ‖h-truncation N h‖ < ε/2 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hN N hNN
  have hb := truncation_remainder_le N ((1/2 : ℝ) • averagedClass g a n T) h
  linarith

/-- The cutoff and mollifier thresholds are chosen independently before
both indices vary; this is stronger than fixed-clock-sector convergence. -/
theorem native_uniform_clock_tail (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N0 n0 : ℕ, ∀ N ≥ N0, ∀ n ≥ n0,
      ‖jointSourceSector 0 (IBMSchwartzLiteralJoint.literalClass g a n T)-
        clockLift (truncation N ((1/2 : ℝ) • averagedClass g a n T))‖ < ε := by
  obtain ⟨N0,n0,h⟩ := averaged_uniform_clock_tail g a T hε
  refine ⟨N0,n0,fun N hNN n hnn => ?_⟩
  rw [literal_source_zero_eq, ← map_sub, clockLift.norm_map]
  exact h N hNN n hnn

/-- This controlled partial sum shares one native product-L2 topology.
It leaves every source degree other than zero and the (2,0) block open. -/
theorem controlled_partial_sum_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n =>
      jointSourceSector 0 (IBMSchwartzLiteralJoint.literalClass g a n T)+
        (condExpL2 ℝ ℝ sourceSigma_le
          (jointSourceSector 2 (IBMSchwartzLiteralJoint.literalClass g a n T)) : Lp ℝ 2 jointMeasure))
      atTop (𝓝 (clockLift ((1/2 : ℝ) • averagedLimit g a T)+
        sourceLift (IBMSchwartzPrimitiveLimit.terminalLimit g a T))) :=
  (literal_source_zero_tendsto g a T).add (IBMSchwartzLiteralJoint.literal_native_block_tendsto_all g a T)

end OperatorDerivativeRewrite.Foundation.IBMSchwartzSourceZeroTails
