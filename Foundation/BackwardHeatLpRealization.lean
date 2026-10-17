import Foundation.BoundedMovingLpProcess

/-! Actual continuous Lp realizations of backward higher-heat Fourier processes. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BackwardHeatLpRealization
open HigherHeatContinuousCylinders HigherHeatLpControls BoundedMovingLpProcess
open BackwardHeatMovingObstruction

variable (μ : Measure Path) [IsFiniteMeasure μ] (k : ℕ) [Fact (0 < k)]

def realization (m : ℕ) : ℝ → Lp ℂ (power k) μ := process μ k (backward m)

theorem realization_ae (m : ℕ) (t : ℝ) :
    realization μ k m t =ᵐ[μ] backward m t := process_ae μ k _ t

theorem realization_continuous (m : ℕ) : Continuous (realization μ k m) :=
  continuous_process μ k (backward m) (joint_continuous m) 1
    (fun t ω => scalar_norm_bound m (t, ω))

theorem realization_bound (m : ℕ) (t : ℝ) :
    ‖realization μ k m t‖ ≤ measureUnivNNReal μ ^ (power k).toReal⁻¹ := by
  simpa only [realization, mul_one] using process_norm_bound μ k (backward m) 1 zero_le_one
    (fun t ω => scalar_norm_bound m (t, ω)) t

theorem realization_memLp (m : ℕ) (q : ℝ≥0∞) (ν : Measure ℝ) [IsFiniteMeasure ν] :
    MemLp (realization μ k m) q ν :=
  process_memLp μ k (backward m) (joint_continuous m) 1 zero_le_one
    (fun t ω => scalar_norm_bound m (t, ω)) q ν

theorem probability_bound [IsProbabilityMeasure μ] (m : ℕ) (t : ℝ) :
    ‖realization μ k m t‖ ≤ 1 := by
  simpa [measureUnivNNReal] using realization_bound μ k m t

end OperatorDerivativeRewrite.Foundation.BackwardHeatLpRealization
