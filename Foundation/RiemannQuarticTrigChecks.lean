import Foundation.RiemannQuarticIntervalTrig
import Foundation.RiemannQuarticIntervalChecks

/-! A concrete kernel-checked phase from the actual quartic-flow cutoff. -/
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticTrigChecks
open RiemannQuarticDyadic RiemannQuarticIntervalTrig RiemannQuarticIntervalChecks

def cutoffPhase : Box × Box := scaledTrig (rational (632083/6250) 96) 96 24 8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Check the complete rounded series and eight doubling steps in the kernel.
theorem cutoffPhase_check :
    inside cutoffPhase.1 (4/5) (9/10)=true ∧
      inside cutoffPhase.2 (1/2) (3/5)=true := by
  decide +kernel

theorem cutoffPhase_bounds :
    (4/5 : ℝ) ≤ Real.cos (632083/6250) ∧ Real.cos (632083/6250) ≤ (9/10 : ℝ) ∧
      (1/2 : ℝ) ≤ Real.sin (632083/6250) ∧ Real.sin (632083/6250) ≤ (3/5 : ℝ) := by
  have hx : (632083/6250 : ℝ) ∈ rational (632083/6250) 96 := by
    simpa using rational_mem (632083/6250) 96
  have he := scaledTrig_mem hx 96 24 8 (by norm_num) (by norm_num)
  have hc := inside_spec cutoffPhase_check.1 he.1
  have hs := inside_spec cutoffPhase_check.2 he.2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hc hs
  exact ⟨hc.1, hc.2, hs.1, hs.2⟩

end OperatorDerivativeRewrite.Foundation.RiemannQuarticTrigChecks
