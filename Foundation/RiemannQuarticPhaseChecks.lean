import Foundation.RiemannQuarticArithmeticJets
import Foundation.RiemannQuarticIntervalChecks

/-! Concrete checks of actual arithmetic phase coefficients, including order16. -/
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticPhaseChecks
open RiemannQuarticDyadic RiemannQuarticIntervalExp RiemannQuarticIntervalChecks
open RiemannQuarticPhaseJets RiemannQuarticTaylorJets

def expTwo : Box := scaledExpHorner (rational 2 96) 96 32 4

def phaseAtHalf (n : ℕ) : Box :=
  phaseJet (rational (1/2) 96) expTwo (piBox 96) (rational 9 96) 1 96 n

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Reduce the actual nested exponential/pi phase calculation and coefficient16.
theorem phaseAtHalf_check :
    inside (phaseAtHalf 0) (-19) (-18)=true ∧
      inside (phaseAtHalf 1) (-81) (-79)=true ∧
      inside (phaseAtHalf 16) (-1/100) (-1/1000)=true := by
  decide +kernel

theorem phaseAtHalf_mem (n : ℕ) : coefficient (phase 1 9) n (1/2) ∈ phaseAtHalf n := by
  have hu : (1/2 : ℝ) ∈ rational (1/2) 96 := by simpa using rational_mem (1/2) 96
  have h2 : (2 : ℝ) ∈ rational 2 96 := by simpa using rational_mem 2 96
  have he2 : Real.exp (2 : ℝ) ∈ expTwo :=
    scaledExpHorner_mem h2 96 32 4 (by norm_num) (by norm_num)
  have he : Real.exp (4*(1/2 : ℝ)) ∈ expTwo := by norm_num; exact he2
  have ha : (9 : ℝ) ∈ rational 9 96 := by simpa using rational_mem 9 96
  exact phaseJet_mem hu he (pi_mem 96) ha 1 96 n

theorem phaseAtHalf_bounds :
    ((-19 : ℝ) ≤ phase 1 9 (1/2) ∧ phase 1 9 (1/2) ≤ -18) ∧
      ((-81 : ℝ) ≤ coefficient (phase 1 9) 1 (1/2) ∧
        coefficient (phase 1 9) 1 (1/2) ≤ -79) ∧
      ((-1/100 : ℝ) ≤ coefficient (phase 1 9) 16 (1/2) ∧
        coefficient (phase 1 9) 16 (1/2) ≤ -1/1000) := by
  have h0 := inside_spec phaseAtHalf_check.1 (phaseAtHalf_mem 0)
  have h1 := inside_spec phaseAtHalf_check.2.1 (phaseAtHalf_mem 1)
  have h16 := inside_spec phaseAtHalf_check.2.2 (phaseAtHalf_mem 16)
  norm_num only [Rat.cast_neg, Rat.cast_ofNat, Rat.cast_div, Rat.cast_one, coefficient_zero] at h0 h1 h16
  refine ⟨h0, h1, ?_⟩
  simpa only [neg_div] using h16

end OperatorDerivativeRewrite.Foundation.RiemannQuarticPhaseChecks
