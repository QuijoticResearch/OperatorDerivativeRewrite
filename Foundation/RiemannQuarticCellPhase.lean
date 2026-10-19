import Foundation.RiemannQuarticPhaseJets
import Foundation.RiemannQuarticIntervalChecks

/-! A uniform phase-exponential enclosure on an actual quadrature cell. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticCellPhase
open RiemannQuarticDyadic RiemannQuarticIntervalExp RiemannQuarticIntervalChecks
open RiemannQuarticPhaseJets RiemannQuarticTaylorJets

def cellU : Box := range (1/2) (51/100) 160
def cellE : Box := scaledExpHorner (mul (rational 4 160) cellU 160) 160 48 4
def cellF (i : ℕ) : Box := phaseJet cellU cellE (piBox 160) (rational 9 160) 1 160 i
def cellB : Box := scaledExpHorner (cellF 0) 160 48 6
def cellJ (n : ℕ) : Box :=
  phaseExpJet cellU cellE (piBox 160) (rational 9 160) cellB 1 160 n

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Check the complete rounded interval phase on the entire cell.
theorem phase_range_check : inside (cellF 0) (-21) (-17)=true := by
  decide +kernel

theorem uniform_inputs (u : ℝ) (hu : u ∈ Icc (1/2 : ℝ) (51/100)) :
    u ∈ cellU ∧ Real.exp (4*u) ∈ cellE ∧ phase 1 9 u ∈ cellF 0 ∧
      Real.exp (phase 1 9 u) ∈ cellB := by
  have huU : u ∈ cellU := by
    apply range_mem
    · simpa using hu.1
    · simpa using hu.2
  have h4 : (4 : ℝ) ∈ rational 4 160 := by simpa using rational_mem 4 160
  have hi := mul_mem h4 huU 160
  have hs : |4*u/((2^4 : ℕ) : ℝ)| ≤ 1 := by
    rw [abs_le]
    norm_num
    constructor <;> linarith [hu.1, hu.2]
  have he : Real.exp (4*u) ∈ cellE := scaledExpHorner_mem hi 160 48 4 (by norm_num) hs
  have ha : (9 : ℝ) ∈ rational 9 160 := by simpa using rational_mem 9 160
  have hf : phase 1 9 u ∈ cellF 0 := by
    simpa only [coefficient_zero, cellF] using phaseJet_mem huU he (pi_mem 160) ha 1 160 0
  have hr := inside_spec phase_range_check hf
  have hbsmall : |phase 1 9 u/((2^6 : ℕ) : ℝ)| ≤ 1 := by
    rw [abs_le]
    norm_num at hr ⊢
    constructor <;> linarith
  have hb : Real.exp (phase 1 9 u) ∈ cellB :=
    scaledExpHorner_mem hf 160 48 6 (by norm_num) hbsmall
  exact ⟨huU, he, hf, hb⟩

theorem uniform_jet (u : ℝ) (hu : u ∈ Icc (1/2 : ℝ) (51/100)) (n : ℕ) :
    coefficient (fun v => Real.exp (phase 1 9 v)) n u ∈ cellJ n := by
  have h := uniform_inputs u hu
  have ha : (9 : ℝ) ∈ rational 9 160 := by simpa using rational_mem 9 160
  exact phaseExpJet_mem h.1 h.2.1 (pi_mem 160) ha 1 160 n h.2.2.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Evaluate the actual order16 interval recurrence, with all rounding retained.
theorem sixteenth_check : inside (cellJ 16) (-(10^22)) (10^22)=true := by
  decide +kernel

theorem uniform_sixteenth (u : ℝ) (hu : u ∈ Icc (1/2 : ℝ) (51/100)) :
    |coefficient (fun v => Real.exp (phase 1 9 v)) 16 u| ≤ (10^22 : ℝ) := by
  have h := inside_spec sixteenth_check (uniform_jet u hu 16)
  apply abs_le.mpr
  norm_num at h ⊢
  exact h

theorem cell_taylor_error :
    |(∫ u in (1/2 : ℝ)..(51/100), Real.exp (phase 1 9 u))-
      (∫ u in (1/2 : ℝ)..(51/100),
        localPolynomial (fun v => Real.exp (phase 1 9 v)) 15 (101/200) u)| ≤
      (1/10^16 : ℝ) := by
  have hf : ContDiff ℝ ∞ (fun v => Real.exp (phase 1 9 v)) := by
    unfold phase
    fun_prop
  have he := local_integral_error (fun v => Real.exp (phase 1 9 v)) hf 15
    (101/200) (1/200) (10^22) (by norm_num) (by positivity) (by
      intro u hu
      apply uniform_sixteenth u
      norm_num at hu ⊢
      exact hu)
  norm_num at he
  exact he.trans (by norm_num)

end OperatorDerivativeRewrite.Foundation.RiemannQuarticCellPhase
