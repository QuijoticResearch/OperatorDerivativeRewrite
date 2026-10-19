import Foundation.RiemannQuarticIntervalExp

/-! Concrete interval results checked by kernel reduction, with real semantics. -/
open Inclusion
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticIntervalChecks
open RiemannQuarticDyadic RiemannQuarticIntervalExp

def inside (I : Box) (a b : ℚ) : Bool :=
  match I.lb, I.ub with
  | some lo, some hi => decide (a ≤ lo.toRat ∧ hi.toRat ≤ b)
  | _, _ => false

theorem inside_spec {I : Box} {a b : ℚ} {x : ℝ}
    (hc : inside I a b=true) (hx : x ∈ I) : (a : ℝ) ≤ x ∧ x ≤ (b : ℝ) := by
  change x ∈ I.map Dyadic.toReal at hx
  rw [Interval.mem_map_iff] at hx
  cases hL : I.lb with
  | bot => simp [inside, hL] at hc
  | coe lo =>
    cases hU : I.ub with
    | top => simp [inside, hL, hU] at hc
    | coe hi =>
      have h : a ≤ lo.toRat ∧ hi.toRat ≤ b := by simpa [inside, hL, hU] using hc
      exact ⟨(Rat.cast_le.mpr h.1).trans (hx.1 lo hL),
        (hx.2 hi hU).trans (Rat.cast_le.mpr h.2)⟩

def piBox (p : ℕ) : Box :=
  range (314159265358979323846/10^20) (314159265358979323847/10^20) p

theorem pi_mem (p : ℕ) : Real.pi ∈ piBox p := by
  apply range_mem
  · convert Real.pi_gt_d20.le using 1 <;> norm_num
  · convert Real.pi_lt_d20.le using 1 <;> norm_num

def exp32fifths : Box := scaledExpHorner (rational (32/5) 160) 160 65 4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Reduce the complete 160-bit finite-series arithmetic in the kernel.
theorem exp32fifths_check :
    inside exp32fifths (601845037/10^6) (601845039/10^6)=true := by
  decide +kernel

theorem exp32fifths_bounds :
    (601845037/10^6 : ℝ) ≤ Real.exp (32/5) ∧
      Real.exp (32/5) ≤ (601845039/10^6 : ℝ) := by
  have hx : (32/5 : ℝ) ∈ rational (32/5) 160 := by
    simpa using rational_mem (32/5) 160
  have he : Real.exp (32/5 : ℝ) ∈ exp32fifths :=
    scaledExpHorner_mem hx 160 65 4 (by norm_num) (by norm_num)
  simpa using inside_spec exp32fifths_check he

end OperatorDerivativeRewrite.Foundation.RiemannQuarticIntervalChecks
