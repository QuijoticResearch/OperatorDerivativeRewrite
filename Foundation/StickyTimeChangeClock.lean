import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith

/-! The deterministic invertible clock needed by a local-time construction of sticky diffusion. -/
noncomputable section
open Set
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.StickyTimeChangeClock
set_option backward.isDefEq.respectTransparency false

def clock (κ : ℝ≥0) (L : ℝ≥0 → ℝ≥0) (t : ℝ≥0) : ℝ≥0 := t + κ * L t

theorem clock_ge (κ : ℝ≥0) (L : ℝ≥0 → ℝ≥0) (t : ℝ≥0) : t ≤ clock κ L t := by
  exact le_add_of_nonneg_right bot_le

theorem clock_strictMono (κ : ℝ≥0) (L : ℝ≥0 → ℝ≥0) (hL : Monotone L) :
    StrictMono (clock κ L) := by
  intro s t hst
  exact add_lt_add_of_lt_of_le hst (mul_le_mul_of_nonneg_left (hL hst.le) bot_le)

theorem clock_continuous (κ : ℝ≥0) (L : ℝ≥0 → ℝ≥0) (hL : Continuous L) :
    Continuous (clock κ L) := continuous_id.add (continuous_const.mul hL)

theorem clock_surjective (κ : ℝ≥0) (L : ℝ≥0 → ℝ≥0)
    (hL : Continuous L) (h0 : L 0 = 0) : Function.Surjective (clock κ L) := by
  intro t
  have ht : t ∈ Icc (clock κ L 0) (clock κ L t) := by
    constructor
    · simpa only [clock, h0, mul_zero, add_zero] using (show 0 ≤ t from bot_le)
    · exact clock_ge κ L t
  obtain ⟨s,_,hs⟩ := intermediate_value_Icc (show 0 ≤ t from bot_le)
    (clock_continuous κ L hL).continuousOn ht
  exact ⟨s,hs⟩

def clockIso (κ : ℝ≥0) (L : ℝ≥0 → ℝ≥0)
    (hc : Continuous L) (hm : Monotone L) (h0 : L 0 = 0) : ℝ≥0 ≃o ℝ≥0 :=
  (clock_strictMono κ L hm).orderIsoOfSurjective (clock κ L) (clock_surjective κ L hc h0)

def inverseClock (κ : ℝ≥0) (L : ℝ≥0 → ℝ≥0)
    (hc : Continuous L) (hm : Monotone L) (h0 : L 0 = 0) : ℝ≥0 → ℝ≥0 :=
  (clockIso κ L hc hm h0).symm

theorem clock_inverse (κ : ℝ≥0) (L : ℝ≥0 → ℝ≥0)
    (hc : Continuous L) (hm : Monotone L) (h0 : L 0 = 0) (t : ℝ≥0) :
    clock κ L (inverseClock κ L hc hm h0 t) = t :=
  (clockIso κ L hc hm h0).apply_symm_apply t

theorem inverse_clock (κ : ℝ≥0) (L : ℝ≥0 → ℝ≥0)
    (hc : Continuous L) (hm : Monotone L) (h0 : L 0 = 0) (t : ℝ≥0) :
    inverseClock κ L hc hm h0 (clock κ L t) = t :=
  (clockIso κ L hc hm h0).symm_apply_apply t

theorem inverse_le (κ : ℝ≥0) (L : ℝ≥0 → ℝ≥0)
    (hc : Continuous L) (hm : Monotone L) (h0 : L 0 = 0) (t : ℝ≥0) :
    inverseClock κ L hc hm h0 t ≤ t := by
  have h := clock_ge κ L (inverseClock κ L hc hm h0 t)
  rwa [clock_inverse] at h

theorem inverse_monotone (κ : ℝ≥0) (L : ℝ≥0 → ℝ≥0)
    (hc : Continuous L) (hm : Monotone L) (h0 : L 0 = 0) :
    Monotone (inverseClock κ L hc hm h0) :=
  (clockIso κ L hc hm h0).symm.monotone

theorem inverse_continuous (κ : ℝ≥0) (L : ℝ≥0 → ℝ≥0)
    (hc : Continuous L) (hm : Monotone L) (h0 : L 0 = 0) :
    Continuous (inverseClock κ L hc hm h0) :=
  (clockIso κ L hc hm h0).symm.continuous

theorem inverse_increment (κ : ℝ≥0) (L : ℝ≥0 → ℝ≥0)
    (hc : Continuous L) (hm : Monotone L) (h0 : L 0 = 0)
    (s t : ℝ≥0) (hst : s ≤ t) :
    (inverseClock κ L hc hm h0 t : ℝ) - inverseClock κ L hc hm h0 s ≤ (t : ℝ) - s := by
  have hmono := hm (inverse_monotone κ L hc hm h0 hst)
  have hs := clock_inverse κ L hc hm h0 s
  have ht := clock_inverse κ L hc hm h0 t
  have hs' := congrArg (fun x : ℝ≥0 => (x : ℝ)) hs
  have ht' := congrArg (fun x : ℝ≥0 => (x : ℝ)) ht
  simp only [clock, NNReal.coe_add, NNReal.coe_mul] at hs' ht'
  have hmonor : (L (inverseClock κ L hc hm h0 s) : ℝ) ≤
      L (inverseClock κ L hc hm h0 t) := hmono
  nlinarith [κ.coe_nonneg]

end OperatorDerivativeRewrite.Foundation.StickyTimeChangeClock
