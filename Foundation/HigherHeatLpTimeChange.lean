import Foundation.HigherHeatLpControlExtension
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Actual interval restrictions of Lp controls and their continuous increasing heat clock. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatLpTimeChange
open HigherHeatLpControls

def restricted (m : ℕ) [Fact (0 < m)] (u : Control m) (s t : ℝ) : Control m :=
  ((Lp.memLp u).indicator measurableSet_Ioc).toLp ((Ioc s t).indicator u)

theorem restricted_ae (m : ℕ) [Fact (0 < m)] (u : Control m) (s t : ℝ) :
    ⇑(restricted m u s t) =ᵐ[volume] (Ioc s t).indicator u :=
  ((Lp.memLp u).indicator measurableSet_Ioc).coeFn_toLp

theorem restricted_clock (m : ℕ) [h : Fact (0 < m)] (u : Control m) (s t : ℝ) :
    (clock m (restricted m u s t) : ℝ) = ∫ x in Ioc s t, ‖u x‖ ^ (2*m) := by
  have hm := h.out
  rw [clock_integral, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [restricted_ae m u s t] with x hx
  rw [hx]
  by_cases hi : x ∈ Ioc s t
  · simp [hi]
  · simp [hi, zero_pow (show 2*m ≠ 0 by omega)]

def time (m : ℕ) [Fact (0 < m)] (u : Control m) (t : ℝ≥0) : ℝ≥0 :=
  ⟨∫ x in (0 : ℝ)..(t : ℝ), ‖u x‖ ^ (2*m),
    intervalIntegral.integral_nonneg_of_forall t.2 (fun _ => by positivity)⟩

theorem time_eq_clock (m : ℕ) [Fact (0 < m)] (u : Control m) (t : ℝ≥0) :
    time m u t = clock m (restricted m u 0 t) := by
  apply NNReal.eq
  exact (intervalIntegral.integral_of_le t.2).trans (restricted_clock m u 0 t).symm

theorem time_zero (m : ℕ) [Fact (0 < m)] (u : Control m) : time m u 0 = 0 := by
  apply NNReal.eq
  change (∫ x in (0 : ℝ)..0, ‖u x‖ ^ (2*m)) = 0
  exact intervalIntegral.integral_same

theorem time_continuous (m : ℕ) [Fact (0 < m)] (u : Control m) :
    Continuous (time m u) := by
  apply Continuous.subtype_mk
  exact ((power_integrable m u).continuous_primitive 0).comp continuous_subtype_val

theorem time_monotone (m : ℕ) [Fact (0 < m)] (u : Control m) : Monotone (time m u) := by
  intro s t hst
  change (∫ x in (0 : ℝ)..(s : ℝ), ‖u x‖ ^ (2*m)) ≤
    ∫ x in (0 : ℝ)..(t : ℝ), ‖u x‖ ^ (2*m)
  exact intervalIntegral.integral_mono_interval le_rfl s.2 hst
    (Filter.Eventually.of_forall (fun _ => by positivity))
    (power_integrable m u).intervalIntegrable

theorem time_increment (m : ℕ) [Fact (0 < m)] (u : Control m)
    (s t : ℝ≥0) (hst : s ≤ t) :
    time m u t - time m u s = clock m (restricted m u s t) := by
  apply NNReal.eq
  rw [NNReal.coe_sub (time_monotone m u hst), restricted_clock]
  rw [← intervalIntegral.integral_of_le (show (s : ℝ) ≤ (t : ℝ) from hst)]
  change (∫ x in (0 : ℝ)..(t : ℝ), ‖u x‖ ^ (2*m)) -
    (∫ x in (0 : ℝ)..(s : ℝ), ‖u x‖ ^ (2*m)) = _
  have he := intervalIntegral.integral_add_adjacent_intervals
    (f := fun x : ℝ => ‖u x‖ ^ (2*m)) (a := (0 : ℝ)) (b := (s : ℝ)) (c := (t : ℝ))
    (power_integrable m u).intervalIntegrable
    (power_integrable m u).intervalIntegrable
  linarith

theorem increment_law (m : ℕ) [h : Fact (0 < m)] (u : Control m)
    (s t : ℝ≥0) (hst : s ≤ t) :
    marginal m (restricted m u s t) =
      HigherHeatStepIntegralRealization.heatLaw m h.out (time m u t - time m u s) := by
  unfold marginal
  rw [time_increment m u s t hst]

end OperatorDerivativeRewrite.Foundation.HigherHeatLpTimeChange
