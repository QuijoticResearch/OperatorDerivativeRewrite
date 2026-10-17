import Foundation.HigherHeatLpTimeChange

/-! Time-inhomogeneous heat operators represented by actual interval-control laws. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatLpPropagator
open HigherHeatLpControls HigherHeatLpTimeChange HigherHeatFourierBanach
open HigherHeatFourierPathSemigroup FourierPathStopping FourierPathTerminalKernels

def propagator (m : ℕ) [h : Fact (0 < m)] (a : ℕ → ℝ) (u : Control m)
    (s t : ℝ≥0) : TestSpace terminalLevels (frequency a) →L[ℂ]
      TestSpace terminalLevels (frequency a) :=
  evolution terminalLevels (frequency a) m h.out (time m u t - time m u s)

theorem propagator_self (m : ℕ) [h : Fact (0 < m)] (a : ℕ → ℝ) (u : Control m)
    (s : ℝ≥0) (q : TestSpace terminalLevels (frequency a)) :
    propagator m a u s s q = q := by
  unfold propagator
  rw [tsub_self, evolution_zero]

theorem propagator_tower (m : ℕ) [h : Fact (0 < m)] (a : ℕ → ℝ) (u : Control m)
    (s t r : ℝ≥0) (hst : s ≤ t) (htr : t ≤ r)
    (q : TestSpace terminalLevels (frequency a)) :
    propagator m a u s t (propagator m a u t r q) = propagator m a u s r q := by
  unfold propagator
  rw [evolution_add]
  have he : time m u t - time m u s + (time m u r - time m u t) =
      time m u r - time m u s := by
    apply NNReal.eq
    rw [NNReal.coe_add, NNReal.coe_sub (time_monotone m u hst),
      NNReal.coe_sub (time_monotone m u htr),
      NNReal.coe_sub (time_monotone m u (hst.trans htr))]
    ring
  rw [he]

theorem propagator_bound (m : ℕ) [h : Fact (0 < m)] (a : ℕ → ℝ) (u : Control m)
    (s t : ℝ≥0) (q : TestSpace terminalLevels (frequency a)) :
    ‖propagator m a u s t q‖ ≤ ‖q‖ :=
  evolution_bound terminalLevels (frequency a) m h.out _ q

theorem propagator_continuous (m : ℕ) [h : Fact (0 < m)] (a : ℕ → ℝ) (u : Control m)
    (q : TestSpace terminalLevels (frequency a)) :
    Continuous (fun z : ℝ≥0 × ℝ≥0 => propagator m a u z.1 z.2 q) := by
  exact (HigherHeatFourierPathC0.evolution_strong_continuous terminalLevels (frequency a)
    m h.out q).comp (((time_continuous m u).comp continuous_snd).sub
      ((time_continuous m u).comp continuous_fst))

theorem propagator_integral (m : ℕ) [h : Fact (0 < m)] (a : ℕ → ℝ) (u : Control m)
    (s t : ℝ≥0) (hst : s ≤ t) (q : TestSpace terminalLevels (frequency a)) (x : ℝ) :
    realize terminalLevels (frequency a) (propagator m a u s t q) (line x) =
      ∫ᵛ y, realize terminalLevels (frequency a) q (shiftedLine x y)
        ∂<•marginal m (restricted m u s t) := by
  unfold propagator
  rw [time_increment m u s t hst]
  exact marginal_operator m a _ q x

theorem interval_expectation_bound (m : ℕ) [h : Fact (0 < m)] (a : ℕ → ℝ) (u : Control m)
    (s t : ℝ≥0) (hst : s ≤ t) (q : TestSpace terminalLevels (frequency a)) (x : ℝ) :
    ‖∫ᵛ y, realize terminalLevels (frequency a) q (shiftedLine x y)
      ∂<•marginal m (restricted m u s t)‖ ≤ ‖q‖ := by
  rw [← propagator_integral m a u s t hst q x]
  exact ((realize terminalLevels (frequency a) (propagator m a u s t q)).norm_coe_le_norm
    (line x)).trans ((realize_bound _ _ _).trans (propagator_bound m a u s t q))

end OperatorDerivativeRewrite.Foundation.HigherHeatLpPropagator
