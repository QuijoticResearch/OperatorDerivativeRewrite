import Foundation.HigherHeatStepIntegralOperators
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! Actual Lebesgue L^(2m) controls and their integral higher-heat clock. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatLpControls
open HigherHeatStepIntegralRealization HigherHeatFourierBanach HigherHeatFourierPathSemigroup
open FourierPathStopping FourierPathTerminalKernels

def power (m : ℕ) : ℝ≥0∞ := (2*m : ℕ)

instance power_fact (m : ℕ) [h : Fact (0 < m)] : Fact (1 ≤ power m) := ⟨by
  have hm := h.out
  unfold power
  exact_mod_cast (show 1 ≤ 2*m by omega)⟩

abbrev Control (m : ℕ) := Lp (α := ℝ) ℝ (power m) volume

theorem power_ne_zero (m : ℕ) [h : Fact (0 < m)] : power m ≠ 0 := by
  have hm := h.out
  simp only [power, Nat.cast_eq_zero, ne_eq]
  omega

theorem power_ne_top (m : ℕ) : power m ≠ ∞ := ENNReal.natCast_ne_top (2*m)

theorem control_complete (m : ℕ) [Fact (0 < m)] : CompleteSpace (Control m) := inferInstance

def clock (m : ℕ) [Fact (0 < m)] (u : Control m) : ℝ≥0 := ‖u‖₊ ^ (2*m)

theorem clock_continuous (m : ℕ) [Fact (0 < m)] : Continuous (clock m) :=
  continuous_nnnorm.pow _

theorem power_integrable (m : ℕ) [Fact (0 < m)] (u : Control m) :
    Integrable (fun s : ℝ => ‖u s‖ ^ (2*m)) := by
  have hh := (Lp.memLp u).norm_rpow (power_ne_zero m) (power_ne_top m)
  have hi := memLp_one_iff_integrable.mp hh
  simpa only [power, ENNReal.toReal_natCast, Real.rpow_natCast] using hi

theorem clock_integral (m : ℕ) [h : Fact (0 < m)] (u : Control m) :
    (clock m u : ℝ) = ∫ s : ℝ, ‖u s‖ ^ (2*m) := by
  have hm := h.out
  have hp : ((2*m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show 2*m ≠ 0 by omega)
  have hn := lpNorm_eq_integral_norm_rpow_toReal (power_ne_zero m) (power_ne_top m)
    (Lp.aestronglyMeasurable u)
  rw [← toReal_eLpNorm, ← Lp.norm_def] at hn
  simp only [power, ENNReal.toReal_natCast, Real.rpow_natCast] at hn
  have hI : 0 ≤ ∫ s : ℝ, ‖u s‖ ^ (2*m) := integral_nonneg fun _ => by positivity
  change ‖u‖ ^ (2*m) = _
  have he := congrArg (fun r : ℝ => r ^ (2*m)) hn
  have hh : ((∫ s : ℝ, ‖u s‖ ^ (2*m)) ^ (((2*m : ℕ) : ℝ)⁻¹)) ^ (2*m) =
      ∫ s : ℝ, ‖u s‖ ^ (2*m) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hI, inv_mul_cancel₀ hp, Real.rpow_one]
  exact he.trans hh

def marginal (m : ℕ) [h : Fact (0 < m)] (u : Control m) : SignedMeasure ℝ :=
  heatLaw m h.out (clock m u)

theorem marginal_mass (m : ℕ) [h : Fact (0 < m)] (u : Control m) : marginal m u Set.univ = 1 :=
  heatLaw_mass m h.out _

theorem marginal_fourier (m : ℕ) [h : Fact (0 < m)] (u : Control m) (ξ : ℝ) :
    (∫ᵛ y, HigherHeatCylinderFourier.phase ξ y ∂<•marginal m u) =
      HigherHeatL2.symbol m (clock m u) ξ := heatLaw_fourier m h.out _ ξ

theorem observable_continuous (m : ℕ) [h : Fact (0 < m)] (a : ℕ → ℝ)
    (q : TestSpace terminalLevels (frequency a)) (x : ℝ) :
    Continuous (fun u : Control m =>
      realize terminalLevels (frequency a) (evolution terminalLevels (frequency a) m h.out (clock m u) q)
        (line x)) := by
  have he := (HigherHeatFourierPathC0.evolution_strong_continuous terminalLevels (frequency a)
    m h.out q).comp (clock_continuous m)
  have hr := (realize terminalLevels (frequency a)).continuous.comp he
  exact (BoundedContinuousFunction.evalCLM ℂ (line x)).continuous.comp hr

theorem marginal_operator (m : ℕ) [h : Fact (0 < m)] (a : ℕ → ℝ) (u : Control m)
    (q : TestSpace terminalLevels (frequency a)) (x : ℝ) :
    realize terminalLevels (frequency a) (evolution terminalLevels (frequency a) m h.out (clock m u) q)
      (line x) = ∫ᵛ y, realize terminalLevels (frequency a) q (shiftedLine x y) ∂<•marginal m u :=
  HigherHeatStepIntegralOperators.heatLaw_operator a m h.out _ q x

end OperatorDerivativeRewrite.Foundation.HigherHeatLpControls
