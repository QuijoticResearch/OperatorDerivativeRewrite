import Foundation.HigherHeatLpObservableIto
import Mathlib.Analysis.SpecificLimits.Basic

/-! Actual L2-small controls whose biharmonic integral laws stay away from the zero law. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatL2InputObstruction
open HigherHeatLpControls HigherHeatLpStepControls

private instance : Fact (0 < (2 : ℕ)) := ⟨by omega⟩

def cell (n : ℕ) (_ : Fin 1) : Set ℝ := Ioc 0 (((n : ℝ)+1)^4)⁻¹

theorem cell_measurable (n : ℕ) (i : Fin 1) : MeasurableSet (cell n i) := measurableSet_Ioc

theorem cell_finite (n : ℕ) (i : Fin 1) : volume (cell n i) ≠ ∞ := by
  rw [cell, Real.volume_Ioc]
  exact ENNReal.ofReal_ne_top

def spike (m : ℕ) [Fact (0 < m)] (n : ℕ) : Control m :=
  control m (cell n) (cell_measurable n) (cell_finite n) (fun _ => (n : ℝ)+1)

theorem spike_clock (m : ℕ) [Fact (0 < m)] (n : ℕ) :
    (clock m (spike m n) : ℝ) = (((n : ℝ)+1)^4)⁻¹ * ((n : ℝ)+1)^(2*m) := by
  have hd : Pairwise (fun i j : Fin 1 => Disjoint (cell n i) (cell n j)) := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  rw [spike, clock_step m (cell n) (cell_measurable n) (cell_finite n) hd]
  simp [cell, measureReal_def, Real.volume_Ioc, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ (n : ℝ)+1 by positivity)]
  exact Or.inl (by positivity)

theorem spike_fourth_clock (n : ℕ) : clock 2 (spike 2 n) = 1 := by
  apply NNReal.eq
  rw [spike_clock]
  norm_num
  exact inv_mul_cancel₀ (by positivity)

theorem spike_l2_norm (n : ℕ) : ‖spike 1 n‖ = 1 / ((n : ℝ)+1) := by
  have he := spike_clock 1 n
  change ‖spike 1 n‖ ^ (2*1) = _ at he
  norm_num at he
  have hn : 0 < (n : ℝ)+1 := by positivity
  have hh : (((n : ℝ)+1)^4)⁻¹ * ((n : ℝ)+1)^2 = (1 / ((n : ℝ)+1))^2 := by
    field_simp
  rw [hh] at he
  have hnorm := norm_nonneg (spike 1 n)
  have hinv : 0 < 1 / ((n : ℝ)+1) := by positivity
  nlinarith

theorem spike_l2_tendsto : Tendsto (spike 1) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [spike_l2_norm] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem spike_fourier (n : ℕ) (ξ : ℝ) :
    (∫ᵛ y, HigherHeatCylinderFourier.phase ξ y ∂<•marginal 2 (spike 2 n)) =
      HigherHeatL2.symbol 2 1 ξ := by
  rw [marginal_fourier, spike_fourth_clock]

theorem no_l2_continuous_extension (F : Control 1 → ℂ)
    (h0 : F 0 = 1)
    (hs : ∀ n, F (spike 1 n) =
      ∫ᵛ y, HigherHeatCylinderFourier.phase 1 y ∂<•marginal 2 (spike 2 n)) :
    ¬ ContinuousAt F 0 := by
  intro hF
  have ht := hF.tendsto.comp spike_l2_tendsto
  simp only [Function.comp_def, hs, spike_fourier, h0] at ht
  have he : HigherHeatL2.symbol 2 1 1 = 1 := tendsto_nhds_unique tendsto_const_nhds ht
  have hr := congrArg Complex.re he
  change Real.exp (-(1 : ℝ) * (2 * Real.pi * 1)^4) = 1 at hr
  have hn : -(1 : ℝ) * (2 * Real.pi * 1)^4 < 0 :=
    mul_neg_of_neg_of_pos (by norm_num) (pow_pos (by positivity) _)
  exact (ne_of_lt (Real.exp_lt_one_iff.mpr hn)) hr

end OperatorDerivativeRewrite.Foundation.HigherHeatL2InputObstruction
