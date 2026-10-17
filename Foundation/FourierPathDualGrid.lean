import Foundation.FourierPathDualStepPairing

/-! Exact integral power clocks and direction pairings for actual uniform-grid controls. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathDualGrid
open HigherHeatLpControls HigherHeatLpStepControls

def cell (N : ℕ) (j : Fin N) : Set ℝ :=
  Ioc ((j.val : ℝ)/(N : ℝ)) ((j.val+1 : ℝ)/(N : ℝ))

theorem cell_measurable (N : ℕ) (j : Fin N) : MeasurableSet (cell N j) := measurableSet_Ioc

theorem cell_finite (N : ℕ) (j : Fin N) : volume (cell N j) ≠ ∞ := by
  rw [cell, Real.volume_Ioc]
  exact ENNReal.ofReal_ne_top

theorem cell_disjoint (N : ℕ) (hN : 0 < N) :
    Pairwise (fun i j : Fin N => Disjoint (cell N i) (cell N j)) := by
  have hnr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hf (i j : Fin N) (hij : i < j) : Disjoint (cell N i) (cell N j) := by
    apply Ioc_disjoint_Ioc_of_le
    apply (div_le_div_iff_of_pos_right hnr).mpr
    exact_mod_cast (Nat.succ_le_of_lt hij)
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hf i j h
  · exact (hf j i h).symm

theorem cell_volume (N : ℕ) (hN : 0 < N) (j : Fin N) : volume.real (cell N j) = 1/(N : ℝ) := by
  have hnr : 0 < (N : ℝ) := by exact_mod_cast hN
  have he : (j.val+1 : ℝ)/(N : ℝ) - (j.val : ℝ)/(N : ℝ) = 1/(N : ℝ) := by ring
  simp only [measureReal_def, cell, Real.volume_Ioc, he]
  exact ENNReal.toReal_ofReal (by positivity)

def step (m : ℕ) [Fact (0 < m)] (N : ℕ) (b : Fin N → ℝ) : Control m :=
  control m (cell N) (cell_measurable N) (cell_finite N) b

theorem step_clock (m : ℕ) [Fact (0 < m)] (N : ℕ) (hN : 0 < N) (b : Fin N → ℝ) :
    (clock m (step m N b) : ℝ) = (∑ j, (b j)^(2*m))/(N : ℝ) := by
  rw [step, clock_step m (cell N) (cell_measurable N) (cell_finite N) (cell_disjoint N hN)]
  simp only [cell_volume N hN, Real.norm_eq_abs, pow_abs_two_mul]
  rw [← Finset.mul_sum]
  ring

theorem norm_le_clock (m : ℕ) [h : Fact (0 < m)] (v : Control m) :
    ‖v‖ ≤ 1 + (clock m v : ℝ) := by
  have hm := h.out
  change ‖v‖ ≤ 1 + ‖v‖^(2*m)
  by_cases hv : ‖v‖ ≤ 1
  · linarith [pow_nonneg (norm_nonneg v) (2*m)]
  · have hp := le_self_pow₀ (le_of_not_ge hv) (show 2*m ≠ 0 by omega)
    linarith

theorem direction_pairing (m : ℕ) [Fact (0 < m)] (u : FourierPathDualControls.Control m)
    (N : ℕ) (hN : 0 < N) (b : Fin N → ℝ) :
    FourierPathDualControls.pairing m u (step m N b) =
      ∑ j, b j * FourierPathDyadicDirections.increment (FourierPathDualControls.direction m u) N j := by
  have hnr : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [step, FourierPathDualStepPairing.pairing_step]
  apply Finset.sum_congr rfl
  intro j _
  rw [FourierPathDualControls.direction_increment,
    intervalIntegral.integral_of_le ((div_le_div_iff_of_pos_right hnr).mpr (by linarith))]
  rfl

end OperatorDerivativeRewrite.Foundation.FourierPathDualGrid
