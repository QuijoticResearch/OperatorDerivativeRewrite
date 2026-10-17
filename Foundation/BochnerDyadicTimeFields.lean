import Foundation.BochnerTimeControlPairing

/-! Actual integrable vector-valued step fields on dyadic observation cells. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BochnerDyadicTimeFields
open FourierPathBoundedControls BochnerTimeControlPairing

def left (N : ℕ) (j : Fin N) : ℝ := (j.val:ℝ)/(N:ℝ)
def right (N : ℕ) (j : Fin N) : ℝ := (j.val+1:ℝ)/(N:ℝ)
def cell (N : ℕ) (j : Fin N) : Set ℝ := Set.Ioc (left N j) (right N j)

theorem cell_measurable (N : ℕ) (j : Fin N) : MeasurableSet (cell N j) := measurableSet_Ioc

theorem left_le_right (N : ℕ) (j : Fin N) : left N j ≤ right N j := by
  dsimp [left, right]
  apply div_le_div_of_nonneg_right (by linarith) (by positivity)

theorem cell_finite (N : ℕ) (j : Fin N) : volume (cell N j) ≠ ∞ := by
  rw [cell, Real.volume_Ioc]
  exact ENNReal.ofReal_ne_top

theorem cell_length (N : ℕ) (hN : 0 < N) (j : Fin N) : volume.real (cell N j) = 1/(N:ℝ) := by
  rw [cell, Real.volume_real_Ioc_of_le (left_le_right N j)]
  dsimp [left, right]
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def cellField (N : ℕ) (j : Fin N) (c : E) : BochnerTimeControlPairing.Field E :=
  indicatorConstLp 1 (cell_measurable N j) (cell_finite N j) c

theorem cellField_norm (N : ℕ) (hN : 0 < N) (j : Fin N) (c : E) :
    ‖cellField N j c‖ = ‖c‖/(N:ℝ) := by
  rw [cellField, norm_indicatorConstLp (p := 1) (by simp) (by simp)]
  simp only [ENNReal.toReal_one, div_one, Real.rpow_one]
  rw [cell_length N hN]
  ring

theorem pairing_cellField (N : ℕ) (j : Fin N) (c : E) (u : Control) :
    pairing E u (cellField N j c) = (∫ t in left N j..right N j, u t) • c := by
  rw [pairing_integral]
  trans ∫ t, (cell N j).indicator (fun s => u s • c) t
  · apply integral_congr_ae
    filter_upwards [@indicatorConstLp_coeFn ℝ E _ 1 volume _ _ (cell_measurable N j)
      (cell_finite N j) c] with t ht
    change u t • (indicatorConstLp 1 (cell_measurable N j) (cell_finite N j) c) t = _
    rw [ht]
    by_cases hts : t ∈ cell N j
    · simp [hts]
    · simp [hts]
  · rw [integral_indicator (show MeasurableSet (cell N j) from measurableSet_Ioc), integral_smul_const]
    rw [intervalIntegral.integral_of_le (left_le_right N j)]
    rfl

def stepField (N : ℕ) (c : Fin N → E) : BochnerTimeControlPairing.Field E := ∑ j, cellField N j (c j)

theorem stepField_bound (N : ℕ) (hN : 0 < N) (c : Fin N → E) :
    ‖stepField N c‖ ≤ (∑ j, ‖c j‖)/(N:ℝ) := by
  calc
    _ ≤ ∑ j, ‖cellField N j (c j)‖ := norm_sum_le _ _
    _ = _ := by simp_rw [cellField_norm N hN]; rw [Finset.sum_div]

theorem pairing_stepField (N : ℕ) (c : Fin N → E) (u : Control) :
    pairing E u (stepField N c) = ∑ j, (∫ t in left N j..right N j, u t) • c j := by
  rw [stepField, map_sum]
  exact Finset.sum_congr rfl (fun j _ => pairing_cellField N j (c j) u)

end OperatorDerivativeRewrite.Foundation.BochnerDyadicTimeFields
