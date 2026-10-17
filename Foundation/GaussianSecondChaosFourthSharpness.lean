import Foundation.GaussianSecondChaosFourthLower
import Mathlib.Analysis.SpecificLimits.Basic

/-! Explicit flat quadratic observables approach the universal lower coefficient. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianSecondChaosFourthSharpness
open InfiniteGaussian GaussianNumberSectors GaussianSecondChaosL4
open GaussianLinearFieldMatrixCoordinates GaussianDiagonalQuadraticL4

def flat (n : ℕ) : sector 2 :=
  ⟨target (fun i : Fin (n+1) => unit i.val) (fun _ => 1), target_mem_second_chaos _ _⟩

theorem flat_variance (n : ℕ) : ‖(flat n).val‖^2 = 2 * (n+1 : ℕ) := by
  change ‖(target (fun i : Fin (n+1) => unit i.val) (fun _ => 1) : GaussianL2)‖^2 = _
  rw [target_variance (fun i : Fin (n+1) => unit i.val)
    (units_orthonormal.comp (fun i : Fin (n+1) => i.val) Fin.val_injective) (fun _ => 1)]
  simp

theorem flat_fourth (n : ℕ) :
    ‖square (flat n)‖^2 = 12 * ((n+1 : ℕ) : ℝ)^2 + 48 * (n+1 : ℕ) := by
  rw [show square (flat n) =
    (polynomialProduct (target (fun i : Fin (n+1) => unit i.val) (fun _ => 1))
      (target (fun i : Fin (n+1) => unit i.val) (fun _ => 1)) : GaussianL2)
    from square_polynomial _ _]
  rw [target_fourth_moment (fun i : Fin (n+1) => unit i.val)
    (units_orthonormal.comp (fun i : Fin (n+1) => i.val) Fin.val_injective) (fun _ => 1)]
  simp

theorem flat_fourth_ratio (n : ℕ) :
    ‖square (flat n)‖^2 / (‖(flat n).val‖^2)^2 = 3 + 12 / (n+1 : ℕ) := by
  rw [flat_fourth, flat_variance]
  have hn : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem flat_fourth_ratio_tendsto :
    Tendsto (fun n => ‖square (flat n)‖^2 / (‖(flat n).val‖^2)^2) atTop (𝓝 3) := by
  simp only [flat_fourth_ratio]
  have ht := ((tendsto_const_div_atTop_nhds_zero_nat (12 : ℝ)).comp
    (tendsto_add_atTop_nat 1)).const_add 3
  simpa using ht

theorem universal_lower_coefficient_le_three (c : ℝ)
    (hc : ∀ f : sector 2, c * (‖f.val‖^2)^2 ≤ ‖square f‖^2) : c ≤ 3 := by
  apply ge_of_tendsto flat_fourth_ratio_tendsto
  apply Eventually.of_forall
  intro n
  apply (le_div_iff₀ _).mpr
  · exact hc (flat n)
  · rw [flat_variance]
    positivity

end OperatorDerivativeRewrite.Foundation.GaussianSecondChaosFourthSharpness
