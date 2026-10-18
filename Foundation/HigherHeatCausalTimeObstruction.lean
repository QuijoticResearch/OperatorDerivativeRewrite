import Foundation.HigherHeatTerminalPositions
import Foundation.HigherHeatCompletedSignedMean
import Foundation.HigherHeatAnalyticTimeObstruction

/-! Failure of strong continuity at zero for the completed coefficient-norm projections.
This is an obstruction in this particular test-space norm, including the Gaussian case. -/
noncomputable section
open scoped NNReal Topology

namespace OperatorDerivativeRewrite.Foundation.HigherHeatCausalTimeObstruction
open HigherHeatPolynomialCylinders HigherHeatPolynomialPathDomain HigherHeatTerminalPositions
open HigherHeatAnalyticCylinderDomain HigherHeatAnalyticTimeObstruction
open HigherHeatCylindricalConditioning HigherHeatCompletedCausalProjection
open HigherHeatCompletedEmptyPast HigherHeatCompletedSignedMean
open Filter

theorem algebraic_terminal (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (r : Fin (size n)) :
    dyadicProjection m hm T hT n (r.val+1) terminalCylinder = positionCylinder n r := by
  rw [terminal_on_grid n, dyadicProjection_apply m hm T hT n (r.val+1) n le_rfl]
  simp only [Nat.sub_self, pow_zero, mul_one]
  rw [localProjection_terminal n m hm T hT]
  rfl

theorem completed_terminal (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (r : Fin (size n)) :
    completed m hm T hT n r (core terminalCylinder) = core (positionCylinder n r) := by
  rw [completed_core, algebraic_terminal m hm T hT n r]

theorem mean_terminal_zero (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    HigherHeatCompletedSignedMean.mean m hm T hT (core terminalCylinder) = 0 := by
  rw [mean_core_real]
  have he := terminal_moments m hm T hT 1
  simp only [pow_one] at he
  rw [he]
  have hz : PseudoPolynomialStein.moment (2*m) ((-1:ℝ)^(m+1)*(T:ℝ)) 1 = 0 := by
    apply PseudoPolynomialStein.moment_off_order (2*m) (by omega)
    intro hd
    have hd' := Nat.dvd_one.mp hd
    omega
  rw [hz]
  rfl

theorem empty_terminal_zero (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    emptyProjection m hm T hT (core terminalCylinder) = 0 := by
  rw [emptyProjection_apply, mean_terminal_zero, zero_smul]

def earlyProjection (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) : Domain →L[ℝ] Domain :=
  completed m hm T hT n (firstIndex n)

theorem earlyProjection_terminal (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    earlyProjection m hm T hT n (core terminalCylinder) = core (firstPosition n) :=
  completed_terminal m hm T hT n (firstIndex n)

theorem earlyProjection_norm (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    ‖earlyProjection m hm T hT n‖ ≤ Real.exp (T:ℝ) := completed_norm m hm T hT n (firstIndex n)

theorem actual_path_tendsto (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (ω : Path) :
    Tendsto (fun n => HigherHeatPolynomialPathDomain.realize
      (dyadicProjection m hm T hT n ((firstIndex n).val+1) terminalCylinder) ω) atTop (𝓝 0) := by
  simp_rw [algebraic_terminal m hm T hT]
  exact first_path_tendsto ω

theorem terminal_gap (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    ‖(earlyProjection m hm T hT n - emptyProjection m hm T hT) (core terminalCylinder)‖ = 1 := by
  rw [sub_apply, earlyProjection_terminal, empty_terminal_zero, sub_zero]
  exact first_core_norm n

theorem not_tendsto_on_terminal (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    ¬ Tendsto (fun n => earlyProjection m hm T hT n (core terminalCylinder)) atTop
      (𝓝 (emptyProjection m hm T hT (core terminalCylinder))) := by
  rw [empty_terminal_zero]
  simp only [earlyProjection_terminal]
  exact first_core_not_tendsto_zero

theorem no_strong_convergence (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    ¬ (∀ u : Domain, Tendsto (fun n => earlyProjection m hm T hT n u) atTop
      (𝓝 (emptyProjection m hm T hT u))) := by
  intro h
  exact not_tendsto_on_terminal m hm T hT (h (core terminalCylinder))

theorem terminal_core_norm : ‖core terminalCylinder‖ = 1 := by
  rw [← positionCylinder_last 0]
  exact position_core_norm 0 (lastIndex 0)

theorem operator_gap (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    1 ≤ ‖earlyProjection m hm T hT n - emptyProjection m hm T hT‖ := by
  calc
    1 = ‖(earlyProjection m hm T hT n - emptyProjection m hm T hT) (core terminalCylinder)‖ :=
      (terminal_gap m hm T hT n).symm
    _ ≤ ‖earlyProjection m hm T hT n - emptyProjection m hm T hT‖ * ‖core terminalCylinder‖ :=
      (earlyProjection m hm T hT n - emptyProjection m hm T hT).le_opNorm _
    _ = _ := by rw [terminal_core_norm, mul_one]

theorem norm_gap_not_tendsto_zero (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    ¬ Tendsto (fun n => ‖earlyProjection m hm T hT n - emptyProjection m hm T hT‖) atTop (𝓝 0) := by
  intro h
  have he : (1:ℝ) ≤ 0 := ge_of_tendsto' h (operator_gap m hm T hT)
  norm_num at he

end OperatorDerivativeRewrite.Foundation.HigherHeatCausalTimeObstruction
