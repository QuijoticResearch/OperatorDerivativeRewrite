import Foundation.HigherHeatAdaptedIntegralClosure
import Foundation.HigherHeatTerminalPositions

/-! A genuine signed-moment obstruction to reconstruction through the first stochastic channel.
This concerns the constructed integral, independently of the manuscript's D^p obstruction. -/
noncomputable section
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.HigherHeatFirstChannelRange
open HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain HigherHeatCommonDerivative
open HigherHeatTimeDerivative HigherHeatPolynomialCoordinates HigherHeatWeakTimeAdjoint
open MultivariateFactorialDomain MultivariateFactorialSubstitution HigherHeatCompletedPairing
open HigherHeatCompletedSignedMean HigherHeatTerminalPositions

theorem gridDerivative_C (n : ℕ) (w : Fin (size n) → ℝ) (c : ℝ) :
    gridDerivative n w (MvPolynomial.C c) = 0 := by
  change coordinates n (polynomialDerivative w ((coordinates n).symm (MvPolynomial.C c))) = 0
  rw [show (coordinates n).symm (MvPolynomial.C c) = MvPolynomial.C c from
    (coordinates n).symm.commutes c, polynomialDerivative_C, map_zero]

theorem atTime_C (t c : ℝ) (n : ℕ) :
    atTime t (core (cylinderOf n (MvPolynomial.C c))) = 0 := by
  rw [atTime, operator_core, gridDerivative_C, map_zero, map_zero]

theorem atTime_coordinate (t : ℝ) (n : ℕ) (j : Fin (size n)) :
    atTime t (core (cylinderOf n (coordinates n (MvPolynomial.X j)))) =
      core (cylinderOf n (MvPolynomial.C (direction t (timeEmbedding n j)))) := by
  rw [atTime, operator_core]
  congr 2
  change coordinates n (polynomialDerivative _ ((coordinates n).symm
    (coordinates n (MvPolynomial.X j)))) = _
  rw [AlgEquiv.symm_apply_apply, polynomialDerivative_X]
  exact (coordinates n).commutes _

theorem atTime_pow_coordinate_zero (t : ℝ) (n : ℕ) (j : Fin (size n))
    (r : ℕ) (hr : 2 ≤ r) :
    ((atTime t)^r) (core (cylinderOf n (coordinates n (MvPolynomial.X j)))) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  have hz : ∀ k, ((atTime t)^(k+2))
      (core (cylinderOf n (coordinates n (MvPolynomial.X j)))) = 0 := by
    intro k
    induction k with
    | zero =>
      change atTime t (atTime t (core (cylinderOf n (coordinates n (MvPolynomial.X j))))) = 0
      rw [atTime_coordinate, atTime_C]
    | succ k ih =>
      rw [show k+1+2 = (k+2)+1 by omega, pow_succ']
      change atTime t (((atTime t)^(k+2))
        (core (cylinderOf n (coordinates n (MvPolynomial.X j))))) = 0
      rw [ih, map_zero]
  simpa only [Nat.add_comm 2 k] using hz k

theorem terminal_coordinate :
    cylinderOf 0 (coordinates 0 (MvPolynomial.X (lastIndex 0))) = terminalCylinder := by
  rw [coordinates_X]
  exact positionCylinder_last 0

theorem firstChannel_terminal_zero (m : ℕ) (hm : 1 < m) (T : ℝ≥0)
    (A : Field timeMeasure) : firstChannel m T A (core terminalCylinder) = 0 := by
  rw [firstChannel_apply]
  have hz (t : ℝ) : ((atTime t)^(2*m-1)) (core terminalCylinder) = 0 := by
    rw [← terminal_coordinate]
    exact atTime_pow_coordinate_zero t 0 (lastIndex 0) (2*m-1) (by omega)
  simp only [hz, map_zero, MeasureTheory.integral_zero, mul_zero]

theorem witness_centered (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    mean m hm T hT (core (terminalCylinder^(2*m-1))) = 0 := by
  rw [mean_core_real, terminal_moments]
  have ho : ¬ 2*m ∣ 2*m-1 := by
    intro h
    have hh := Nat.le_of_dvd (by omega : 0 < 2*m-1) h
    omega
  rw [PseudoPolynomialStein.moment_off_order (2*m) (by omega) _ _ ho]
  rfl

theorem witness_pairing (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    pairing m hm T hT (core (terminalCylinder^(2*m-1))) (core terminalCylinder) =
      ((2*m).factorial:ℝ)*((-1:ℝ)^(m+1)*(T:ℝ)) := by
  rw [pairing_core_real, ← pow_succ, show 2*m-1+1 = 2*m by omega,
    terminal_moments, PseudoPolynomialStein.moment_leading (2*m) (by omega)]
  rfl

theorem no_firstChannel_representation (m : ℕ) (hm : 1 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : Field timeMeasure) :
    firstChannel m T A ≠
      pairing m (by omega) T hT (core (terminalCylinder^(2*m-1))) := by
  intro he
  have hh := congrArg (fun φ : HigherHeatPairedDualCausality.Dual => φ (core terminalCylinder)) he
  rw [firstChannel_terminal_zero m hm, witness_pairing] at hh
  have hn : ((2*m).factorial:ℝ)*((-1:ℝ)^(m+1)*(T:ℝ)) ≠ 0 :=
    mul_ne_zero (by positivity)
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) (ne_of_gt (by exact_mod_cast hT)))
  exact hn hh.symm

end OperatorDerivativeRewrite.Foundation.HigherHeatFirstChannelRange
