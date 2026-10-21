import Foundation.HigherHeatSmallTimeBound
import Foundation.HigherHeatPredictableJetBounds

/-! The actual one-cell heat shift of a native predictable Taylor coefficient.
These estimates do not yet identify the shifted jet with the causal projected
derivative, and do not assert convergence of the surviving coefficient fields. -/
noncomputable section
open scoped NNReal

namespace OperatorDerivativeRewrite.Foundation.HigherHeatJetHeatCorrection
open HigherHeatPolynomialCylinders HigherHeatPolynomialCoordinates
open HigherHeatPredictableJetBounds HigherHeatPositionSteinDerivative
open HigherHeatFiniteCausalBound MultivariateDirectionalKernel MultivariateFactorialDomain
open HigherHeatSmallTimeBound

theorem clamped_transport_error (n p : ℕ) (hp : 0 < p) (a : ℝ)
    (j : Fin (size n)) (P : Test n) :
    ‖encode n (clampBefore n j (transport p hp a (Pi.single j 1) P)) -
      encode n (clampBefore n j P)‖ ≤ (Real.exp |a| - 1) * ‖encode n P‖ := by
  rw [← map_sub, ← map_sub]
  exact (clampBefore_bound n j _).trans (by
    rw [map_sub]
    exact transport_sub_identity_bound n p hp a j P)

def shiftedJet (n m : ℕ) (hm : 0 < m) (T : ℝ≥0)
    (j : Fin (size n)) (q : ℕ) (a : ℝ) (P : Test n) : Test n :=
  (q.factorial:ℝ)⁻¹ • clampBefore n j
    (transport (2*m) (by omega) a (Pi.single j 1)
      ((polynomialDerivative (Pi.single j 1) : Test n → Test n)^[q]
        (nextConditioned n m T j P)))

theorem shiftedJet_error (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (q : ℕ) (a : ℝ) (P : Test n) :
    ‖encode n (shiftedJet n m hm T j q a P) - encode n (predictableJet n m T j q P)‖ ≤
      (q.factorial:ℝ)⁻¹ * (Real.exp |a| - 1) * Real.exp (T:ℝ) * ‖encode n P‖ := by
  rw [shiftedJet, predictableJet, map_smul, map_smul, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (q.factorial:ℝ)⁻¹)]
  have h := (clamped_transport_error n (2*m) (by omega) a j _).trans
    (mul_le_mul_of_nonneg_left
      ((encode_iterate_bound n j q _).trans (localProjection_encode_bound n m hm T hT j P))
      (sub_nonneg.mpr (Real.one_le_exp (abs_nonneg a))))
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by ring)

end OperatorDerivativeRewrite.Foundation.HigherHeatJetHeatCorrection
