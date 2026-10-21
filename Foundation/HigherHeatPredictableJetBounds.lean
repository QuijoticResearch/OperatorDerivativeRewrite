import Foundation.HigherHeatFiniteCausalBound
import Foundation.HigherHeatEmptyPastBound
import Foundation.HigherHeatPositionSteinDerivative
import Foundation.PureOrderTaylorInnovations

/-! Degree-independent bounds for actual finite signed predictable Taylor
coefficients: future conditioning, coordinate derivatives and strict-past clamping. -/
noncomputable section
open scoped NNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatPredictableJetBounds
open HigherHeatPolynomialCylinders HigherHeatPolynomialCoordinates HigherHeatAnalyticClamping
open HigherHeatEmptyPastBound HigherHeatFiniteCausalBound HigherHeatDyadicConditioning
open HigherHeatPositionSteinDerivative MultivariateFactorialDomain MultivariateDirectionalKernel
open MultivariateFactorialSubstitution

def basePoint (n : ℕ) (j : Fin (size n)) (x : Fin (size n) → ℝ) : Fin (size n) → ℝ :=
  fun i => if i < j then x i else 0

def clampBefore (n : ℕ) (j : Fin (size n)) : Test n →ₐ[ℝ] Test n :=
  if hz : j.val=0 then zeroAll n else zeroFuture n ⟨j.val-1, by omega⟩

theorem eval_clampBefore (n : ℕ) (j : Fin (size n)) (P : Test n) (x : Fin (size n) → ℝ) :
    MvPolynomial.eval x (clampBefore n j P) = MvPolynomial.eval (basePoint n j x) P := by
  by_cases hz : j.val=0
  · rw [clampBefore, dif_pos hz, eval_zeroAll]
    apply congrArg (fun y : Fin (size n) → ℝ => MvPolynomial.eval y P)
    funext i
    simp [basePoint, Fin.lt_def, hz]
  · rw [clampBefore, dif_neg hz, zeroFuture, eval_polynomialSubstitution]
    apply congrArg (fun y : Fin (size n) → ℝ => MvPolynomial.eval y P)
    funext i
    have hi : i ≤ (⟨j.val-1, by omega⟩ : Fin (size n)) ↔ i < j := by
      change i.val ≤ j.val-1 ↔ i.val < j.val
      omega
    by_cases h : i < j <;> simp [mask, hi, basePoint, h]

theorem clampBefore_bound (n : ℕ) (j : Fin (size n)) (P : Test n) :
    ‖encode n (clampBefore n j P)‖ ≤ ‖encode n P‖ := by
  by_cases hz : j.val=0
  · rw [clampBefore, dif_pos hz]
    exact encode_zeroAll_bound n P
  · rw [clampBefore, dif_neg hz]
    exact encode_zeroFuture_bound n _ P

def nextConditioned (n m : ℕ) (T : ℝ≥0) (j : Fin (size n)) (P : Test n) : Test n :=
  localProjection m T n (initialPast n (j.val+1)) P

def predictableJet (n m : ℕ) (T : ℝ≥0) (j : Fin (size n)) (q : ℕ) (P : Test n) : Test n :=
  (q.factorial:ℝ)⁻¹ • clampBefore n j
    ((polynomialDerivative (Pi.single j 1) : Test n → Test n)^[q] (nextConditioned n m T j P))

theorem predictable_jet_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (q : ℕ) (P : Test n) :
    ‖encode n (predictableJet n m T j q P)‖ ≤
      (q.factorial:ℝ)⁻¹ * Real.exp (T:ℝ) * ‖encode n P‖ := by
  rw [predictableJet, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (q.factorial:ℝ)⁻¹)]
  have h := (clampBefore_bound n j _).trans
    ((encode_iterate_bound n j q _).trans (localProjection_encode_bound n m hm T hT j P))
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by ring)

theorem predictable_jet_coefficient (n m : ℕ) (T : ℝ≥0) (j : Fin (size n)) (q : ℕ)
    (P : Test n) (x : Fin (size n) → ℝ) :
    MvPolynomial.eval x (predictableJet n m T j q P) =
      (line (Pi.single j 1) (basePoint n j x) (nextConditioned n m T j P)).coeff q := by
  have h := PureOrderTaylorInnovations.hasse_eval_derivative
    (line (Pi.single j 1) (basePoint n j x) (nextConditioned n m T j P)) q 0
  rw [← Polynomial.coeff_zero_eq_eval_zero (Polynomial.hasseDeriv q
    (line (Pi.single j 1) (basePoint n j x) (nextConditioned n m T j P))),
    Polynomial.hasseDeriv_coeff] at h
  simp only [zero_add,
    Nat.choose_self, Nat.cast_one, one_mul] at h
  rw [iterate_derivative_line, eval_line] at h
  simp only [zero_mul, add_zero] at h
  rw [predictableJet, MvPolynomial.smul_eval, eval_clampBefore, h]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

end OperatorDerivativeRewrite.Foundation.HigherHeatPredictableJetBounds
