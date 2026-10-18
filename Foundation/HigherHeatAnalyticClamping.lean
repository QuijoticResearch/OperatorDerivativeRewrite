import Foundation.MultivariateFactorialSubstitution
import Foundation.HigherHeatPolynomialCoordinates

/-! Contractive position clamping, identified with actual increment zeroing. -/
noncomputable section

namespace OperatorDerivativeRewrite.Foundation.HigherHeatAnalyticClamping
open HigherHeatPolynomialCylinders HigherHeatPolynomialCoordinates HigherHeatPositionVariation
open HigherHeatCylinderFourier MultivariateFactorialSubstitution MultivariateFactorialDomain

def clamp (n : ℕ) (r : Fin (size n)) (i : Fin (size n)) : Fin (size n) := min i r

def mask (n : ℕ) (r : Fin (size n)) (i : Fin (size n)) : ℝ := if i ≤ r then 1 else 0

theorem mask_bound (n : ℕ) (r : Fin (size n)) (i : Fin (size n)) : |mask n r i| ≤ 1 := by
  simp only [mask]
  split <;> norm_num

def zeroFuture (n : ℕ) (r : Fin (size n)) : Test n →ₐ[ℝ] Test n :=
  polynomialSubstitution id (mask n r)

def clampPositions (n : ℕ) (r : Fin (size n)) : Test n →ₐ[ℝ] Test n :=
  polynomialSubstitution (clamp n r) (fun _ => 1)

theorem cumulative_mask (n : ℕ) (r i : Fin (size n)) (x : Fin (size n) → ℝ) :
    cumulativeEquiv (size n) (fun j => mask n r j * x j) i =
      cumulativeEquiv (size n) x (clamp n r i) := by
  rw [cumulativeEquiv_apply, cumulativeEquiv_apply, cumulative_apply, cumulative_apply]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hi : j ≤ i <;> by_cases hr : j ≤ r <;>
    simp [mask, clamp, hi, hr]

theorem zeroFuture_coordinates (n : ℕ) (r : Fin (size n)) (P : Test n) :
    zeroFuture n r (coordinates n P) = coordinates n (clampPositions n r P) := by
  apply MvPolynomial.funext
  intro x
  rw [zeroFuture, eval_polynomialSubstitution, eval_coordinates, eval_coordinates,
    clampPositions, eval_polynomialSubstitution]
  apply congrArg (fun y => MvPolynomial.eval y P)
  funext i
  simpa only [one_mul, id_eq] using cumulative_mask n r i x

theorem inverse_zeroFuture (n : ℕ) (r : Fin (size n)) (P : Test n) :
    (coordinates n).symm (zeroFuture n r P) = clampPositions n r ((coordinates n).symm P) := by
  apply (coordinates n).injective
  rw [AlgEquiv.apply_symm_apply, ← zeroFuture_coordinates, AlgEquiv.apply_symm_apply]

def clampOperator (n : ℕ) (r : Fin (size n)) :
    H (Fin (size n)) →L[ℝ] H (Fin (size n)) :=
  substitute (clamp n r) (fun _ => 1) (by intro _; norm_num)

theorem clampOperator_encode (n : ℕ) (r : Fin (size n)) (P : Test n) :
    clampOperator n r (encode n P) = encode n (zeroFuture n r P) := by
  rw [encode_apply, encode_apply, inverse_zeroFuture]
  exact substitute_polynomial _ _ _ _

theorem clampOperator_bound (n : ℕ) (r : Fin (size n)) : ‖clampOperator n r‖ ≤ 1 :=
  substitute_bound _ _ _

theorem encode_zeroFuture_bound (n : ℕ) (r : Fin (size n)) (P : Test n) :
    ‖encode n (zeroFuture n r P)‖ ≤ ‖encode n P‖ := by
  rw [← clampOperator_encode]
  simpa only [one_mul] using
    (clampOperator n r).le_of_opNorm_le (clampOperator_bound n r) (encode n P)

theorem clampOperator_tower (n : ℕ) (r s : Fin (size n)) :
    (clampOperator n s).comp (clampOperator n r) = clampOperator n (min r s) := by
  have he : clamp n s ∘ clamp n r = clamp n (min r s) := by
    funext i
    simp only [Function.comp_apply, clamp, min_assoc]
  have h := substitute_comp (clamp n r) (clamp n s) (fun _ => (1:ℝ)) (fun _ => (1:ℝ))
    (by intro _; norm_num) (by intro _; norm_num)
  simpa only [clampOperator, one_mul, he] using h

theorem clampOperator_idempotent (n : ℕ) (r : Fin (size n)) :
    (clampOperator n r).comp (clampOperator n r) = clampOperator n r := by
  simpa only [min_self] using clampOperator_tower n r r

theorem zeroFuture_idempotent (n : ℕ) (r : Fin (size n)) (P : Test n) :
    zeroFuture n r (zeroFuture n r P) = zeroFuture n r P := by
  apply (encode_injective n)
  rw [← clampOperator_encode, ← clampOperator_encode]
  exact DFunLike.congr_fun (clampOperator_idempotent n r) (encode n P)

end OperatorDerivativeRewrite.Foundation.HigherHeatAnalyticClamping
