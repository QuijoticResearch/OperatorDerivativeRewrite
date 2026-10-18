import Foundation.HigherHeatFirstChannelRange

/-! Actual signed increment-product corrections, retaining the complementary derivative channel. -/
noncomputable section
open scoped NNReal ENNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatAffineStepCorrection
open MultivariateFactorialDomain MultivariateFactorialSubstitution MultivariateConditionalStein
open HigherHeatPolynomialRefinement HigherHeatPolynomialCylinders HigherHeatGridDoubling

theorem derivative_mul_affine {ι : Type*} (v : ι → ℝ) (F G : MvPolynomial ι ℝ)
    (hF : polynomialDerivative v (polynomialDerivative v F) = 0) (r : ℕ) :
    (polynomialDerivative v : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[r+1] (F*G) =
      F * (polynomialDerivative v : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[r+1] G +
        ((r+1:ℕ):ℝ) • ((polynomialDerivative v F) *
          (polynomialDerivative v : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[r] G) := by
  induction r with
  | zero =>
    simp only [Nat.zero_add, Function.iterate_one, Function.iterate_zero_apply,
      Nat.cast_one, one_smul]
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    ring
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, map_add, Derivation.map_smul, Derivation.leibniz,
      Derivation.leibniz, hF]
    simp only [smul_eq_mul, MvPolynomial.smul_eq_C_mul, mul_zero, add_zero,
      Function.iterate_succ_apply', Nat.cast_add, Nat.cast_one, map_add, map_one]
    ring

theorem derivative_pullback_X {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (p : ι → κ) (k : ι) (i : κ) :
    polynomialDerivative (Pi.single k 1) (pullback p (MvPolynomial.X i)) =
      (MvPolynomial.C ((Pi.single (p k) (1:ℝ) : κ → ℝ) i) : MvPolynomial ι ℝ) := by
  classical
  simp [pullback, blockVariable, polynomialDerivative_X, Pi.single_apply, eq_comm]

theorem derivative_pullback {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (p : ι → κ) (k : ι) (F : MvPolynomial κ ℝ) :
    polynomialDerivative (Pi.single k 1) (pullback p F) =
      pullback p (polynomialDerivative (Pi.single (p k) 1) F) := by
  induction F using MvPolynomial.induction_on with
  | C c =>
    rw [show pullback p (MvPolynomial.C c) = MvPolynomial.C c from (pullback p).commutes c,
      polynomialDerivative_C, polynomialDerivative_C, map_zero]
  | add F G hF hG => simp only [map_add, hF, hG]
  | mul_X F i hF =>
    rw [map_mul, Derivation.leibniz, Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul]
    rw [hF, derivative_pullback_X, polynomialDerivative_X]
    rw [show pullback p (MvPolynomial.C ((Pi.single (p k) (1:ℝ) : κ → ℝ) i)) =
      MvPolynomial.C ((Pi.single (p k) (1:ℝ) : κ → ℝ) i) from (pullback p).commutes _]

theorem actual_affine_stein {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i)
    (j : ι) (F G : MvPolynomial ι ℝ)
    (hF : polynomialDerivative (Pi.single j 1) (polynomialDerivative (Pi.single j 1) F) = 0) :
    HigherHeatMultivariateMoments.mean m hm t ht ((F * MvPolynomial.X j) * G) =
      (((2*m:ℕ):ℝ)*PureOrderPolynomialConditioning.parameters m t j) •
        (HigherHeatMultivariateMoments.mean m hm t ht
          (F * (polynomialDerivative (Pi.single j 1) : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[2*m-1] G) +
        ((2*m-1:ℕ):ℝ) • HigherHeatMultivariateMoments.mean m hm t ht
          ((polynomialDerivative (Pi.single j 1) F) *
            (polynomialDerivative (Pi.single j 1) : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[2*m-2] G)) := by
  rw [mul_comm F (MvPolynomial.X j), mul_assoc, actual_coordinate_stein]
  have he : 2*m-1 = (2*m-2)+1 := by omega
  rw [he, derivative_mul_affine _ F G hF (2*m-2), map_add, map_smul]

end OperatorDerivativeRewrite.Foundation.HigherHeatAffineStepCorrection
