import Foundation.HigherHeatCylinderDilation

/-! Homogeneous dilation of the actual even-order signed polynomial cylinder laws. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.HigherHeatDilationLaw
open PseudoPolynomialStein HigherHeatPolynomialCylinders HigherHeatCylinderDilation
open MultivariateFactorialSubstitution MultivariateFactorialDampedProduct
open HigherHeatMultivariateMoments PureOrderPolynomialConditioning
open scoped NNReal BigOperators

theorem moment_scale (p : ℕ) (hp : 0 < p) (a c : ℝ) (n : ℕ) :
    moment p (c^p*a) n = c^n * moment p a n := by
  by_cases hn : p ∣ n
  · obtain ⟨k, rfl⟩ := hn
    rw [moment_multiple p hp, moment_multiple p hp, mul_pow, ← pow_mul]
    ring
  · rw [moment_off_order p hp _ n hn, moment_off_order p hp _ n hn, mul_zero]

def horizon (m : ℕ) (T : ℝ≥0) : ℝ≥0 := (2:ℝ≥0)^(2*m)*T

theorem horizon_pos (m : ℕ) (T : ℝ≥0) (hT : 0 < T) : 0 < horizon m T := by
  unfold horizon
  positivity

theorem parameter_scale (m : ℕ) (T : ℝ≥0) (n : ℕ) (i : Fin (size n)) :
    parameters m (fun _ : Fin (size n) => HigherHeatDyadicLaws.duration (horizon m T) n) i =
      (2:ℝ)^(2*m)*parameters m (fun _ : Fin (size n) => HigherHeatDyadicLaws.duration T n) i := by
  simp only [parameters, HigherHeatDyadicLaws.duration, horizon, NNReal.coe_div,
    NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat]
  ring

theorem expectation_dilation (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (P : Test n) :
    expectation m hm (horizon m T) (horizon_pos m T hT) n (gridDilation (1/2) n P) =
      expectation m hm T hT n P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, map_add, map_add, hP, hQ]
  | monomial d c =>
    change HigherHeatMultivariateMoments.mean _ _ _ _
      (polynomialSubstitution id (fun _ => (1/2:ℝ)) (MvPolynomial.monomial d c)) = _
    rw [dilation_monomial, actual_mean_monomial]
    change ((_ : ℝ):ℂ) = HigherHeatMultivariateMoments.mean _ _ _ _ (MvPolynomial.monomial d c)
    rw [actual_mean_monomial]
    apply congrArg (fun x : ℝ => (x:ℂ))
    simp_rw [parameter_scale, moment_scale (2*m) (by omega)]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    have hd : ∑ i : Fin (size n), d i = d.degree := by
      exact (Finsupp.sum_fintype d (fun _ k => k) (fun _ => rfl)).symm
    rw [hd, div_pow, one_pow]
    field_simp

theorem cylinder_dilation (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (F : Cylinder) :
    cylindricalExpectation m hm (horizon m T) (horizon_pos m T hT) (dilation (1/2) F) =
      cylindricalExpectation m hm T hT F := by
  induction F using DirectLimit.induction with
  | _ n P =>
    change cylindricalExpectation m hm (horizon m T) (horizon_pos m T hT)
      (dilation (1/2) (cylinderOf n P)) = cylindricalExpectation m hm T hT (cylinderOf n P)
    rw [dilation_core, cylindricalExpectation_apply, cylindricalExpectation_apply]
    exact expectation_dilation m hm T hT n P

end OperatorDerivativeRewrite.Foundation.HigherHeatDilationLaw
