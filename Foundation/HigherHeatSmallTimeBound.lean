import Foundation.HigherHeatPositionTransport

/-! Degree-independent small-time error of the actual completed heat operator.
The estimate applies to the signed polynomial transport through its verified
position-coordinate realization; it assumes no positive stochastic measure. -/
noncomputable section

namespace OperatorDerivativeRewrite.Foundation.HigherHeatSmallTimeBound
open MultivariateFactorialDomain MultivariateFactorialHeat
open HigherHeatPolynomialCylinders HigherHeatPolynomialCoordinates
open HigherHeatPositionTransport MultivariateDirectionalKernel

theorem evolution_sub_identity_bound {ι : Type*} [DecidableEq ι]
    (p : ℕ) (a : ℝ) (v : ι → ℝ) (hv : ∀ i, |v i| ≤ 1) (u : H ι) :
    ‖evolution p a v hv u - u‖ ≤ (Real.exp |a| - 1) * ‖u‖ := by
  have hs := (hasSum_nat_add_iff' 1).mpr (evolution_series p a v hv u)
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, mul_zero, one_smul] at hs
  have hr : HasSum (fun k : ℕ => (k.factorial : ℝ)⁻¹ * |a|^k) (Real.exp |a|) := by
    simpa only [smul_eq_mul, Real.exp_eq_exp_ℝ] using
      NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) |a|
  have ht := ((hasSum_nat_add_iff' 1).mpr hr).mul_right ‖u‖
  simp only [Finset.sum_range_one, Nat.factorial_zero, Nat.cast_one,
    inv_one, pow_zero, one_mul] at ht
  apply hs.norm_le_of_bounded ht
  intro k
  rw [norm_smul, Real.norm_eq_abs, abs_div, abs_pow,
    abs_of_pos (by positivity : (0:ℝ) < ((k+1).factorial:ℝ))]
  have h : ‖(derivative v hv ^ (p*(k+1))) u‖ ≤ ‖u‖ := by
    simpa only [one_mul] using (derivative v hv ^ (p*(k+1))).le_of_opNorm_le
      (derivative_power_norm v hv (p*(k+1))) u
  calc
    _ ≤ (|a|^(k+1) / ((k+1).factorial:ℝ)) * ‖u‖ := by gcongr
    _ = _ := by ring

theorem transport_sub_identity_bound (n p : ℕ) (hp : 0 < p) (a : ℝ)
    (j : Fin (size n)) (P : Test n) :
    ‖encode n (transport p hp a (Pi.single j 1) P) - encode n P‖ ≤
      (Real.exp |a| - 1) * ‖encode n P‖ := by
  rw [← evolution_encode n p hp a j P]
  exact evolution_sub_identity_bound p a _ _ _

end OperatorDerivativeRewrite.Foundation.HigherHeatSmallTimeBound
