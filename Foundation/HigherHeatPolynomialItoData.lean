import Foundation.HigherHeatPolynomialPredictableField
import Foundation.HigherHeatAllChannelLimit

/-! Native polynomial telescoping for the all-order signed Itô identity. -/
noncomputable section
open scoped NNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatPolynomialItoData
open HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain HigherHeatCompletedPairing
open HigherHeatQuadraticItoData HigherHeatPolynomialPredictableField HigherHeatAllChannelLimit

theorem binomial_increment {R : Type*} [CommRing R] (a b : R) (N : ℕ) :
    (a+b)^N-a^N = ∑ q ∈ Finset.range N, N.choose (q+1) • (a^(N-(q+1))*b^(q+1)) := by
  rw [add_comm a b, add_pow, Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one,
    mul_one, add_sub_cancel_right]
  apply Finset.sum_congr rfl
  intro q _
  simp only [nsmul_eq_mul]
  ring

theorem power_telescope (n N : ℕ) :
    (HigherHeatMultivariateMoments.terminal : Test n)^N-(0:Test n)^N =
      ∑ q ∈ Finset.range N, N.choose (q+1) •
        powerPolynomial n (q+1) (powerPast n (N-(q+1))) := by
  have ht := Finset.sum_range_sub (fun c => (prefixPolynomial n c)^N) (size n)
  have hf := Fin.sum_univ_eq_sum_range
    (fun c => (prefixPolynomial n (c+1))^N-(prefixPolynomial n c)^N) (size n)
  have hs : (∑ j : Fin (size n),
      ((prefixPolynomial n (j.val+1))^N-(prefixPolynomial n j.val)^N)) =
      (HigherHeatMultivariateMoments.terminal : Test n)^N-(0:Test n)^N := by
    rw [hf, ht, prefix_end, prefix_zero]
  have he (j : Fin (size n)) :
      (prefixPolynomial n (j.val+1))^N-(prefixPolynomial n j.val)^N =
        ∑ q ∈ Finset.range N, N.choose (q+1) • ((past n j)^(N-(q+1))*(MvPolynomial.X j)^(q+1)) := by
    rw [prefix_succ n j.val j.isLt]
    exact binomial_increment (past n j) (MvPolynomial.X j) N
  rw [← hs]
  simp only [he]
  rw [Finset.sum_comm]
  simp only [powerPolynomial, powerPast, Finset.smul_sum]

theorem native_identity (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (N : ℕ) :
    pairing m hm T hT (core (terminalCylinder^N-(0:Cylinder)^N)) =
      ∑ q ∈ Finset.range N, N.choose (q+1) • pairing m hm T hT
        (core (cylinderOf n (powerPolynomial n (q+1) (powerPast n (N-(q+1)))))) := by
  have hc : cylinderOf n ((HigherHeatMultivariateMoments.terminal : Test n)^N-(0:Test n)^N) =
      terminalCylinder^N-(0:Cylinder)^N := by
    simp only [map_sub, map_pow, map_zero, ← HigherHeatTerminalPositions.terminal_on_grid n]
  have h := congrArg (fun P : Test n => pairing m hm T hT (core (cylinderOf n P)))
    (power_telescope n N)
  rw [hc] at h
  simpa only [map_sum, map_nsmul] using h

end OperatorDerivativeRewrite.Foundation.HigherHeatPolynomialItoData
