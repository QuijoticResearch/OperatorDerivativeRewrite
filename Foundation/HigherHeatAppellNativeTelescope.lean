import Foundation.HigherHeatAppellInnovationLimits
import Foundation.PureOrderAppellCenteredStep

/-! Exact native-grid backward Appell telescope with every centered innovation
power retained. No stochastic limit is taken in this algebraic identity. -/
noncomputable section
open scoped NNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatAppellNativeTelescope
open HigherHeatPolynomialCylinders HigherHeatQuadraticItoData
open HigherHeatAppellPredictableFields HigherHeatAppellInnovationLimits
open HigherHeatWeightedPastFields HigherHeatDyadicTimeDensity HigherHeatCenteredPowerLimits
open PureOrderAppellCalculus PureOrderAppellParameter PureOrderAppellCenteredStep
open HigherHeatInnovationMoments HigherHeatDyadicStepAgreement

def prefixAppell (n m : ℕ) (T : ℝ≥0) (N c : ℕ) : Test n :=
  Polynomial.aeval (prefixPolynomial n c)
    (appell (2*m) (parameter m T*((c:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ)-1)) N)

theorem eval_aeval (n : ℕ) (x : Fin (size n) → ℝ) (F : Test n) (P : Polynomial ℝ) :
    MvPolynomial.eval x (Polynomial.aeval F P) = P.eval (MvPolynomial.eval x F) := by
  simpa only [MvPolynomial.aeval_eq_eval, Polynomial.coe_aeval_eq_eval] using
    (Polynomial.aeval_algHom_apply (MvPolynomial.aeval x) F P).symm

theorem right_time (n : ℕ) (j : Fin (size n)) :
    (rightNode n j:ℝ) = ((j.val:ℝ)+1)*(HigherHeatDyadicLaws.duration 1 n:ℝ) := by
  change HigherHeatContinuousCylinders.interpolationNode n
    (prefixNode n (j.val+1) (by omega)) = _
  rw [prefixNode_time]
  simp only [HigherHeatDyadicLaws.duration, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_natCast, Nat.cast_add, Nat.cast_one]
  ring

theorem prefix_step (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (N : ℕ) (j : Fin (size n)) :
    prefixAppell n m T N (j.val+1)-prefixAppell n m T N j.val =
      ∑ r ∈ Finset.range N, canonicalPast n m T N (r+1) j *
        ((MvPolynomial.X j)^(r+1)-MvPolynomial.C (cellMoment n m T (r+1))) := by
  apply MvPolynomial.funext
  intro x
  have hp : parameter m T*(HigherHeatDyadicLaws.duration 1 n:ℝ) +
      parameter m T*((j.val:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ)-1) =
      parameter m T*(((j.val:ℝ)+1)*(HigherHeatDyadicLaws.duration 1 n:ℝ)-1) := by ring
  have hc : parameter m T*(HigherHeatDyadicLaws.duration 1 n:ℝ) =
      (-1:ℝ)^(m+1)*(HigherHeatDyadicLaws.duration T n:ℝ) := by
    rw [parameter, mul_assoc, duration_scale]
  have h := centered_step (2*m) (by omega)
    (parameter m T*(HigherHeatDyadicLaws.duration 1 n:ℝ))
    (parameter m T*((j.val:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ)-1)) N
    (MvPolynomial.eval x (past n j)) (x j)
  rw [hp] at h
  simp only [prefixAppell, map_sub, eval_aeval, prefix_succ n j.val j.isLt,
    map_add, MvPolynomial.eval_X, Nat.cast_add, Nat.cast_one, canonicalPast,
    map_sum, map_mul, map_pow, MvPolynomial.smul_eq_C_mul, MvPolynomial.eval_C, appellPast,
    right_time, cellMoment, ← hc, smul_eq_mul]
  exact h

theorem prefix_initial (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (N : ℕ) :
    prefixAppell n m T N 0 = MvPolynomial.C (PseudoPolynomialStein.moment (2*m) (parameter m T) N) := by
  apply MvPolynomial.funext
  intro x
  simp only [prefixAppell, prefix_zero, eval_aeval, map_zero, Nat.cast_zero,
    zero_mul, zero_sub, mul_neg_one, MvPolynomial.eval_C]
  exact initial_mean (2*m) (by omega) (parameter m T) N

theorem prefix_terminal (n m : ℕ) (T : ℝ≥0) (N : ℕ) :
    prefixAppell n m T N (size n) = (HigherHeatMultivariateMoments.terminal : Test n)^N := by
  rw [prefixAppell, HigherHeatQuadraticChannelLimit.size_duration, sub_self,
    mul_zero, zero_parameter, map_pow, Polynomial.aeval_X, prefix_end]

theorem telescope (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (N : ℕ) :
    (HigherHeatMultivariateMoments.terminal : Test n)^N -
      MvPolynomial.C (PseudoPolynomialStein.moment (2*m) (parameter m T) N) =
      ∑ r ∈ Finset.range N, centeredPower n m T (r+1) (canonicalPast n m T N (r+1)) := by
  have hs := Finset.sum_range_sub (prefixAppell n m T N) (size n)
  have hf := Fin.sum_univ_eq_sum_range
    (fun c => prefixAppell n m T N (c+1)-prefixAppell n m T N c) (size n)
  rw [prefix_initial n m hm T N, prefix_terminal n m T N] at hs
  rw [← hs, ← hf]
  simp only [prefix_step n m hm T N]
  rw [Finset.sum_comm]
  rfl

end OperatorDerivativeRewrite.Foundation.HigherHeatAppellNativeTelescope
