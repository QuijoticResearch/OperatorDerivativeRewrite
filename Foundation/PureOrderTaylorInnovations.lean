import Foundation.PureOrderAppellTransition
import Mathlib.Algebra.Polynomial.Taylor

/-! Exact signed Taylor innovations with canonical derivative coefficients. -/
noncomputable section
open Polynomial MeasureTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.PureOrderTaylorInnovations
open PseudoPolynomialStein PseudoFiniteGramObstruction

def innovation (p : ℕ) (a : ℝ) (r : ℕ) : Polynomial ℝ := X^r-C (moment p a r)

theorem innovation_zero (p : ℕ) (a : ℝ) : innovation p a 0 = 0 := by
  simp [innovation, moment_zero]

theorem innovation_mean (p : ℕ) (a : ℝ) (r : ℕ) :
    expectation p a (innovation p a r) = 0 := by
  rw [innovation, map_sub, expectation_X_pow, expectation_C, sub_self]

theorem innovation_coeff (p : ℕ) (a : ℝ) (r k : ℕ) (hk : 0 < k) :
    (innovation p a r).coeff k = if k = r then 1 else 0 := by
  simp only [innovation, coeff_sub, coeff_X_pow, coeff_C, hk.ne', ite_false, sub_zero]

def centering (p : ℕ) (a : ℝ) : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ :=
  LinearMap.id - ((Polynomial.CAlgHom : ℝ →ₐ[ℝ] Polynomial ℝ).toLinearMap.comp (expectation p a))

theorem centering_apply (p : ℕ) (a : ℝ) (P : Polynomial ℝ) :
    centering p a P = P-C (expectation p a P) := rfl

theorem centered_expansion (p : ℕ) (a : ℝ) (P : Polynomial ℝ) :
    centering p a P = ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k • innovation p a k := by
  have he : P = ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k • (X : Polynomial ℝ)^k := by
    simpa only [smul_eq_C_mul] using P.as_sum_range_C_mul_X_pow
  conv_lhs => rw [he]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [centering_apply, expectation_X_pow]
  rfl

theorem hasse_eval_derivative (P : Polynomial ℝ) (r : ℕ) (x : ℝ) :
    (hasseDeriv r P).eval x = ((derivative^[r] P).eval x)/(r.factorial : ℝ) := by
  have he := congrArg (fun f : Polynomial ℝ → Polynomial ℝ => (f P).eval x)
    (Polynomial.factorial_smul_hasseDeriv (R := ℝ) (k := r))
  change (r.factorial • (hasseDeriv r P)).eval x = (derivative^[r] P).eval x at he
  rw [← Nat.cast_smul_eq_nsmul ℝ, eval_smul] at he
  simp only [smul_eq_mul] at he
  apply (eq_div_iff (by positivity : (r.factorial : ℝ) ≠ 0)).mpr
  simpa only [mul_comm] using he

theorem centered_taylor (p : ℕ) (a x : ℝ) (P : Polynomial ℝ) :
    centering p a (taylor x P) = ∑ k ∈ Finset.range (P.natDegree + 1),
      (((derivative^[k] P).eval x)/(k.factorial : ℝ)) • innovation p a k := by
  rw [centered_expansion, natDegree_taylor]
  apply Finset.sum_congr rfl
  intro k hk
  rw [taylor_coeff, hasse_eval_derivative]

theorem centered_taylor_eval (p : ℕ) (a x z : ℝ) (P : Polynomial ℝ) :
    P.eval (x + z)-expectation p a (taylor x P) =
      ∑ k ∈ Finset.range (P.natDegree + 1),
      (((derivative^[k] P).eval x)/(k.factorial : ℝ)) * (z^k-moment p a k) := by
  have he := congrArg (fun Q : Polynomial ℝ => Q.eval z) (centered_taylor p a x P)
  simpa only [centering_apply, eval_sub, eval_C, taylor_eval, add_comm z x,
    eval_finsetSum, eval_smul, smul_eq_mul, innovation, eval_pow, eval_X] using he

def representation (p : ℕ) (a : ℝ) (N : ℕ) : (Fin N → ℝ) →ₗ[ℝ] Polynomial ℝ :=
  ∑ k : Fin N, (LinearMap.toSpanSingleton ℝ (Polynomial ℝ) (innovation p a (k.val + 1))).comp
    (LinearMap.proj k)

theorem representation_apply (p : ℕ) (a : ℝ) (N : ℕ) (c : Fin N → ℝ) :
    representation p a N c = ∑ k : Fin N, c k • innovation p a (k.val + 1) := by
  simp [representation]

theorem representation_coeff (p : ℕ) (a : ℝ) (N : ℕ) (c : Fin N → ℝ) (i : Fin N) :
    (representation p a N c).coeff (i.val + 1) = c i := by
  rw [representation_apply, finsetSum_coeff]
  simp only [coeff_smul, smul_eq_mul, innovation_coeff p a _ (i.val + 1) (Nat.zero_lt_succ i.val)]
  have he (k : Fin N) : (i.val + 1 = k.val + 1) ↔ i = k := by simp [Fin.ext_iff]
  simp only [he, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem representation_injective (p : ℕ) (a : ℝ) (N : ℕ) :
    Function.Injective (representation p a N) := by
  intro c d he
  funext i
  simpa only [representation_coeff] using congrArg (fun P : Polynomial ℝ => P.coeff (i.val + 1)) he

theorem actual_taylor_eval (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (x z : ℝ) (P : Polynomial ℝ) :
    P.eval (x + z)-HigherHeatPolynomialRealization.kernelExpectation m hm t ht (taylor x P) =
      ∑ k ∈ Finset.range (P.natDegree + 1),
      (((derivative^[k] P).eval x)/(k.factorial : ℝ)) *
      (z^k-moment (2 * m) ((-1 : ℝ)^(m + 1)*(t : ℝ)) k) := by
  rw [HigherHeatPolynomialRealization.kernelExpectation_eq_moments]
  exact centered_taylor_eval (2 * m) _ x z P

theorem actual_innovation_integrable (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (r : ℕ) : (HigherHeatSignedLaws.law m hm t ht).Integrable (fun z : ℝ =>
      (((innovation (2 * m) ((-1 : ℝ)^(m + 1)*(t : ℝ)) r).eval z : ℝ) : ℂ)) :=
  HigherHeatSignedPolynomialCalculus.polynomial_signed_integrable m hm t ht _

theorem actual_innovation_mean (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (r : ℕ) :
    (∫ᵛ z : ℝ, (((innovation (2 * m) ((-1 : ℝ)^(m + 1)*(t : ℝ)) r).eval z : ℝ) : ℂ)
      ∂<•HigherHeatSignedLaws.law m hm t ht) = 0 := by
  rw [HigherHeatSignedPolynomialCalculus.signed_polynomial_integral,
    HigherHeatPolynomialRealization.kernelExpectation_eq_moments, innovation_mean,
    Complex.ofReal_zero]

def coefficients (P : Polynomial ℝ) (x : ℝ) : Fin P.natDegree → ℝ :=
  fun k => ((derivative^[k.val + 1] P).eval x)/((k.val + 1).factorial : ℝ)

theorem canonical_reconstruction (p : ℕ) (a x : ℝ) (P : Polynomial ℝ) :
    centering p a (taylor x P) = representation p a P.natDegree (coefficients P x) := by
  rw [centered_taylor, Finset.sum_range_succ', innovation_zero, smul_zero, add_zero,
    representation_apply]
  simp only [coefficients]
  exact (Fin.sum_univ_eq_sum_range
    (fun k : ℕ => (((derivative^[k + 1] P).eval x)/((k + 1).factorial : ℝ)) •
      innovation p a (k + 1)) P.natDegree).symm

theorem canonical_unique (p : ℕ) (a x : ℝ) (P : Polynomial ℝ) (c : Fin P.natDegree → ℝ)
    (hc : representation p a P.natDegree c = centering p a (taylor x P)) :
    c = coefficients P x :=
  representation_injective p a P.natDegree (hc.trans (canonical_reconstruction p a x P))

theorem representation_pointwise_unique (p : ℕ) (a : ℝ) (N : ℕ) {α : Type*}
    (c d : α → Fin N → ℝ)
    (h : ∀ x z, (representation p a N (c x)).eval z = (representation p a N (d x)).eval z) :
    c = d := by
  funext x
  exact representation_injective p a N (Polynomial.funext (h x))

end OperatorDerivativeRewrite.Foundation.PureOrderTaylorInnovations
