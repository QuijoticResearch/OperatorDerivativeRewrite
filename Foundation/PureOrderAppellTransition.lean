import Foundation.PureOrderAppellPairing
import Foundation.HigherHeatSignedPolynomialCalculus

/-! Actual polynomial backward transport for pure-order Appell observables. -/
noncomputable section
open Polynomial MeasureTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.PureOrderAppellTransition
open PureOrderAppellCalculus PureOrderAppellExpansion PureOrderAppellPairing
open PseudoPolynomialStein PseudoClarkOconeObstruction

def shift (x : ℝ) (P : Polynomial ℝ) : Polynomial ℝ := P.comp (X+C x)

theorem shift_smul (x c : ℝ) (P : Polynomial ℝ) :
    shift x (c • P) = c • shift x P := by simp [shift, smul_eq_C_mul]

theorem derivative_shift (x : ℝ) (P : Polynomial ℝ) :
    derivative (shift x P) = shift x (derivative P) := by simp [shift, derivative_comp]

theorem iterate_shift (x : ℝ) (r : ℕ) (P : Polynomial ℝ) :
    derivative^[r] (shift x P) = shift x (derivative^[r] P) := by
  induction r generalizing P with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply, derivative_shift, ih,
      Function.iterate_succ_apply]

theorem shifted_raise_mean (p : ℕ) (a b x : ℝ) (P : Polynomial ℝ) :
    expectation p a (shift x (raise p (a+b) P)) =
      x * expectation p a (shift x P) -
        (p:ℝ)*b*expectation p a (shift x (derivative^[p-1] P)) := by
  have he : shift x (raise p (a+b) P) = X*shift x P + x • shift x P -
      ((p:ℝ)*(a+b)) • shift x (derivative^[p-1] P) := by
    simp only [shift, raise, sub_comp, mul_comp, X_comp, smul_comp]
    simp only [smul_eq_C_mul]
    ring
  rw [he, map_sub, map_add, map_smul, map_smul, polynomial_stein, iterate_shift]
  simp only [smul_eq_mul]
  ring

theorem appell_transition (p : ℕ) (hp : 1 < p) (a b : ℝ) (n : ℕ) (x : ℝ) :
    expectation p a (shift x (appell p (a+b) n)) = (appell p b n).eval x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [appell, shift, PseudoFiniteGramObstruction.expectation_one]
    | succ n =>
      rw [appell, shifted_raise_mean, ih n (by omega)]
      by_cases hn : n=0
      · subst n
        have hq : 0 < p-1 := by omega
        simp [appell, raise, iterate_derivative_one hq, shift]
      · rw [appell_iterate, shift_smul, map_smul, ih (n-(p-1)) (by omega)]
        simp only [appell, raise, appell_iterate, eval_sub, eval_mul, eval_X,
          eval_smul, smul_eq_mul]

theorem actual_kernel_transition (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (b x : ℝ) (n : ℕ) :
    (∫ y : ℝ, (appell (2*m) (((-1:ℝ)^(m+1)*(t:ℝ))+b) n).eval (x+y) *
      HigherHeatSignedLaws.realKernel m hm t ht y) = (appell (2*m) b n).eval x := by
  have he := appell_transition (2*m) (by omega) ((-1:ℝ)^(m+1)*(t:ℝ)) b n x
  rw [← HigherHeatPolynomialRealization.kernelExpectation_eq_moments m hm t ht] at he
  simpa only [HigherHeatPolynomialRealization.kernelExpectation, LinearMap.coe_mk,
    AddHom.coe_mk, shift, eval_comp, eval_add, eval_X, eval_C, add_comm] using he


theorem actual_signed_integrable (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (b x : ℝ) (n : ℕ) :
    (HigherHeatSignedLaws.law m hm t ht).Integrable (fun y : ℝ =>
      (((appell (2*m) (((-1:ℝ)^(m+1)*(t:ℝ))+b) n).eval (x+y):ℝ):ℂ)) := by
  have h := HigherHeatSignedPolynomialCalculus.polynomial_signed_integrable m hm t ht
    (shift x (appell (2*m) (((-1:ℝ)^(m+1)*(t:ℝ))+b) n))
  simpa only [shift, eval_comp, eval_add, eval_X, eval_C, add_comm] using h

theorem actual_signed_transition (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (b x : ℝ) (n : ℕ) :
    (∫ᵛ y : ℝ, (((appell (2*m) (((-1:ℝ)^(m+1)*(t:ℝ))+b) n).eval (x+y):ℝ):ℂ)
      ∂<•HigherHeatSignedLaws.law m hm t ht) = (((appell (2*m) b n).eval x:ℝ):ℂ) := by
  have h := HigherHeatSignedPolynomialCalculus.signed_polynomial_integral m hm t ht
    (shift x (appell (2*m) (((-1:ℝ)^(m+1)*(t:ℝ))+b) n))
  rw [HigherHeatPolynomialRealization.kernelExpectation_eq_moments,
    appell_transition (2*m) (by omega)] at h
  simpa only [shift, eval_comp, eval_add, eval_X, eval_C, add_comm] using h

end OperatorDerivativeRewrite.Foundation.PureOrderAppellTransition
