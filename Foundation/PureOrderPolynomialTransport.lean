import Foundation.PureOrderTaylorInnovations

/-! Actual polynomial heat transport and its exact full-power innovation step. -/
noncomputable section
open Polynomial MeasureTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.PureOrderPolynomialTransport
open PureOrderAppellCalculus PureOrderAppellExpansion PureOrderAppellTransition
open PureOrderTaylorInnovations PseudoPolynomialStein

def transport (p : ℕ) (a : ℝ) : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ :=
  (basis p a).constr ℝ (appell p 0)

theorem transport_basis (p : ℕ) (a : ℝ) (n : ℕ) :
    transport p a (appell p a n) = appell p 0 n := by
  rw [← basis_apply p a n]
  exact Module.Basis.constr_basis _ _ _ _

theorem transport_eval (p : ℕ) (hp : 1 < p) (a x : ℝ) (P : Polynomial ℝ) :
    (transport p a P).eval x = expectation p a (taylor x P) := by
  have he : (Polynomial.leval x).comp (transport p a) =
      (expectation p a).comp (taylor x) := by
    apply (basis p a).ext
    intro n
    simp only [LinearMap.comp_apply, basis_apply, transport_basis, Polynomial.leval_apply]
    have ht : expectation p a (taylor x (appell p a n)) = (appell p 0 n).eval x := by
      simpa only [add_zero, shift, taylor_apply] using appell_transition p hp a 0 n x
    exact ht.symm
  exact LinearMap.congr_fun he P

theorem transport_appell (p : ℕ) (hp : 1 < p) (a b : ℝ) (n : ℕ) :
    transport p a (appell p (a + b) n) = appell p b n := by
  apply Polynomial.funext
  intro x
  rw [transport_eval p hp]
  exact appell_transition p hp a b n x

theorem transport_zero (p : ℕ) : transport p 0 = LinearMap.id := by
  apply (basis p 0).ext
  intro n
  rw [basis_apply, transport_basis, LinearMap.id_apply]

theorem transport_add (p : ℕ) (hp : 1 < p) (a b : ℝ) :
    (transport p a).comp (transport p b) = transport p (a + b) := by
  apply (basis p (a + b)).ext
  intro n
  simp only [LinearMap.comp_apply, basis_apply]
  have hb : transport p b (appell p (a + b) n) = appell p a n := by
    simpa only [add_comm a b] using transport_appell p hp b a n
  rw [hb, transport_basis, transport_basis]

theorem transport_derivative (p : ℕ) (a : ℝ) :
    Polynomial.derivative.comp (transport p a) = (transport p a).comp Polynomial.derivative := by
  apply (basis p a).ext
  intro n
  simp only [LinearMap.comp_apply, basis_apply]
  rw [transport_basis]
  cases n with
  | zero => simp only [appell, derivative_one, map_zero]
  | succ n => rw [appell_derivative, appell_derivative, map_smul, transport_basis]

theorem transport_iterate_derivative (p : ℕ) (a : ℝ) (r : ℕ) (P : Polynomial ℝ) :
    derivative^[r] (transport p a P) = transport p a (derivative^[r] P) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    exact LinearMap.congr_fun (transport_derivative p a) _

theorem actual_kernel_transport (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (P : Polynomial ℝ) (x : ℝ) :
    (∫ y : ℝ, P.eval (x + y) * HigherHeatSignedLaws.realKernel m hm t ht y) =
      (transport (2 * m) ((-1 : ℝ)^(m + 1)*(t : ℝ)) P).eval x := by
  rw [transport_eval (2 * m) (by omega),
    ← HigherHeatPolynomialRealization.kernelExpectation_eq_moments m hm t ht]
  simp only [HigherHeatPolynomialRealization.kernelExpectation, LinearMap.coe_mk,
    AddHom.coe_mk, taylor_eval, add_comm]

theorem exact_innovation_step (p : ℕ) (hp : 1 < p) (a b x z : ℝ) (P : Polynomial ℝ) :
    (transport p b P).eval (x + z) - (transport p (a + b) P).eval x =
      ∑ k ∈ Finset.range ((transport p b P).natDegree+1),
      (((derivative^[k] (transport p b P)).eval x)/(k.factorial : ℝ)) *
      (z^k-moment p a k) := by
  have he := centered_taylor_eval p a x z (transport p b P)
  rw [← transport_eval p hp] at he
  have hc : transport p a (transport p b P) = transport p (a + b) P :=
    LinearMap.congr_fun (transport_add p hp a b) P
  rw [hc] at he
  exact he

end OperatorDerivativeRewrite.Foundation.PureOrderPolynomialTransport
