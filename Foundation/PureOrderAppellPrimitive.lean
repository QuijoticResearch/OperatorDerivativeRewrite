import Foundation.PureOrderAppellTail

/-! The unique centered polynomial primitive, without a stochastic-integral assertion. -/
noncomputable section
open Polynomial
namespace OperatorDerivativeRewrite.Foundation.PureOrderAppellPrimitive
open PureOrderAppellCalculus PureOrderAppellExpansion PseudoPolynomialStein

def primitive (p : ℕ) (a : ℝ) : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ :=
  (basis p a).constr ℝ (fun n => (n+1:ℝ)⁻¹ • appell p a (n+1))

theorem primitive_appell (p : ℕ) (a : ℝ) (n : ℕ) :
    primitive p a (appell p a n) = (n+1:ℝ)⁻¹ • appell p a (n+1) := by
  rw [← basis_apply]
  exact (basis p a).constr_basis ℝ _ n

theorem derivative_primitive (p : ℕ) (a : ℝ) (P : Polynomial ℝ) :
    derivative (primitive p a P) = P := by
  have he : derivative.comp (primitive p a) = LinearMap.id := by
    apply (basis p a).ext
    intro n
    rw [LinearMap.comp_apply, basis_apply, primitive_appell, derivative_smul,
      appell_derivative, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
    rfl
  exact LinearMap.congr_fun he P

theorem primitive_mean_zero (p : ℕ) (a : ℝ) (P : Polynomial ℝ) :
    expectation p a (primitive p a P) = 0 := by
  have he : (expectation p a).comp (primitive p a) = 0 := by
    apply (basis p a).ext
    intro n
    rw [LinearMap.comp_apply, basis_apply, primitive_appell, map_smul, appell_mean_zero,
      smul_zero]
    rfl
  exact LinearMap.congr_fun he P

theorem zero_of_derivative_mean_zero (p : ℕ) (a : ℝ) (P : Polynomial ℝ)
    (hd : derivative P = 0) (he : expectation p a P = 0) : P = 0 := by
  have hc := eq_C_of_derivative_eq_zero hd
  rw [hc, PseudoFiniteGramObstruction.expectation_C] at he
  rw [hc, he, C_0]

theorem primitive_unique (p : ℕ) (a : ℝ) (P Q : Polynomial ℝ)
    (hd : derivative Q = P) (he : expectation p a Q = 0) : Q = primitive p a P := by
  apply sub_eq_zero.mp
  apply zero_of_derivative_mean_zero p a
  · rw [map_sub, hd, derivative_primitive, sub_self]
  · rw [map_sub, he, primitive_mean_zero, sub_self]

theorem primitive_derivative (p : ℕ) (a : ℝ) (P : Polynomial ℝ) :
    primitive p a (derivative P) = P-C (expectation p a P) := by
  symm
  apply primitive_unique p a
  · simp
  · rw [map_sub, PseudoFiniteGramObstruction.expectation_C, sub_self]


open PureOrderAppellTail

def recover (p : ℕ) (a : ℝ) (r : ℕ) : Module.End ℝ (Polynomial ℝ) :=
  (primitive p a)^r * derivative^r

theorem recover_succ (p : ℕ) (a : ℝ) (r : ℕ) (P : Polynomial ℝ) :
    recover p a (r+1) P = primitive p a (recover p a r (derivative P)) := by
  unfold recover
  rw [pow_succ' (primitive p a), pow_succ (derivative : Module.End ℝ (Polynomial ℝ))]
  rfl

theorem recover_appell (p : ℕ) (a : ℝ) (r n : ℕ) :
    recover p a r (appell p a n) = if n < r then 0 else appell p a n := by
  induction r generalizing n with
  | zero => simp [recover]
  | succ r ih =>
    cases n with
    | zero => simp [recover_succ, appell]
    | succ n =>
      rw [recover_succ, appell_derivative, map_smul, ih]
      by_cases hn : n < r
      · simp [hn]
      · simp only [ite_eq_right hn, map_smul, primitive_appell]
        rw [smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
        simp [hn]

def lowOperator (p : ℕ) (a : ℝ) (r : ℕ) : Module.End ℝ (Polynomial ℝ) where
  toFun := lowPart p a r
  map_add' P Q := by
    simp only [lowPart, map_add, add_smul, Finset.sum_add_distrib]
  map_smul' c P := by
    simp only [lowPart, map_smul, Finset.smul_sum, smul_smul, smul_eq_mul, RingHom.id_apply]

def tailOperator (p : ℕ) (a : ℝ) (r : ℕ) : Module.End ℝ (Polynomial ℝ) :=
  LinearMap.id - lowOperator p a r

theorem tailOperator_apply (p : ℕ) (a : ℝ) (r : ℕ) (P : Polynomial ℝ) :
    tailOperator p a r P = tailPart p a r P := rfl

theorem tail_appell (p : ℕ) (a : ℝ) (r n : ℕ) :
    tailPart p a r (appell p a n) = if n < r then 0 else appell p a n := by
  by_cases hn : n < r <;> simp [tailPart, lowPart, coordinate_appell, hn]

theorem recover_eq_tailOperator (p : ℕ) (a : ℝ) (r : ℕ) :
    recover p a r = tailOperator p a r := by
  apply (basis p a).ext
  intro n
  rw [basis_apply, recover_appell, tailOperator_apply, tail_appell]

theorem recover_eq_tail (p : ℕ) (a : ℝ) (r : ℕ) (P : Polynomial ℝ) :
    recover p a r P = tailPart p a r P := by
  rw [recover_eq_tailOperator, tailOperator_apply]

end OperatorDerivativeRewrite.Foundation.PureOrderAppellPrimitive
