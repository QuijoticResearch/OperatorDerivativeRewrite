import Foundation.PureOrderPolynomialTransport
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Algebra.Exponential

/-! A complete factorial-coefficient space with a genuine bounded derivative. -/
noncomputable section
open Polynomial Filter
open scoped Topology ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.FactorialAnalyticDomain

abbrev H := lp (fun _ : ℕ => ℝ) 1

instance nontrivialH : Nontrivial H := by
  refine ⟨⟨lp.single 1 0 (0 : ℝ), lp.single 1 0 (1 : ℝ), ?_⟩⟩
  intro he
  have hh := congrArg (fun u : H => u 0) he
  simp at hh

theorem sum_norm (u : H) : Summable (fun n : ℕ => ‖u n‖) := by
  simpa only [ENNReal.toReal_one, Real.rpow_one] using u.property.summable (by norm_num)

theorem norm_eq_sum (u : H) : ‖u‖ = ∑' n : ℕ, ‖u n‖ := by
  simpa using lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal) u

def shiftLinear : H →ₗ[ℝ] H where
  toFun u := ⟨fun n => u (n + 1), by
    apply memℓp_gen
    simpa only [ENNReal.toReal_one, Real.rpow_one, Function.comp_def] using
      (sum_norm u).comp_injective Nat.succ_injective⟩
  map_add' u v := by ext n; rfl
  map_smul' c u := by ext n; rfl

theorem shiftLinear_norm (u : H) : ‖shiftLinear u‖ ≤ ‖u‖ := by
  rw [norm_eq_sum, norm_eq_sum]
  exact tsum_comp_le_tsum_of_inj (sum_norm u) (fun n => norm_nonneg (u n)) Nat.succ_injective

def shift : H →L[ℝ] H := shiftLinear.mkContinuous 1 (by simpa using shiftLinear_norm)

theorem shift_apply (u : H) (n : ℕ) : shift u n = u (n + 1) := rfl

theorem shift_norm_le : ‖shift‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound shift (by norm_num) (by
    intro u
    change ‖shiftLinear u‖ ≤ 1 * ‖u‖
    simpa using shiftLinear_norm u)

def polynomial (P : Polynomial ℝ) : H := ⟨fun n => (n.factorial : ℝ) * P.coeff n, by
  apply memℓp_gen
  apply summable_of_ne_finset_zero (s := P.support)
  intro n hn
  have hz : P.coeff n = 0 := by simpa only [mem_support_iff, not_not] using hn
  simp [hz]⟩

theorem polynomial_apply (P : Polynomial ℝ) (n : ℕ) :
    polynomial P n = (n.factorial : ℝ) * P.coeff n := rfl

def polynomialMap : Polynomial ℝ →ₗ[ℝ] H where
  toFun := polynomial
  map_add' P Q := by
    ext n
    simp only [polynomial_apply, coeff_add, lp.coeFn_add, Pi.add_apply]
    ring
  map_smul' c P := by
    ext n
    simp only [polynomial_apply, coeff_smul, smul_eq_mul, RingHom.id_apply,
      lp.coeFn_smul, Pi.smul_apply]
    ring

theorem polynomial_injective : Function.Injective polynomial := by
  intro P Q he
  ext n
  have h := congrArg (fun u : H => u n) he
  exact mul_left_cancel₀ (by positivity : (n.factorial : ℝ) ≠ 0) h

theorem polynomial_derivative (P : Polynomial ℝ) :
    polynomial P.derivative = shift (polynomial P) := by
  ext n
  simp only [polynomial_apply, shift_apply, coeff_derivative, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  ring

theorem polynomial_iterate_derivative (r : ℕ) (P : Polynomial ℝ) :
    polynomial (derivative^[r] P) = (shift^r) (polynomial P) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', polynomial_derivative, ih, pow_succ']
    rfl

theorem polynomial_monomial (n : ℕ) (c : ℝ) :
    polynomial (monomial n c) = lp.single 1 n ((n.factorial : ℝ)*c) := by
  ext k
  by_cases h : k = n
  · subst k
    simp [polynomial_apply]
  · simp [polynomial_apply, coeff_monomial, lp.single_apply, h, Ne.symm h]

theorem single_mem_range (n : ℕ) (c : ℝ) : lp.single 1 n c ∈ Set.range polynomial := by
  refine ⟨monomial n (c/(n.factorial : ℝ)), ?_⟩
  rw [polynomial_monomial]
  congr 1
  field_simp

theorem polynomial_dense : DenseRange polynomial := by
  intro u
  have hs := lp.hasSum_single (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) u
  apply isClosed_closure.mem_of_tendsto hs
  apply Eventually.of_forall
  intro s
  apply subset_closure
  have he : (∑ n ∈ s, lp.single 1 n (u n)) =
      polynomialMap (∑ n ∈ s, monomial n (u n/(n.factorial : ℝ))) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro n hn
    change lp.single 1 n (u n) = polynomial (monomial n (u n/(n.factorial : ℝ)))
    rw [polynomial_monomial]
    congr 1
    field_simp
  rw [he]
  exact ⟨_, rfl⟩

theorem shift_pow_apply (r : ℕ) (u : H) (n : ℕ) : (shift^r) u n = u (n + r) := by
  induction r generalizing n with
  | zero => rfl
  | succ r ih =>
    rw [pow_succ']
    change shift ((shift^r) u) n = _
    rw [shift_apply]
    exact (ih (n + 1)).trans (congrArg u (by omega))

theorem polynomial_norm (P : Polynomial ℝ) :
    ‖polynomial P‖ = ∑ n ∈ P.support, (n.factorial : ℝ) * |P.coeff n| := by
  rw [norm_eq_sum]
  rw [tsum_eq_sum (s := P.support)]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [polynomial_apply, norm_mul, Real.norm_eq_abs, Nat.abs_cast]
  · intro n hn
    have hz : P.coeff n = 0 := by simpa only [mem_support_iff, not_not] using hn
    simp [polynomial_apply, hz]

theorem monomial_norm (n : ℕ) (c : ℝ) :
    ‖polynomial (monomial n c)‖ = (n.factorial : ℝ) * |c| := by
  rw [polynomial_monomial, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1)]
  simp only [norm_mul, Real.norm_eq_abs, Nat.abs_cast]

theorem no_bounded_coordinate_multiplication (L : H →L[ℝ] H) :
    ¬ ∀ P : Polynomial ℝ, L (polynomial P) = polynomial (X*P) := by
  intro hL
  obtain ⟨n, hn⟩ := exists_nat_gt ‖L‖
  let c : ℝ := 1/(n.factorial : ℝ)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hnorm : ‖polynomial (monomial n c)‖ = 1 := by
    rw [monomial_norm, abs_of_nonneg hc]
    dsimp [c]
    field_simp
  have hxnorm : ‖polynomial (X*monomial n c)‖ = (n:ℝ)+1 := by
    rw [X_mul_monomial, monomial_norm, abs_of_nonneg hc, Nat.factorial_succ]
    dsimp [c]
    push_cast
    field_simp
  have hb := L.le_opNorm (polynomial (monomial n c))
  rw [hL, hxnorm, hnorm, mul_one] at hb
  linarith

end OperatorDerivativeRewrite.Foundation.FactorialAnalyticDomain
