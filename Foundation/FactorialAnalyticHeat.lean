import Foundation.FactorialAnalyticDomain
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! A complete analytic heat evolution identified with actual signed polynomial transport. -/
noncomputable section
open Polynomial MeasureTheory Filter
open scoped Topology ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.FactorialAnalyticHeat
open FactorialAnalyticDomain PseudoPolynomialStein

def evolution (p : ℕ) (a : ℝ) : H →L[ℝ] H := NormedSpace.exp (a • shift^p)

def mean (p : ℕ) (a : ℝ) : H →L[ℝ] ℝ :=
  (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 1 0).comp (evolution p a)

theorem scaled_pow (a : ℝ) (A : H →L[ℝ] H) (k : ℕ) :
    (a • A)^k = a^k • A^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    apply ContinuousLinearMap.ext
    intro u
    change a^k • ((A^k) (a • A u)) = (a^k*a) • ((A^k) (A u))
    rw [map_smul, smul_smul]

theorem series_coordinate (p : ℕ) (a : ℝ) (u : H) (n : ℕ) :
    HasSum (fun k : ℕ => (a^k/(k.factorial : ℝ)) * u (n + p * k)) (evolution p a u n) := by
  let L : (H →L[ℝ] H) →L[ℝ] ℝ :=
    (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 1 n).comp (ContinuousLinearMap.apply ℝ H u)
  have hs := L.hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (a • shift^p))
  convert hs using 1
  · funext k
    change (a^k/(k.factorial : ℝ)) * u (n + p * k) =
    (((k.factorial : ℝ)⁻¹) • ((a • shift^p)^k)) u n
    rw [scaled_pow, ← pow_mul]
    change (a^k/(k.factorial : ℝ)) * u (n + p * k) =
      (k.factorial : ℝ)⁻¹ * (a^k * ((shift^(p * k)) u n))
    rw [shift_pow_apply]
    ring
  · rfl

theorem mean_X_multiple (p : ℕ) (hp : 0 < p) (a : ℝ) (k : ℕ) :
    mean p a (polynomial (X^(p * k))) = moment p a (p * k) := by
  have hs := series_coordinate p a (polynomial (X^(p * k))) 0
  have he (j : ℕ) : (a^j/(j.factorial : ℝ)) * polynomial (X^(p * k)) (0+p*j) =
      if j=k then ((p * k).factorial : ℝ)*a^k/(k.factorial : ℝ) else 0 := by
    simp only [polynomial_apply, coeff_X_pow, zero_add]
    by_cases hj : j=k
    · subst j
      simp only [ite_true, mul_one]
      ring
    · have hne : p * k ≠ p*j := fun h => hj (Nat.eq_of_mul_eq_mul_left hp h.symm)
      simp only [hj, Ne.symm hne, ite_false, mul_zero]
  have hsum : HasSum (fun j : ℕ => if j=k then ((p * k).factorial : ℝ)*a^k/(k.factorial : ℝ)
      else 0) (((p * k).factorial : ℝ)*a^k/(k.factorial : ℝ)) := by
    exact hasSum_ite_eq k _
  have hh := hs.congr_fun (fun j => (he j).symm)
  rw [moment_multiple p hp a k]
  exact hh.unique hsum

theorem mean_X_off_order (p : ℕ) (hp : 0 < p) (a : ℝ) (d : ℕ) (hd : ¬p ∣ d) :
    mean p a (polynomial (X^d)) = moment p a d := by
  have hs := series_coordinate p a (polynomial (X^d)) 0
  have he (j : ℕ) : (a^j/(j.factorial : ℝ)) * polynomial (X^d) (0+p*j) = 0 := by
    have hn : d ≠ p*j := fun h => hd ⟨j, h⟩
    simp only [polynomial_apply, coeff_X_pow, zero_add, Ne.symm hn, ite_false, mul_zero]
  have hh := hs.congr_fun (fun j => (he j).symm)
  rw [moment_off_order p hp a d hd]
  exact hh.unique hasSum_zero

theorem mean_polynomial (p : ℕ) (hp : 0 < p) (a : ℝ) (P : Polynomial ℝ) :
    mean p a (polynomial P) = expectation p a P := by
  have hx (n : ℕ) : mean p a (polynomial (X^n)) = expectation p a (X^n) := by
    rw [expectation_X_pow]
    by_cases hn : p ∣ n
    · obtain ⟨k, rfl⟩ := hn
      exact mean_X_multiple p hp a k
    · exact mean_X_off_order p hp a n hn
  have he : (mean p a).toLinearMap.comp polynomialMap = expectation p a := by
    apply Polynomial.lhom_ext'
    intro n
    apply LinearMap.ext
    intro c
    have hm : monomial n c = c • (X : Polynomial ℝ)^n := by
      simp [smul_eq_C_mul, C_mul_X_pow_eq_monomial]
    change mean p a (polynomialMap (monomial n c)) = expectation p a (monomial n c)
    rw [hm, map_smul, map_smul, map_smul]
    exact congrArg (fun z : ℝ => c • z) (hx n)
  exact LinearMap.congr_fun he P

theorem polynomial_coordinate_derivative (P : Polynomial ℝ) (n : ℕ) :
    polynomial P n = (derivative^[n] P).eval 0 := by
  simp only [polynomial_apply, ← coeff_zero_eq_eval_zero, coeff_iterate_derivative, zero_add,
    Nat.descFactorial_self, nsmul_eq_mul]

theorem shift_evolution (p n : ℕ) (a : ℝ) (u : H) :
    (shift^n) (evolution p a u) = evolution p a ((shift^n) u) := by
  have hc : Commute (shift^n) (a • shift^p) := by
    apply ContinuousLinearMap.ext
    intro v
    change (shift^n) (a • ((shift^p) v)) = a • ((shift^p) ((shift^n) v))
    rw [map_smul]
    exact congrArg (fun w : H => a • w)
      (congrArg (fun A : H →L[ℝ] H => A v)
        (((Commute.refl shift).pow_left n).pow_right p).eq)
  have he := congrArg (fun A : H →L[ℝ] H => A u) hc.exp_right.eq
  exact he

theorem evolution_polynomial (p : ℕ) (hp : 1 < p) (a : ℝ) (P : Polynomial ℝ) :
    evolution p a (polynomial P) = polynomial (PureOrderPolynomialTransport.transport p a P) := by
  ext n
  have he : polynomial (PureOrderPolynomialTransport.transport p a P) n =
      expectation p a (derivative^[n] P) := by
    rw [polynomial_coordinate_derivative, PureOrderPolynomialTransport.transport_iterate_derivative,
      PureOrderPolynomialTransport.transport_eval p hp, taylor_zero]
  rw [he]
  calc
    evolution p a (polynomial P) n = (shift^n) (evolution p a (polynomial P)) 0 := by
      rw [shift_pow_apply, zero_add]
    _ = evolution p a ((shift^n) (polynomial P)) 0 :=
      congrArg (fun u : H => u 0) (shift_evolution p n a (polynomial P))
    _ = mean p a (polynomial (derivative^[n] P)) := by
      rw [polynomial_iterate_derivative]
      rfl
    _ = expectation p a (derivative^[n] P) := mean_polynomial p (by omega) a _

theorem evolution_norm (p : ℕ) (a : ℝ) : ‖evolution p a‖ ≤ Real.exp |a| := by
  have hr : HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹) * |a|^k) (Real.exp |a|) := by
    simpa only [smul_eq_mul, Real.exp_eq_exp_ℝ] using
      NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) |a|
  apply (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (a • shift^p)).norm_le_of_bounded hr
  intro k
  rw [scaled_pow, ← pow_mul, norm_smul, norm_smul, norm_inv, Real.norm_natCast,
    Real.norm_eq_abs, abs_pow]
  have hs : ‖shift^(p * k)‖ ≤ 1 := (norm_pow_le shift (p * k)).trans
    (pow_le_one₀ (norm_nonneg shift) shift_norm_le)
  calc
    _ ≤ (k.factorial : ℝ)⁻¹ * (|a|^k * 1) := by gcongr
    _ = _ := by ring

theorem mean_norm (p : ℕ) (a : ℝ) : ‖mean p a‖ ≤ Real.exp |a| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro u
  have he : |mean p a u| ≤ ‖evolution p a u‖ :=
    lp.norm_apply_le_norm (p := 1) (by norm_num : (1 : ℝ≥0∞) ≠ 0) (evolution p a u) 0
  exact he.trans ((evolution p a).le_of_opNorm_le (evolution_norm p a) u)

theorem evolution_zero (p : ℕ) : evolution p 0 = ContinuousLinearMap.id ℝ H := by
  exact (congrArg NormedSpace.exp (zero_smul ℝ (shift^p))).trans NormedSpace.exp_zero

theorem evolution_add (p : ℕ) (hp : 1 < p) (a b : ℝ) :
    (evolution p a).comp (evolution p b) = evolution p (a + b) := by
  apply ContinuousLinearMap.coeFn_injective
  apply polynomial_dense.equalizer
    (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  funext P
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, evolution_polynomial p hp]
  exact congrArg polynomial
    (LinearMap.congr_fun (PureOrderPolynomialTransport.transport_add p hp a b) P)

theorem evolution_unique (p : ℕ) (hp : 1 < p) (a : ℝ) (L : H →L[ℝ] H)
    (hL : ∀ P, L (polynomial P) = polynomial (PureOrderPolynomialTransport.transport p a P)) :
    L = evolution p a := by
  apply ContinuousLinearMap.coeFn_injective
  apply polynomial_dense.equalizer L.continuous (evolution p a).continuous
  funext P
  exact (hL P).trans (evolution_polynomial p hp a P).symm

theorem mean_unique (p : ℕ) (hp : 0 < p) (a : ℝ) (L : H →L[ℝ] ℝ)
    (hL : ∀ P, L (polynomial P) = expectation p a P) : L = mean p a := by
  apply ContinuousLinearMap.coeFn_injective
  apply polynomial_dense.equalizer L.continuous (mean p a).continuous
  funext P
  exact (hL P).trans (mean_polynomial p hp a P).symm

theorem actual_mean (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (P : Polynomial ℝ) :
    mean (2 * m) ((-1 : ℝ)^(m + 1)*(t : ℝ)) (polynomial P) =
      HigherHeatPolynomialRealization.kernelExpectation m hm t ht P := by
  rw [mean_polynomial (2 * m) (by omega),
    HigherHeatPolynomialRealization.kernelExpectation_eq_moments]

theorem evolution_hasDerivAt (p : ℕ) (a : ℝ) (u : H) :
    HasDerivAt (fun t : ℝ => evolution p t u) (evolution p a ((shift^p) u)) a := by
  have hd := (ContinuousLinearMap.apply ℝ H u).hasFDerivAt.comp_hasDerivAt a
    (hasDerivAt_exp_smul_const (shift^p) a)
  exact hd

theorem mean_hasDerivAt (p : ℕ) (a : ℝ) (u : H) :
    HasDerivAt (fun t : ℝ => mean p t u) (mean p a ((shift^p) u)) a := by
  exact (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 1 0).hasFDerivAt.comp_hasDerivAt a
    (evolution_hasDerivAt p a u)

theorem evolution_continuous (p : ℕ) : Continuous (evolution p) := by
  let : NormedAlgebra ℚ (H →L[ℝ] H) := NormedAlgebra.restrictScalars ℚ ℝ _
  exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

end OperatorDerivativeRewrite.Foundation.FactorialAnalyticHeat
