import Foundation.L1BoundedSynthesis
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Finsupp.Order
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! A complete multivariate factorial domain with dimension-independent genuine derivatives. -/
noncomputable section
open Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.MultivariateFactorialDomain
variable {ι : Type*} [DecidableEq ι]

abbrev H (ι : Type*) := lp (fun _ : ι →₀ ℕ => ℝ) 1

def polynomial (P : MvPolynomial ι ℝ) : H ι :=
  ⟨fun d => (d.degree.factorial : ℝ) * P.coeff d, by
    apply memℓp_gen
    apply summable_of_ne_finset_zero (s := P.support)
    intro d hd
    have hz : P.coeff d = 0 := by simpa only [MvPolynomial.mem_support_iff, not_not] using hd
    simp [hz]⟩

omit [DecidableEq ι] in
theorem polynomial_apply (P : MvPolynomial ι ℝ) (d : ι →₀ ℕ) :
    polynomial P d = (d.degree.factorial : ℝ) * P.coeff d := rfl

def polynomialMap : MvPolynomial ι ℝ →ₗ[ℝ] H ι where
  toFun := polynomial
  map_add' P Q := by
    ext d
    simp only [polynomial_apply, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      lp.coeFn_add, Pi.add_apply]
    ring
  map_smul' c P := by
    ext d
    simp only [polynomial_apply, MvPolynomial.coeff_smul, smul_eq_mul,
      lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
    ring

omit [DecidableEq ι] in
theorem polynomial_injective : Function.Injective (polynomial (ι := ι)) := by
  intro P Q he
  ext d
  have h := congrArg (fun u : H ι => u d) he
  exact mul_left_cancel₀ (by positivity : (d.degree.factorial : ℝ) ≠ 0) h

theorem polynomial_monomial (d : ι →₀ ℕ) (c : ℝ) :
    polynomial (MvPolynomial.monomial d c) = lp.single 1 d ((d.degree.factorial : ℝ)*c) := by
  ext e
  by_cases he : e=d
  · subst e
    simp [polynomial_apply]
  · simp [polynomial_apply, MvPolynomial.coeff_monomial, lp.single_apply, he, Ne.symm he]

omit [DecidableEq ι] in
theorem polynomial_dense : DenseRange (polynomial (ι := ι)) := by
  classical
  intro u
  have hs := lp.hasSum_single (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) u
  apply isClosed_closure.mem_of_tendsto hs
  apply Filter.Eventually.of_forall
  intro s
  apply subset_closure
  refine ⟨∑ d ∈ s, MvPolynomial.monomial d (u d/(d.degree.factorial : ℝ)), ?_⟩
  change polynomialMap (∑ d ∈ s, MvPolynomial.monomial d (u d/(d.degree.factorial : ℝ))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  change polynomial (MvPolynomial.monomial d (u d/(d.degree.factorial : ℝ))) = _
  rw [polynomial_monomial]
  congr 1
  field_simp

def atom (v : ι → ℝ) (d : ι →₀ ℕ) : H ι :=
  ∑ i ∈ d.support, (((d i : ℝ)/(d.degree : ℝ))*v i) •
    lp.single 1 (d - Finsupp.single i 1) (1 : ℝ)

theorem atom_norm (v : ι → ℝ) (hv : ∀ i, |v i| ≤ 1) (d : ι →₀ ℕ) : ‖atom v d‖ ≤ 1 := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i ∈ d.support, (d i : ℝ)/(d.degree : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, lp.norm_single (by norm_num : (0 : ℝ≥0∞)<1), norm_one, mul_one,
        Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (d i : ℝ)/(d.degree : ℝ))]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hv i)
        (by positivity : 0 ≤ (d i : ℝ)/(d.degree : ℝ))
    _ ≤ 1 := by
      rw [← Finset.sum_div, ← Nat.cast_sum, ← Finsupp.degree_apply]
      by_cases hd : d.degree=0
      · simp [hd]
      · exact le_of_eq (div_self (by exact_mod_cast hd : (d.degree : ℝ) ≠ 0))

def derivative (v : ι → ℝ) (hv : ∀ i, |v i| ≤ 1) : H ι →L[ℝ] H ι :=
  L1BoundedSynthesis.synthesis (atom v) (atom_norm v hv)

theorem derivative_norm (v : ι → ℝ) (hv : ∀ i, |v i| ≤ 1) : ‖derivative v hv‖ ≤ 1 :=
  L1BoundedSynthesis.synthesis_norm (atom v) (atom_norm v hv)

def polynomialDerivative (v : ι → ℝ) : Derivation ℝ (MvPolynomial ι ℝ) (MvPolynomial ι ℝ) :=
  MvPolynomial.mkDerivation ℝ (fun i => MvPolynomial.C (v i))

omit [DecidableEq ι] in
theorem polynomialDerivative_monomial (v : ι → ℝ) (d : ι →₀ ℕ) (c : ℝ) :
    polynomialDerivative v (MvPolynomial.monomial d c) =
      ∑ i ∈ d.support, MvPolynomial.monomial (d - Finsupp.single i 1) (c*(d i : ℝ)*v i) := by
  rw [polynomialDerivative, MvPolynomial.mkDerivation_monomial, Finsupp.sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change c • (MvPolynomial.monomial (d - Finsupp.single i 1) (d i : ℝ) *
    MvPolynomial.C (v i)) = _
  rw [mul_comm _ (MvPolynomial.C (v i)), MvPolynomial.C_mul_monomial,
    MvPolynomial.smul_monomial]
  congr 1
  simp only [smul_eq_mul]
  ring

omit [DecidableEq ι] in
theorem lower_degree (d : ι →₀ ℕ) (i : ι) (hi : i ∈ d.support) :
    (d - Finsupp.single i 1).degree + 1 = d.degree := by
  have he := congrArg Finsupp.degree
    (Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp hi))
  simpa only [map_add, Finsupp.degree_single] using he

omit [DecidableEq ι] in
theorem factorial_lower (d : ι →₀ ℕ) (i : ι) (hi : i ∈ d.support) :
    (d.degree.factorial : ℝ)/(d.degree : ℝ) = ((d - Finsupp.single i 1).degree.factorial : ℝ) := by
  rw [← lower_degree d i hi, Nat.factorial_succ]
  push_cast
  field_simp

theorem derivative_monomial (v : ι → ℝ) (hv : ∀ i, |v i| ≤ 1)
    (d : ι →₀ ℕ) (c : ℝ) :
    derivative v hv (polynomial (MvPolynomial.monomial d c)) =
      polynomial (polynomialDerivative v (MvPolynomial.monomial d c)) := by
  rw [polynomial_monomial]
  change L1BoundedSynthesis.synthesis (atom v) (atom_norm v hv)
    (lp.single 1 d ((d.degree.factorial : ℝ)*c)) = _
  rw [L1BoundedSynthesis.synthesis_single, atom, Finset.smul_sum, polynomialDerivative_monomial]
  change _ = polynomialMap (∑ i ∈ d.support,
    MvPolynomial.monomial (d - Finsupp.single i 1) (c*(d i : ℝ)*v i))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change ((d.degree.factorial : ℝ)*c) •
    ((((d i : ℝ)/(d.degree : ℝ))*v i) • lp.single 1 (d - Finsupp.single i 1) (1 : ℝ)) =
    polynomial (MvPolynomial.monomial (d - Finsupp.single i 1) (c*(d i : ℝ)*v i))
  rw [polynomial_monomial, smul_smul]
  have he : ((d.degree.factorial : ℝ)*c)*(((d i : ℝ)/(d.degree : ℝ))*v i) =
      ((d - Finsupp.single i 1).degree.factorial : ℝ)*(c*(d i : ℝ)*v i) := by
    calc
      _ = (c*(d i : ℝ)*v i)*((d.degree.factorial : ℝ)/(d.degree : ℝ)) := by ring
      _ = _ := by rw [factorial_lower d i hi]; ring
  rw [he, ← lp.single_smul]
  simp only [smul_eq_mul, mul_one]

theorem derivative_polynomial (v : ι → ℝ) (hv : ∀ i, |v i| ≤ 1) (P : MvPolynomial ι ℝ) :
    derivative v hv (polynomial P) = polynomial (polynomialDerivative v P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c => exact derivative_monomial v hv d c
  | add P Q hP hQ =>
    change derivative v hv (polynomialMap (P + Q)) = polynomialMap (polynomialDerivative v (P + Q))
    rw [map_add, map_add, map_add, map_add]
    exact congrArg₂ (·+·) hP hQ

theorem derivative_unique (v : ι → ℝ) (hv : ∀ i, |v i| ≤ 1) (L : H ι →L[ℝ] H ι)
    (hL : ∀ P, L (polynomial P) = polynomial (polynomialDerivative v P)) : L = derivative v hv := by
  apply ContinuousLinearMap.coeFn_injective
  apply polynomial_dense.equalizer L.continuous (derivative v hv).continuous
  funext P
  exact (hL P).trans (derivative_polynomial v hv P).symm

omit [DecidableEq ι] in
theorem polynomial_norm (P : MvPolynomial ι ℝ) :
    ‖polynomial P‖ = ∑ d ∈ P.support, (d.degree.factorial : ℝ)*|P.coeff d| := by
  have he : ‖polynomial P‖ = ∑' d : ι →₀ ℕ, ‖polynomial P d‖ := by
    simpa using lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal) (polynomial P)
  rw [he, tsum_eq_sum (s := P.support)]
  · apply Finset.sum_congr rfl
    intro d hd
    simp only [polynomial_apply, norm_mul, Real.norm_eq_abs, Nat.abs_cast]
  · intro d hd
    have hz : P.coeff d = 0 := by simpa only [MvPolynomial.mem_support_iff, not_not] using hd
    simp [polynomial_apply, hz]

theorem derivative_iterate_core (v : ι → ℝ) (hv : ∀ i, |v i| ≤ 1)
    (r : ℕ) (P : MvPolynomial ι ℝ) :
    ((derivative v hv)^r) (polynomial P) =
      polynomial ((polynomialDerivative v : MvPolynomial ι ℝ → MvPolynomial ι ℝ)^[r] P) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [pow_succ']
    change derivative v hv (((derivative v hv)^r) (polynomial P)) = _
    rw [ih, derivative_polynomial, Function.iterate_succ_apply']

theorem derivative_iterate_bound (v : ι → ℝ) (hv : ∀ i, |v i| ≤ 1) (r : ℕ) (u : H ι) :
    ‖((derivative v hv)^r) u‖ ≤ ‖u‖ := by
  induction r with
  | zero => exact le_rfl
  | succ r ih =>
    rw [pow_succ']
    change ‖derivative v hv (((derivative v hv)^r) u)‖ ≤ _
    have he := (derivative v hv).le_of_opNorm_le (derivative_norm v hv) (((derivative v hv)^r) u)
    have hb : ‖derivative v hv (((derivative v hv)^r) u)‖ ≤ ‖((derivative v hv)^r) u‖ := by
      simpa only [one_mul] using he
    exact hb.trans ih

theorem derivative_power_norm (v : ι → ℝ) (hv : ∀ i, |v i| ≤ 1) (r : ℕ) :
    ‖((derivative v hv)^r)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using derivative_iterate_bound v hv r u

omit [DecidableEq ι] in
theorem polynomial_hasDerivAt (v x : ι → ℝ) (P : MvPolynomial ι ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => MvPolynomial.eval (fun i => x i + s * v i) P)
      (MvPolynomial.eval (fun i => x i + t * v i) (polynomialDerivative v P)) t := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    simpa [polynomialDerivative] using hasDerivAt_const t c
  | add P Q hP hQ =>
    simpa only [map_add, MvPolynomial.eval_add, Pi.add_apply] using hP.fun_add hQ
  | mul_X P i hP =>
    have hx : HasDerivAt (fun s : ℝ => x i + s * v i) (v i) t := by
      simpa only [Pi.add_apply, zero_add, one_mul, id_eq] using
        (hasDerivAt_const t (x i)).fun_add ((hasDerivAt_id t).mul_const (v i))
    convert hP.mul hx using 1
    · funext s
      simp
    · have he : polynomialDerivative v (P * MvPolynomial.X i) =
          P * MvPolynomial.C (v i) + MvPolynomial.X i*polynomialDerivative v P := by
        rw [Derivation.leibniz]
        simp only [polynomialDerivative, MvPolynomial.mkDerivation_X, smul_eq_mul]
      change MvPolynomial.eval (fun j => x j + t * v j)
        (polynomialDerivative v (P * MvPolynomial.X i)) = _
      rw [he, map_add, map_mul, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C]
      ring

end OperatorDerivativeRewrite.Foundation.MultivariateFactorialDomain
