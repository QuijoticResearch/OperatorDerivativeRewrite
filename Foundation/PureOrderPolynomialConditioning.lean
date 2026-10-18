import Foundation.HigherHeatMultivariateMoments

/-! Finite signed polynomial causal projections; no completed path-space assertion. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.PureOrderPolynomialConditioning
open PseudoPolynomialStein HigherHeatMultivariateMoments HigherHeatPolynomialRealization
variable {ι : Type*} [Fintype ι]

open Classical in
def keep (S : Finset ι) (d : ι →₀ ℕ) : ι →₀ ℕ := d.filter (fun i => i ∈ S)

open Classical in
def factor (p : ℕ) (a : ι → ℝ) (S : Finset ι) (d : ι →₀ ℕ) : ℝ :=
  ∏ i, if i ∈ S then 1 else moment p (a i) (d i)

def conditioning (p : ℕ) (a : ι → ℝ) (S : Finset ι) :
    MvPolynomial ι ℝ →ₗ[ℝ] MvPolynomial ι ℝ :=
  (MvPolynomial.basisMonomials ι ℝ).constr ℝ
    (fun d => MvPolynomial.monomial (keep S d) (factor p a S d))

theorem conditioning_monomial (p : ℕ) (a : ι → ℝ) (S : Finset ι)
    (d : ι →₀ ℕ) (c : ℝ) :
    conditioning p a S (MvPolynomial.monomial d c) =
      MvPolynomial.monomial (keep S d) (c * factor p a S d) := by
  have he : MvPolynomial.monomial d c = c • MvPolynomial.monomial d 1 := by
    rw [MvPolynomial.smul_monomial]
    simp
  rw [he, map_smul]
  have hb : MvPolynomial.monomial d (1:ℝ) = (MvPolynomial.basisMonomials ι ℝ) d := rfl
  rw [hb]
  change c • ((MvPolynomial.basisMonomials ι ℝ).constr ℝ _) _ = _
  rw [Module.Basis.constr_basis]
  simp only [MvPolynomial.smul_monomial, smul_eq_mul]

omit [Fintype ι] in
open Classical in
theorem keep_apply (S : Finset ι) (d : ι →₀ ℕ) (i : ι) :
    keep S d i = if i ∈ S then d i else 0 := by
  classical
  rfl

omit [Fintype ι] in
open Classical in
theorem keep_keep (S T : Finset ι) (d : ι →₀ ℕ) :
    keep S (keep T d) = keep (S ∩ T) d := by
  classical
  ext i
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [keep_apply, hS, hT]

open Classical in
theorem factor_tower (p : ℕ) (a : ι → ℝ) (S T : Finset ι) (d : ι →₀ ℕ) :
    factor p a T d * factor p a S (keep T d) = factor p a (S ∩ T) d := by
  classical
  rw [factor, factor, factor, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    simp [keep_apply, hS, hT, moment_zero]

open Classical in
theorem conditioning_tower (p : ℕ) (a : ι → ℝ) (S T : Finset ι)
    (P : MvPolynomial ι ℝ) :
    conditioning p a S (conditioning p a T P) = conditioning p a (S ∩ T) P := by
  classical
  have he : (conditioning p a S).comp (conditioning p a T) = conditioning p a (S ∩ T) := by
    apply (MvPolynomial.basisMonomials ι ℝ).ext
    intro d
    change conditioning p a S (conditioning p a T (MvPolynomial.monomial d 1)) =
      conditioning p a (S ∩ T) (MvPolynomial.monomial d 1)
    rw [conditioning_monomial, conditioning_monomial, one_mul, keep_keep,
      conditioning_monomial, one_mul, factor_tower]
  exact LinearMap.congr_fun he P

theorem conditioning_idempotent (p : ℕ) (a : ι → ℝ) (S : Finset ι)
    (P : MvPolynomial ι ℝ) :
    conditioning p a S (conditioning p a S P) = conditioning p a S P := by
  simpa using conditioning_tower p a S S P

theorem conditioning_commute (p : ℕ) (a : ι → ℝ) (S T : Finset ι)
    (P : MvPolynomial ι ℝ) :
    conditioning p a S (conditioning p a T P) = conditioning p a T (conditioning p a S P) := by
  classical
  rw [conditioning_tower, conditioning_tower, Finset.inter_comm]


def dependsOn (S : Finset ι) (P : MvPolynomial ι ℝ) : Prop :=
  ∀ x y : ι → ℝ, (∀ i ∈ S, x i = y i) → value P x = value P y

theorem kept_monomial_depends (S : Finset ι) (d : ι →₀ ℕ) (c : ℝ) :
    dependsOn S (MvPolynomial.monomial (keep S d) c) := by
  classical
  intro x y hxy
  rw [value_monomial, value_monomial]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S
  · rw [keep_apply, ite_eq_left hi, hxy i hi]
  · simp [keep_apply, hi]

theorem conditioning_dependsOn (p : ℕ) (a : ι → ℝ) (S : Finset ι)
    (P : MvPolynomial ι ℝ) : dependsOn S (conditioning p a S P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [conditioning_monomial]
    exact kept_monomial_depends S d _
  | add P Q hP hQ =>
    intro x y hxy
    rw [map_add, value_add, value_add, hP x y hxy, hQ x y hxy]

omit [Fintype ι] in
theorem keep_eq_self (S : Finset ι) (d : ι →₀ ℕ) (h : ∀ i, i ∉ S → d i = 0) :
    keep S d = d := by
  classical
  ext i
  by_cases hi : i ∈ S
  · simp [keep_apply, hi]
  · simp [keep_apply, hi, h i hi]

theorem factor_of_supported (p : ℕ) (a : ι → ℝ) (S : Finset ι) (d : ι →₀ ℕ)
    (h : ∀ i, i ∉ S → d i = 0) : factor p a S d = 1 := by
  classical
  apply Finset.prod_eq_one
  intro i _
  by_cases hi : i ∈ S
  · simp [hi]
  · simp [hi, h i hi, moment_zero]

theorem conditioning_supported_monomial (p : ℕ) (a : ι → ℝ) (S : Finset ι)
    (d : ι →₀ ℕ) (c : ℝ) (h : ∀ i, i ∉ S → d i = 0) :
    conditioning p a S (MvPolynomial.monomial d c) = MvPolynomial.monomial d c := by
  rw [conditioning_monomial, keep_eq_self S d h, factor_of_supported p a S d h, mul_one]



theorem factor_mean (p : ℕ) (a : ι → ℝ) (S : Finset ι) (d : ι →₀ ℕ) :
    factor p a S d * (∏ i, moment p (a i) (keep S d i)) =
      ∏ i, moment p (a i) (d i) := by
  classical
  rw [factor, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> simp [hi, keep_apply, moment_zero]

def parameters (m : ℕ) (t : ι → ℝ≥0) (i : ι) : ℝ := (-1)^(m+1)*(t i : ℝ)

theorem actual_mean_monomial (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (d : ι →₀ ℕ) (c : ℝ) :
    mean m hm t ht (MvPolynomial.monomial d c) =
      ((c * ∏ i, moment (2*m) (parameters m t i) (d i) : ℝ) : ℂ) := by
  rw [mean_monomial]
  simp_rw [kernelExpectation_eq_moments, expectation_X_pow]
  simp only [parameters, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_prod]

theorem actual_mean_conditioning (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (S : Finset ι) (P : MvPolynomial ι ℝ) :
    mean m hm t ht (conditioning (2*m) (parameters m t) S P) = mean m hm t ht P := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [conditioning_monomial, actual_mean_monomial, actual_mean_monomial,
      mul_assoc, factor_mean]
  | add P Q hP hQ =>
    rw [map_add, map_add, map_add, hP, hQ]

omit [Fintype ι] in
theorem keep_add_supported (S : Finset ι) (d e : ι →₀ ℕ)
    (he : ∀ i, i ∉ S → e i = 0) : keep S (d+e) = keep S d + e := by
  classical
  ext i
  by_cases hi : i ∈ S
  · simp [keep_apply, hi]
  · simp [keep_apply, hi, he i hi]

theorem factor_add_supported (p : ℕ) (a : ι → ℝ) (S : Finset ι) (d e : ι →₀ ℕ)
    (he : ∀ i, i ∉ S → e i = 0) : factor p a S (d+e) = factor p a S d := by
  classical
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S
  · simp [hi]
  · simp [hi, he i hi]

theorem conditioning_mul_supported_monomial (p : ℕ) (a : ι → ℝ) (S : Finset ι)
    (P : MvPolynomial ι ℝ) (e : ι →₀ ℕ) (b : ℝ) (he : ∀ i, i ∉ S → e i = 0) :
    conditioning p a S (P * MvPolynomial.monomial e b) =
      conditioning p a S P * MvPolynomial.monomial e b := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [MvPolynomial.monomial_mul_monomial, conditioning_monomial,
      conditioning_monomial, MvPolynomial.monomial_mul_monomial,
      keep_add_supported S d e he, factor_add_supported p a S d e he]
    congr 1
    ring
  | add P Q hP hQ =>
    rw [add_mul, map_add, hP, hQ, map_add, add_mul]

theorem actual_past_monomial_pairing (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (S : Finset ι) (P : MvPolynomial ι ℝ)
    (e : ι →₀ ℕ) (b : ℝ) (he : ∀ i, i ∉ S → e i = 0) :
    mean m hm t ht (conditioning (2*m) (parameters m t) S P * MvPolynomial.monomial e b) =
      mean m hm t ht (P * MvPolynomial.monomial e b) := by
  rw [← conditioning_mul_supported_monomial _ _ _ P e b he, actual_mean_conditioning]



def supported (S : Finset ι) (P : MvPolynomial ι ℝ) : Prop :=
  ∀ d ∈ P.support, ∀ i, i ∉ S → d i = 0

theorem conditioning_fixed_of_supported (p : ℕ) (a : ι → ℝ) (S : Finset ι)
    (P : MvPolynomial ι ℝ) (hP : supported S P) : conditioning p a S P = P := by
  classical
  calc
    _ = conditioning p a S (∑ d ∈ P.support, MvPolynomial.monomial d (P.coeff d)) :=
      congrArg (conditioning p a S) (MvPolynomial.as_sum P)
    _ = ∑ d ∈ P.support, MvPolynomial.monomial d (P.coeff d) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro d hd
      exact conditioning_supported_monomial p a S d _ (hP d hd)
    _ = P := (MvPolynomial.as_sum P).symm

theorem conditioning_mul_supported (p : ℕ) (a : ι → ℝ) (S : Finset ι)
    (P Q : MvPolynomial ι ℝ) (hQ : supported S Q) :
    conditioning p a S (P*Q) = conditioning p a S P * Q := by
  classical
  calc
    _ = conditioning p a S (P * ∑ d ∈ Q.support, MvPolynomial.monomial d (Q.coeff d)) :=
      congrArg (fun R => conditioning p a S (P*R)) (MvPolynomial.as_sum Q)
    _ = ∑ d ∈ Q.support, conditioning p a S (P * MvPolynomial.monomial d (Q.coeff d)) := by
      rw [Finset.mul_sum, map_sum]
    _ = ∑ d ∈ Q.support, conditioning p a S P * MvPolynomial.monomial d (Q.coeff d) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact conditioning_mul_supported_monomial p a S P d _ (hQ d hd)
    _ = conditioning p a S P * Q := by
      rw [← Finset.mul_sum, ← MvPolynomial.as_sum Q]

theorem actual_past_polynomial_pairing (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (S : Finset ι) (P Q : MvPolynomial ι ℝ) (hQ : supported S Q) :
    (∫ᵛ x, value (conditioning (2*m) (parameters m t) S P) x * value Q x
      ∂<•HigherHeatSignedLaws.incrementLaw m hm t ht) =
    (∫ᵛ x, value P x * value Q x ∂<•HigherHeatSignedLaws.incrementLaw m hm t ht) := by
  have he := actual_mean_conditioning m hm t ht S (P*Q)
  rw [conditioning_mul_supported _ _ _ P Q hQ] at he
  change (∫ᵛ x, value (conditioning (2*m) (parameters m t) S P * Q) x
      ∂<•HigherHeatSignedLaws.incrementLaw m hm t ht) =
    (∫ᵛ x, value (P*Q) x ∂<•HigherHeatSignedLaws.incrementLaw m hm t ht) at he
  simpa only [value_mul] using he



omit [Fintype ι] in
theorem keep_empty (d : ι →₀ ℕ) : keep ∅ d = 0 := by
  classical
  ext i
  simp [keep_apply]

theorem factor_empty (p : ℕ) (a : ι → ℝ) (d : ι →₀ ℕ) :
    factor p a ∅ d = ∏ i, moment p (a i) (d i) := by
  classical
  simp [factor]

theorem conditioning_univ (p : ℕ) (a : ι → ℝ) (P : MvPolynomial ι ℝ) :
    conditioning p a Finset.univ P = P := by
  apply conditioning_fixed_of_supported
  intro d _ i hi
  exact False.elim (hi (Finset.mem_univ i))

theorem actual_value_empty (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (P : MvPolynomial ι ℝ) (x : ι → ℝ) :
    value (conditioning (2*m) (parameters m t) ∅ P) x = mean m hm t ht P := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [conditioning_monomial, keep_empty, factor_empty, actual_mean_monomial]
    simp [value]
  | add P Q hP hQ =>
    rw [map_add, value_add, map_add, hP, hQ]


end OperatorDerivativeRewrite.Foundation.PureOrderPolynomialConditioning
