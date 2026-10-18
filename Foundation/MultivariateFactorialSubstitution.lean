import Foundation.MultivariateFactorialRenaming
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Contractive weighted substitutions, including coordinate collisions and zeroing. -/
noncomputable section
open scoped ENNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.MultivariateFactorialSubstitution
open MultivariateFactorialDomain
variable {ι κ ν : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]

def weight (w : ι → ℝ) (d : ι →₀ ℕ) : ℝ := ∏ i ∈ d.support, w i ^ d i

omit [DecidableEq ι] in
theorem weight_bound (w : ι → ℝ) (hw : ∀ i, |w i| ≤ 1) (d : ι →₀ ℕ) :
    ‖weight w d‖ ≤ 1 := by
  rw [weight, norm_prod]
  apply Finset.prod_le_one₀
  · intro i hi
    exact norm_nonneg _
  · intro i hi
    rw [norm_pow, Real.norm_eq_abs]
    exact pow_le_one₀ (abs_nonneg _) (hw i)

def atom (f : ι → κ) (w : ι → ℝ) (d : ι →₀ ℕ) : H κ :=
  lp.single 1 (d.mapDomain f) (weight w d)

omit [DecidableEq ι] in
theorem atom_bound (f : ι → κ) (w : ι → ℝ) (hw : ∀ i, |w i| ≤ 1) (d : ι →₀ ℕ) :
    ‖atom f w d‖ ≤ 1 := by
  rw [atom, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1)]
  exact weight_bound w hw d

def substitute (f : ι → κ) (w : ι → ℝ) (hw : ∀ i, |w i| ≤ 1) : H ι →L[ℝ] H κ :=
  L1BoundedSynthesis.synthesis (atom f w) (atom_bound f w hw)

omit [DecidableEq ι] in
theorem substitute_bound (f : ι → κ) (w : ι → ℝ) (hw : ∀ i, |w i| ≤ 1) :
    ‖substitute f w hw‖ ≤ 1 := L1BoundedSynthesis.synthesis_norm _ _

def polynomialSubstitution (f : ι → κ) (w : ι → ℝ) :
    MvPolynomial ι ℝ →ₐ[ℝ] MvPolynomial κ ℝ :=
  MvPolynomial.aeval (fun i => MvPolynomial.C (w i) * MvPolynomial.X (f i))

omit [DecidableEq ι] [DecidableEq κ] in
theorem polynomialSubstitution_monomial (f : ι → κ) (w : ι → ℝ)
    (d : ι →₀ ℕ) (c : ℝ) :
    polynomialSubstitution f w (MvPolynomial.monomial d c) =
      MvPolynomial.monomial (d.mapDomain f) (c * weight w d) := by
  classical
  rw [polynomialSubstitution, MvPolynomial.aeval_monomial]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib]
  have he : (∏ i ∈ d.support, MvPolynomial.X (f i) ^ d i : MvPolynomial κ ℝ) =
      MvPolynomial.monomial (d.mapDomain f) 1 := by
    have h := congrArg (MvPolynomial.rename f)
      (MvPolynomial.prod_X_pow_eq_monomial (R := ℝ) (s := d))
    simpa only [map_prod, map_pow, MvPolynomial.rename_X, MvPolynomial.rename_monomial] using h
  have hc : (∏ i ∈ d.support, MvPolynomial.C (w i) ^ d i : MvPolynomial κ ℝ) =
      MvPolynomial.C (weight w d) := by simp only [weight, map_prod, map_pow]
  rw [he, hc]
  change MvPolynomial.C c * (MvPolynomial.C (weight w d) *
    MvPolynomial.monomial (d.mapDomain f) 1) = _
  rw [← mul_assoc, ← map_mul, MvPolynomial.C_mul_monomial]
  simp only [mul_one]

theorem substitute_single (f : ι → κ) (w : ι → ℝ) (hw : ∀ i, |w i| ≤ 1)
    (d : ι →₀ ℕ) (c : ℝ) :
    substitute f w hw (lp.single 1 d c) = c • atom f w d :=
  L1BoundedSynthesis.synthesis_single _ _ _ _

omit [DecidableEq ι] in
theorem substitute_polynomial (f : ι → κ) (w : ι → ℝ) (hw : ∀ i, |w i| ≤ 1)
    (P : MvPolynomial ι ℝ) :
    substitute f w hw (polynomial P) = polynomial (polynomialSubstitution f w P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [polynomial_monomial, substitute_single, polynomialSubstitution_monomial,
      polynomial_monomial, Finsupp.degree_mapDomain]
    rw [atom, ← lp.single_smul]
    simp only [smul_eq_mul]
    congr 1
    ring
  | add P Q hP hQ =>
    change substitute f w hw (polynomialMap (P+Q)) =
      polynomialMap (polynomialSubstitution f w (P+Q))
    rw [map_add, map_add, map_add, map_add]
    exact congrArg₂ (·+·) hP hQ

omit [DecidableEq ι] [DecidableEq κ] in
theorem eval_polynomialSubstitution (f : ι → κ) (w : ι → ℝ)
    (P : MvPolynomial ι ℝ) (x : κ → ℝ) :
    MvPolynomial.eval x (polynomialSubstitution f w P) =
      MvPolynomial.eval (fun i => w i * x (f i)) P := by
  have he : (MvPolynomial.aeval x).comp (polynomialSubstitution f w) =
      MvPolynomial.aeval (fun i => w i * x (f i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [polynomialSubstitution]
  exact AlgHom.congr_fun he P

omit [DecidableEq ι] [DecidableEq κ] [DecidableEq ν] in
theorem polynomialSubstitution_comp (f : ι → κ) (g : κ → ν) (w : ι → ℝ) (z : κ → ℝ) :
    (polynomialSubstitution g z).comp (polynomialSubstitution f w) =
      polynomialSubstitution (g ∘ f) (fun i => w i * z (f i)) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, polynomialSubstitution, MvPolynomial.aeval_X,
    map_mul, MvPolynomial.aeval_C, Function.comp_apply]
  rw [MvPolynomial.algebraMap_eq]
  ring

omit [DecidableEq ι] in
theorem polynomialSubstitution_id :
    polynomialSubstitution (id : ι → ι) (fun _ => 1) = AlgHom.id ℝ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [polynomialSubstitution]

omit [DecidableEq ι] in
theorem substitute_comp (f : ι → κ) (g : κ → ν) (w : ι → ℝ) (z : κ → ℝ)
    (hw : ∀ i, |w i| ≤ 1) (hz : ∀ j, |z j| ≤ 1) :
    (substitute g z hz).comp (substitute f w hw) =
      substitute (g ∘ f) (fun i => w i * z (f i))
        (fun i => by
          rw [abs_mul]
          exact (mul_le_mul_of_nonneg_right (hw i) (abs_nonneg _)).trans
            (by simpa using hz (f i))) := by
  classical
  apply ContinuousLinearMap.coeFn_injective
  apply polynomial_dense.equalizer
    (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  funext P
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, substitute_polynomial]
  exact congrArg polynomial (AlgHom.congr_fun (polynomialSubstitution_comp f g w z) P)

theorem substitute_id : substitute (id : ι → ι) (fun _ => 1) (by intro _; norm_num) =
    ContinuousLinearMap.id ℝ (H ι) := by
  apply ContinuousLinearMap.coeFn_injective
  apply polynomial_dense.equalizer
    (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  funext P
  simp only [Function.comp_apply, ContinuousLinearMap.id_apply, substitute_polynomial,
    polynomialSubstitution_id, AlgHom.id_apply]

omit [DecidableEq ι] in
theorem polynomialDerivative_C (v : ι → ℝ) (c : ℝ) :
    polynomialDerivative v (MvPolynomial.C c) = 0 := by
  rw [← MvPolynomial.algebraMap_eq]
  exact (polynomialDerivative v).map_algebraMap c

omit [DecidableEq ι] in
theorem polynomialDerivative_X (v : ι → ℝ) (i : ι) :
    polynomialDerivative v (MvPolynomial.X i) = MvPolynomial.C (v i) := by
  rw [polynomialDerivative, MvPolynomial.mkDerivation_X]

omit [DecidableEq ι] [DecidableEq κ] in
theorem polynomialDerivative_substitution (f : ι → κ) (w : ι → ℝ) (v : κ → ℝ)
    (P : MvPolynomial ι ℝ) :
    polynomialDerivative v (polynomialSubstitution f w P) =
      polynomialSubstitution f w (polynomialDerivative (fun i => w i * v (f i)) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [polynomialSubstitution, polynomialDerivative]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    have hx : polynomialDerivative v (polynomialSubstitution f w (MvPolynomial.X i)) =
        MvPolynomial.C (w i * v (f i)) := by
      rw [polynomialSubstitution, MvPolynomial.aeval_X, Derivation.leibniz,
        polynomialDerivative_C, polynomialDerivative_X]
      simp only [smul_eq_mul, mul_zero, add_zero, map_mul]
    rw [map_mul, Derivation.leibniz, Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul]
    rw [hP, hx, polynomialDerivative_X]
    simp only [polynomialSubstitution, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

theorem derivative_substitute (f : ι → κ) (w : ι → ℝ) (v : κ → ℝ)
    (hw : ∀ i, |w i| ≤ 1) (hv : ∀ j, |v j| ≤ 1) :
    (derivative v hv).comp (substitute f w hw) = (substitute f w hw).comp
      (derivative (fun i => w i * v (f i)) (fun i => by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_right (hw i) (abs_nonneg _)).trans
          (by simpa using hv (f i)))) := by
  apply ContinuousLinearMap.coeFn_injective
  apply polynomial_dense.equalizer
    (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  funext P
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, substitute_polynomial,
    derivative_polynomial, polynomialDerivative_substitution]

omit [DecidableEq ι] in
theorem substitute_unique (f : ι → κ) (w : ι → ℝ) (hw : ∀ i, |w i| ≤ 1)
    (L : H ι →L[ℝ] H κ)
    (hL : ∀ P, L (polynomial P) = polynomial (polynomialSubstitution f w P)) :
    L = substitute f w hw := by
  classical
  apply ContinuousLinearMap.coeFn_injective
  apply polynomial_dense.equalizer
    (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  funext P
  rw [Function.comp_apply, Function.comp_apply, hL, substitute_polynomial]

omit [DecidableEq ι] [DecidableEq κ] in
theorem polynomialSubstitution_one (f : ι → κ) :
    polynomialSubstitution f (fun _ => 1) = MvPolynomial.rename f := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [polynomialSubstitution]

omit [DecidableEq ι] in
theorem substitute_embedding (e : ι ↪ κ) :
    substitute e (fun _ => 1) (by intro _; norm_num) =
      MultivariateFactorialRenaming.renameOperator e := by
  classical
  apply ContinuousLinearMap.coeFn_injective
  apply polynomial_dense.equalizer
    (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  funext P
  simp only [Function.comp_apply, substitute_polynomial, polynomialSubstitution_one,
    MultivariateFactorialRenaming.renaming_polynomial]

omit [DecidableEq ι] [DecidableEq κ] in
theorem polynomialSubstitution_zero (f : ι → κ) (P : MvPolynomial ι ℝ) :
    polynomialSubstitution f (fun _ => 0) P = MvPolynomial.C (MvPolynomial.constantCoeff P) := by
  simp only [polynomialSubstitution, map_zero, zero_mul, MvPolynomial.aeval_zero',
    MvPolynomial.algebraMap_eq]

omit [DecidableEq ι] in
theorem substitute_zero_polynomial (f : ι → κ) (P : MvPolynomial ι ℝ) :
    substitute f (fun _ => 0) (by intro _; norm_num) (polynomial P) =
      polynomial (MvPolynomial.C (MvPolynomial.constantCoeff P)) := by
  classical
  rw [substitute_polynomial, polynomialSubstitution_zero]

theorem exponential_intertwining (f : ι → ι) (w v : ι → ℝ)
    (hw : ∀ i, |w i| ≤ 1) (hv : ∀ i, |v i| ≤ 1) (p : ℕ) (a : ℝ) :
    (NormedSpace.exp (a • (derivative v hv)^p)).comp (substitute f w hw) =
      (substitute f w hw).comp (NormedSpace.exp (a • (derivative
        (fun i => w i * v (f i)) (fun i => by
          rw [abs_mul]
          exact (mul_le_mul_of_nonneg_right (hw i) (abs_nonneg _)).trans
            (by simpa using hv (f i))))^p)) := by
  have h : SemiconjBy (substitute f w hw)
      (derivative (fun i => w i * v (f i)) (fun i => by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_right (hw i) (abs_nonneg _)).trans
          (by simpa using hv (f i)))) (derivative v hv) :=
    (derivative_substitute f w v hw hv).symm
  have hs : SemiconjBy (substitute f w hw)
      (a • (derivative (fun i => w i * v (f i)) (fun i => by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_right (hw i) (abs_nonneg _)).trans
          (by simpa using hv (f i))))^p) (a • (derivative v hv)^p) := by
    apply ContinuousLinearMap.ext
    intro u
    simpa only [mul_apply_eq_comp, smul_apply, map_smul] using
      congrArg (fun z : H ι => a • z) (DFunLike.congr_fun (h.pow_right p).eq u)
  let : NormedAlgebra ℚ (H ι →L[ℝ] H ι) := NormedAlgebra.restrictScalars ℚ ℝ _
  exact hs.exp_right.eq.symm

end OperatorDerivativeRewrite.Foundation.MultivariateFactorialSubstitution
