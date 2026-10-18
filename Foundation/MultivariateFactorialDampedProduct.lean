import Foundation.MultivariateFactorialSubstitution
import Mathlib.Data.Nat.Choose.Bounds

/-! Contractive damped multiplication on complete factorial coefficient spaces.
The core action is P(x/2)Q(x/2); ordinary multiplication is not asserted bounded. -/
noncomputable section
open scoped ENNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.MultivariateFactorialDampedProduct
open MultivariateFactorialDomain MultivariateFactorialSubstitution
variable {ι : Type*} [DecidableEq ι]

def mix (a b : ℕ) : ℝ := ((a+b).choose b : ℝ)/(2:ℝ)^(a+b)

omit [DecidableEq ι] in
theorem mix_nonneg (a b : ℕ) : 0 ≤ mix a b := by unfold mix; positivity

omit [DecidableEq ι] in
theorem mix_le_one (a b : ℕ) : mix a b ≤ 1 := by
  apply (div_le_one (by positivity : (0:ℝ)<2^(a+b))).mpr
  exact_mod_cast Nat.choose_le_two_pow (a+b) b

omit [DecidableEq ι] in
theorem mix_factorial (a b : ℕ) :
    mix a b * ((a.factorial:ℝ)*(b.factorial:ℝ)) = ((a+b).factorial:ℝ)/(2:ℝ)^(a+b) := by
  have he : ((a+b).choose b:ℝ)*(a.factorial:ℝ)*(b.factorial:ℝ) = ((a+b).factorial:ℝ) := by
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial a b
  calc
    _ = (((a+b).choose b:ℝ)*(a.factorial:ℝ)*(b.factorial:ℝ))/(2:ℝ)^(a+b) := by unfold mix; ring
    _ = _ := by rw [he]

def pairAtom (d e : ι →₀ ℕ) : H ι := lp.single 1 (d+e) (mix d.degree e.degree)

theorem pairAtom_bound (d e : ι →₀ ℕ) : ‖pairAtom d e‖ ≤ 1 := by
  rw [pairAtom, lp.norm_single (by norm_num : (0:ℝ≥0∞)<1), Real.norm_eq_abs,
    abs_of_nonneg (mix_nonneg _ _)]
  exact mix_le_one _ _

def rightAtom (d : ι →₀ ℕ) : H ι →L[ℝ] H ι :=
  L1BoundedSynthesis.synthesis (pairAtom d) (pairAtom_bound d)

theorem rightAtom_bound (d : ι →₀ ℕ) : ‖rightAtom d‖ ≤ 1 :=
  L1BoundedSynthesis.synthesis_norm _ _

def dampedProduct : H ι →L[ℝ] H ι →L[ℝ] H ι :=
  L1BoundedSynthesis.synthesis rightAtom rightAtom_bound

theorem dampedProduct_norm : ‖dampedProduct (ι := ι)‖ ≤ 1 :=
  L1BoundedSynthesis.synthesis_norm _ _

theorem dampedProduct_single (d e : ι →₀ ℕ) (c h : ℝ) :
    dampedProduct (lp.single 1 d c) (lp.single 1 e h) = (c*h) • pairAtom d e := by
  change (L1BoundedSynthesis.synthesis rightAtom rightAtom_bound (lp.single 1 d c)) _ = _
  rw [L1BoundedSynthesis.synthesis_single]
  change c • (rightAtom d (lp.single 1 e h)) = _
  rw [rightAtom, L1BoundedSynthesis.synthesis_single, smul_smul]

theorem dampedProduct_bound (u v : H ι) : ‖dampedProduct u v‖ ≤ ‖u‖*‖v‖ := by
  have he : ‖dampedProduct u‖ ≤ ‖u‖ := by
    simpa only [one_mul] using (dampedProduct (ι := ι)).le_of_opNorm_le dampedProduct_norm u
  exact ((dampedProduct u).le_opNorm v).trans (mul_le_mul_of_nonneg_right he (norm_nonneg v))

omit [DecidableEq ι] in
theorem weight_const (c : ℝ) (d : ι →₀ ℕ) : weight (fun _ => c) d = c^d.degree := by
  rw [weight, Finset.prod_pow_eq_pow_sum]
  rfl

omit [DecidableEq ι] in
theorem dilation_monomial (c : ℝ) (d : ι →₀ ℕ) (a : ℝ) :
    polynomialSubstitution id (fun _ => c) (MvPolynomial.monomial d a) =
      MvPolynomial.monomial d (a*c^d.degree) := by
  rw [polynomialSubstitution_monomial, weight_const]
  simp only [Finsupp.mapDomain_id]

theorem dampedProduct_monomials (d e : ι →₀ ℕ) (c h : ℝ) :
    dampedProduct (polynomial (MvPolynomial.monomial d c)) (polynomial (MvPolynomial.monomial e h)) =
      polynomial (polynomialSubstitution id (fun _ => (1/2:ℝ))
        (MvPolynomial.monomial d c * MvPolynomial.monomial e h)) := by
  rw [polynomial_monomial, polynomial_monomial, dampedProduct_single,
    MvPolynomial.monomial_mul_monomial, dilation_monomial, polynomial_monomial]
  rw [pairAtom, ← lp.single_smul]
  simp only [smul_eq_mul, map_add]
  congr 1
  have hf := mix_factorial d.degree e.degree
  rw [div_pow, one_pow]
  calc
    _ = (c*h) * (mix d.degree e.degree * ((d.degree.factorial:ℝ)*(e.degree.factorial:ℝ))) := by ring
    _ = _ := by rw [hf]; ring

theorem dampedProduct_polynomial (P Q : MvPolynomial ι ℝ) :
    dampedProduct (polynomial P) (polynomial Q) =
      polynomial (polynomialSubstitution id (fun _ => (1/2:ℝ)) (P*Q)) := by
  induction P using MvPolynomial.induction_on' generalizing Q with
  | monomial d c =>
    induction Q using MvPolynomial.induction_on' with
    | monomial e h => exact dampedProduct_monomials d e c h
    | add Q R hQ hR =>
      change dampedProduct (polynomial (MvPolynomial.monomial d c)) (polynomialMap (Q+R)) =
        polynomialMap (polynomialSubstitution id (fun _ => (1/2:ℝ)) (MvPolynomial.monomial d c*(Q+R)))
      rw [map_add, map_add, mul_add, map_add, map_add]
      exact congrArg₂ (·+·) hQ hR
  | add P R hP hR =>
    change dampedProduct (polynomialMap (P+R)) (polynomial Q) =
      polynomialMap (polynomialSubstitution id (fun _ => (1/2:ℝ)) ((P+R)*Q))
    rw [map_add, map_add, add_apply, add_mul, map_add, map_add]
    exact congrArg₂ (·+·) (hP Q) (hR Q)

theorem dampedProduct_unique (L : H ι →L[ℝ] H ι →L[ℝ] H ι)
    (hL : ∀ P Q, L (polynomial P) (polynomial Q) =
      polynomial (polynomialSubstitution id (fun _ => (1/2:ℝ)) (P*Q))) : L = dampedProduct := by
  apply ContinuousLinearMap.coeFn_injective
  apply polynomial_dense.equalizer L.continuous (dampedProduct (ι := ι)).continuous
  funext P
  apply ContinuousLinearMap.coeFn_injective
  apply polynomial_dense.equalizer (L (polynomial P)).continuous (dampedProduct (polynomial P)).continuous
  funext Q
  exact (hL P Q).trans (dampedProduct_polynomial P Q).symm

theorem dampedProduct_comm (u v : H ι) : dampedProduct u v = dampedProduct v u := by
  have he : (dampedProduct (ι := ι)).flip = dampedProduct := by
    apply dampedProduct_unique
    intro P Q
    change dampedProduct (polynomial Q) (polynomial P) = _
    rw [dampedProduct_polynomial, mul_comm Q P]
  exact (DFunLike.congr_fun (DFunLike.congr_fun he u) v).symm

omit [DecidableEq ι] in
theorem dilation_rename {κ : Type*} (f : ι → κ) (c : ℝ) (P : MvPolynomial ι ℝ) :
    polynomialSubstitution id (fun _ => c) (MvPolynomial.rename f P) =
      MvPolynomial.rename f (polynomialSubstitution id (fun _ => c) P) := by
  have he : (polynomialSubstitution (id : κ → κ) (fun _ => c)).comp (MvPolynomial.rename f) =
      (MvPolynomial.rename f).comp (polynomialSubstitution id (fun _ => c)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [polynomialSubstitution]
  exact AlgHom.congr_fun he P

theorem dampedProduct_rename {κ : Type*} [DecidableEq κ] (e : ι ↪ κ) (u v : H ι) :
    dampedProduct (MultivariateFactorialRenaming.renameOperator e u)
      (MultivariateFactorialRenaming.renameOperator e v) =
        MultivariateFactorialRenaming.renameOperator e (dampedProduct u v) := by
  have hcore (P Q : MvPolynomial ι ℝ) :
      dampedProduct (MultivariateFactorialRenaming.renameOperator e (polynomial P))
          (MultivariateFactorialRenaming.renameOperator e (polynomial Q)) =
        MultivariateFactorialRenaming.renameOperator e (dampedProduct (polynomial P) (polynomial Q)) := by
    rw [MultivariateFactorialRenaming.renaming_polynomial,
      MultivariateFactorialRenaming.renaming_polynomial, dampedProduct_polynomial,
      dampedProduct_polynomial, MultivariateFactorialRenaming.renaming_polynomial,
      ]
    have hm : (MvPolynomial.rename e) P * (MvPolynomial.rename e) Q =
        (MvPolynomial.rename e) (P*Q) := (map_mul (MvPolynomial.rename e) P Q).symm
    rw [hm, dilation_rename]
  have he : (fun u : H ι => dampedProduct (MultivariateFactorialRenaming.renameOperator e u)
      (MultivariateFactorialRenaming.renameOperator e v)) =
      (fun u => MultivariateFactorialRenaming.renameOperator e (dampedProduct u v)) := by
    apply polynomial_dense.equalizer (by fun_prop) (by fun_prop)
    funext P
    have hr : (fun v : H ι => dampedProduct (MultivariateFactorialRenaming.renameOperator e (polynomial P))
        (MultivariateFactorialRenaming.renameOperator e v)) =
        (fun v => MultivariateFactorialRenaming.renameOperator e (dampedProduct (polynomial P) v)) := by
      apply polynomial_dense.equalizer (by fun_prop) (by fun_prop)
      funext Q
      exact hcore P Q
    exact congrFun hr v
  exact congrFun he u

end OperatorDerivativeRewrite.Foundation.MultivariateFactorialDampedProduct
