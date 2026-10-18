import Foundation.HigherHeatPolynomialRefinement
import Mathlib.Algebra.MvPolynomial.Funext

/-! Pointwise kernel representation and block compatibility of signed polynomial conditioning. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.HigherHeatConditionalRefinement
open HigherHeatSignedLaws HigherHeatMultivariateMoments HigherHeatPolynomialRefinement
  PureOrderPolynomialConditioning PseudoPolynomialStein HigherHeatBlockCoarsening
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

open Classical in
def freeze (S : Finset ι) (x : ι → ℝ) : MvPolynomial ι ℝ →ₐ[ℝ] MvPolynomial ι ℝ :=
  MvPolynomial.aeval (fun i => if i ∈ S then MvPolynomial.C (x i) else MvPolynomial.X i)

omit [Fintype ι] [Fintype κ] in
open Classical in
theorem eval_freeze (S : Finset ι) (x y : ι → ℝ) (P : MvPolynomial ι ℝ) :
    MvPolynomial.eval y (freeze S x P) =
      MvPolynomial.eval (fun i => if i ∈ S then x i else y i) P := by
  classical
  have he : (MvPolynomial.aeval y).comp (freeze S x) =
      MvPolynomial.aeval (fun i => if i ∈ S then x i else y i) := by
    apply MvPolynomial.algHom_ext
    intro i
    by_cases hi : i ∈ S <;> simp [freeze, hi]
  exact DFunLike.congr_fun he P

open Classical in
def future (S : Finset ι) (d : ι →₀ ℕ) : ι →₀ ℕ := d.filter (fun i => i ∉ S)

omit [Fintype ι] [Fintype κ] in
open Classical in
theorem future_apply (S : Finset ι) (d : ι →₀ ℕ) (i : ι) :
    future S d i = if i ∈ S then 0 else d i := by
  classical
  by_cases hi : i ∈ S <;> simp [future, hi]

open Classical in
def pastValue (S : Finset ι) (x : ι → ℝ) (d : ι →₀ ℕ) : ℝ :=
  ∏ i, if i ∈ S then x i ^ d i else 1

omit [Fintype κ] in
theorem freeze_monomial (S : Finset ι) (x : ι → ℝ) (d : ι →₀ ℕ) (c : ℝ) :
    freeze S x (MvPolynomial.monomial d c) =
      MvPolynomial.monomial (future S d) (c * pastValue S x d) := by
  classical
  apply MvPolynomial.funext
  intro y
  rw [eval_freeze, MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
  rw [Finsupp.prod_fintype d _ (fun _ => pow_zero _),
    Finsupp.prod_fintype (future S d) _ (fun _ => pow_zero _)]
  have hp : (∏ i, (if i ∈ S then x i else y i)^d i) =
      pastValue S x d * ∏ i, y i ^ future S d i := by
    rw [pastValue, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ S <;> simp [hi, future_apply]
  rw [hp]
  ring

omit [Fintype κ] in
theorem future_moments (p : ℕ) (a : ι → ℝ) (S : Finset ι) (d : ι →₀ ℕ) :
    (∏ i, moment p (a i) (future S d i)) = factor p a S d := by
  classical
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> simp [future_apply, hi, moment_zero]

omit [Fintype κ] in
theorem kept_value (S : Finset ι) (x : ι → ℝ) (d : ι →₀ ℕ) :
    (∏ i, x i ^ keep S d i) = pastValue S x d := by
  classical
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> simp [keep_apply, hi]

omit [Fintype κ] in
theorem actual_kernel_conditioning (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (S : Finset ι) (x : ι → ℝ) (P : MvPolynomial ι ℝ) :
    mean m hm t ht (freeze S x P) =
      value (conditioning (2*m) (parameters m t) S P) x := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [freeze_monomial, actual_mean_monomial, future_moments, conditioning_monomial,
      value_monomial]
    simp only [HigherHeatChronologicalProbes.powers, ← Complex.ofReal_pow,
      ← Complex.ofReal_prod, kept_value, Complex.real_smul, ← Complex.ofReal_mul]
    congr 1
    ring
  | add P Q hP hQ => rw [map_add, map_add, map_add, value_add, hP, hQ]


open Classical in
def pastCells (p : ι → κ) (S : Finset κ) : Finset ι :=
  Finset.univ.filter (fun j => p j ∈ S)

omit [Fintype κ] in
theorem freeze_pullback (p : ι → κ) (S : Finset κ) (x : ι → ℝ)
    (P : MvPolynomial κ ℝ) :
    freeze (pastCells p S) x (pullback p P) = pullback p (freeze S (coarsen p x) P) := by
  classical
  apply MvPolynomial.funext
  intro y
  rw [eval_freeze, eval_pullback, eval_pullback, eval_freeze]
  apply congrArg (fun z => MvPolynomial.eval z P)
  funext k
  by_cases hk : k ∈ S
  · rw [ite_eq_left hk]
    apply Finset.sum_congr rfl
    intro j hj
    have hpj : p j = k := (Finset.mem_filter.mp hj).2
    simp [pastCells, hpj, hk]
  · rw [ite_eq_right hk]
    apply Finset.sum_congr rfl
    intro j hj
    have hpj : p j = k := (Finset.mem_filter.mp hj).2
    simp [pastCells, hpj, hk]

theorem conditional_refinement_value (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ j, 0 < t j) (p : ι → κ) (hp : Function.Surjective p)
    (S : Finset κ) (P : MvPolynomial κ ℝ) (x : ι → ℝ) :
    value (conditioning (2*m) (parameters m t) (pastCells p S) (pullback p P)) x =
      value (pullback p (conditioning (2*m) (parameters m (blockTimes p t)) S P)) x := by
  calc
    _ = mean m hm t ht (freeze (pastCells p S) x (pullback p P)) :=
      (actual_kernel_conditioning m hm t ht _ x _).symm
    _ = mean m hm t ht (pullback p (freeze S (coarsen p x) P)) := by rw [freeze_pullback]
    _ = mean m hm (blockTimes p t) (blockTimes_pos p hp t ht) (freeze S (coarsen p x) P) :=
      actual_mean_pullback m hm t ht p hp _
    _ = value (conditioning (2*m) (parameters m (blockTimes p t)) S P) (coarsen p x) :=
      actual_kernel_conditioning m hm _ _ S _ P
    _ = _ := (value_pullback p _ x).symm

theorem conditional_refinement (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ j, 0 < t j) (p : ι → κ) (hp : Function.Surjective p)
    (S : Finset κ) (P : MvPolynomial κ ℝ) :
    conditioning (2*m) (parameters m t) (pastCells p S) (pullback p P) =
      pullback p (conditioning (2*m) (parameters m (blockTimes p t)) S P) := by
  apply MvPolynomial.funext
  intro x
  exact Complex.ofReal_injective (conditional_refinement_value m hm t ht p hp S P x)

theorem conditional_difference_refinement (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ j, 0 < t j) (p : ι → κ) (hp : Function.Surjective p)
    (S T : Finset κ) (P : MvPolynomial κ ℝ) :
    conditioning (2*m) (parameters m t) (pastCells p T) (pullback p P) -
        conditioning (2*m) (parameters m t) (pastCells p S) (pullback p P) =
      pullback p (conditioning (2*m) (parameters m (blockTimes p t)) T P -
        conditioning (2*m) (parameters m (blockTimes p t)) S P) := by
  rw [conditional_refinement m hm t ht p hp T P, conditional_refinement m hm t ht p hp S P,
    map_sub]


end OperatorDerivativeRewrite.Foundation.HigherHeatConditionalRefinement
