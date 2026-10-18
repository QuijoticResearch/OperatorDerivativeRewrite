import Foundation.PureOrderPolynomialConditioning

/-! Actual finite signed conditioning is symmetric for polynomial-product expectation. -/
noncomputable section
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.PureOrderConditionalPairing
open PseudoPolynomialStein PureOrderPolynomialConditioning HigherHeatMultivariateMoments
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem supported_monomial (S : Finset ι) (d : ι →₀ ℕ) (c : ℝ)
    (hd : ∀ i, i ∉ S → d i = 0) : supported S (MvPolynomial.monomial d c) := by
  classical
  intro e he i hi
  have heq : e = d := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset he)
  subst e
  exact hd i hi

omit [Fintype ι] in
theorem supported_add (S : Finset ι) (P Q : MvPolynomial ι ℝ)
    (hP : supported S P) (hQ : supported S Q) : supported S (P+Q) := by
  classical
  intro d hd i hi
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · exact hP d h i hi
  · exact hQ d h i hi

theorem conditioning_supported (p : ℕ) (a : ι → ℝ) (S : Finset ι)
    (P : MvPolynomial ι ℝ) : supported S (conditioning p a S P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [conditioning_monomial]
    apply supported_monomial
    intro i hi
    simp [keep_apply, hi]
  | add P Q hP hQ =>
    rw [map_add]
    exact supported_add S _ _ hP hQ

theorem actual_pair_projected (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (S : Finset ι) (P Q : MvPolynomial ι ℝ) :
    mean m hm t ht (conditioning (2*m) (parameters m t) S P *
      conditioning (2*m) (parameters m t) S Q) =
      mean m hm t ht (P * conditioning (2*m) (parameters m t) S Q) := by
  have he := actual_mean_conditioning m hm t ht S
    (P * conditioning (2*m) (parameters m t) S Q)
  rw [conditioning_mul_supported _ _ _ P _ (conditioning_supported _ _ _ Q)] at he
  exact he

theorem actual_pair_symmetric (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (S : Finset ι) (P Q : MvPolynomial ι ℝ) :
    mean m hm t ht (conditioning (2*m) (parameters m t) S P * Q) =
      mean m hm t ht (P * conditioning (2*m) (parameters m t) S Q) := by
  calc
    _ = mean m hm t ht (Q * conditioning (2*m) (parameters m t) S P) := by rw [mul_comm]
    _ = mean m hm t ht (conditioning (2*m) (parameters m t) S Q *
      conditioning (2*m) (parameters m t) S P) := (actual_pair_projected m hm t ht S Q P).symm
    _ = mean m hm t ht (conditioning (2*m) (parameters m t) S P *
      conditioning (2*m) (parameters m t) S Q) := by rw [mul_comm]
    _ = _ := actual_pair_projected m hm t ht S P Q

end OperatorDerivativeRewrite.Foundation.PureOrderConditionalPairing
