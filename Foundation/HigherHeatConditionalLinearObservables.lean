import Foundation.HigherHeatConditionalRefinement

/-! Actual signed conditioning of linear increment observables. -/
noncomputable section
open scoped NNReal BigOperators Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatConditionalLinearObservables
open PureOrderPolynomialConditioning HigherHeatConditionalRefinement HigherHeatMultivariateMoments
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem mean_X_zero (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i) (i : ι) :
    HigherHeatMultivariateMoments.mean m hm t ht (MvPolynomial.X i) = 0 := by
  change HigherHeatMultivariateMoments.mean m hm t ht
    (MvPolynomial.monomial (Finsupp.single i 1) 1) = 0
  apply mean_monomial_off_order m hm t ht _ _ i
  simp only [Finsupp.single_eq_same]
  intro h
  have he := Nat.dvd_one.mp h
  omega

theorem conditioning_X (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i)
    (S : Finset ι) (i : ι) :
    conditioning (2*m) (parameters m t) S (MvPolynomial.X i) =
      if i ∈ S then MvPolynomial.X i else 0 := by
  classical
  by_cases hi : i ∈ S
  · rw [ite_eq_left hi]
    apply conditioning_supported_monomial
    intro j hj
    by_cases hji : j=i
    · subst j
      exact False.elim (hj hi)
    · simp [hji]
  · rw [ite_eq_right hi]
    apply MvPolynomial.funext
    intro x
    rw [map_zero]
    have he := actual_kernel_conditioning m hm t ht S x (MvPolynomial.X i)
    have hf : freeze S x (MvPolynomial.X i) = MvPolynomial.X i := by simp [freeze, hi]
    rw [hf, mean_X_zero m hm t ht i] at he
    exact Complex.ofReal_injective he.symm

end OperatorDerivativeRewrite.Foundation.HigherHeatConditionalLinearObservables
