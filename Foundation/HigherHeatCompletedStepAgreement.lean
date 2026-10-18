import Foundation.HigherHeatStepRefinement

/-! Agreement of the bounded time integral and actual adapted signed step sums
as functionals on the whole common analytic completion. -/
noncomputable section
open scoped NNReal ENNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatCompletedStepAgreement
open HigherHeatPolynomialCylinders HigherHeatGridDoubling HigherHeatDyadicStepAgreement
open HigherHeatStepRefinement HigherHeatWeakTimeAdjoint HigherHeatAnalyticCylinderDomain
open HigherHeatCompletedPairing HigherHeatAdaptedStepDuality

theorem agreement_finer (d : ℕ) (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (hF : j ∉ F.vars) (G : Test (n+d)) :
    firstChannel m T (coefficientField n m hm T hT j F) (core (cylinderOf (n+d) G)) =
      pairing m hm T hT (core (cylinderOf n (F * MvPolynomial.X j)))
        (core (cylinderOf (n+d) G)) := by
  induction d generalizing n with
  | zero => exact actual_adapted_step_agreement n m hm T hT j F G hF
  | succ d ih =>
    have he : n + (d+1) = (n+1)+d := by omega
    revert G
    rw [he]
    intro G
    have hl : pairBlock (evenIndex j) = j := by apply Fin.ext; simp [pairBlock, evenIndex]
    have hr : pairBlock (oddIndex j) = j := by
      apply Fin.ext
      dsimp [pairBlock, oddIndex]
      omega
    rw [coefficientField_split n m hm T hT j F, stochastic_polynomial_split n j F]
    simp only [map_add, add_apply]
    exact congrArg₂ (·+·)
      (ih (n+1) (evenIndex j) (HigherHeatPolynomialCylinders.step n F)
        (step_missing n j F hF _ hl) G)
      (ih (n+1) (oddIndex j) (HigherHeatPolynomialCylinders.step n F)
        (step_missing n j F hF _ hr) G)

theorem agreement_cylinder (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (hF : j ∉ F.vars) (G : Cylinder) :
    firstChannel m T (coefficientField n m hm T hT j F) (core G) =
      pairing m hm T hT (core (cylinderOf n (F * MvPolynomial.X j))) (core G) := by
  apply HigherHeatCylindricalConditioning.tail_induction n (fun G =>
    firstChannel m T (coefficientField n m hm T hT j F) (core G) =
      pairing m hm T hT (core (cylinderOf n (F * MvPolynomial.X j))) (core G)) _ G
  intro N hn P
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact agreement_finer d n m hm T hT j F hF P

theorem agreement_dual (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) (hF : j ∉ F.vars) :
    firstChannel m T (coefficientField n m hm T hT j F) =
      pairing m hm T hT (core (cylinderOf n (F * MvPolynomial.X j))) := by
  apply ContinuousLinearMap.coeFn_injective
  apply core_dense.equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  funext G
  exact agreement_cylinder n m hm T hT j F hF G

theorem adapted_sum_dual (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (F : Fin (size n) → Test n) (hF : Adapted F) :
    firstChannel m T (adaptedField n m hm T hT F) =
      pairing m hm T hT (core (cylinderOf n (stepPolynomial F))) := by
  simp only [adaptedField, stepPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact agreement_dual n m hm T hT j (F j) (adapted_missing hF j)

theorem adapted_sum_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (F : Fin (size n) → Test n) (hF : Adapted F) :
    ‖pairing m hm T hT (core (cylinderOf n (stepPolynomial F)))‖ ≤
      ((2*m:ℕ):ℝ)*(T:ℝ)*‖adaptedField n m hm T hT F‖ := by
  rw [← adapted_sum_dual n m hm T hT F hF]
  exact firstChannel_bound m T _

end OperatorDerivativeRewrite.Foundation.HigherHeatCompletedStepAgreement
