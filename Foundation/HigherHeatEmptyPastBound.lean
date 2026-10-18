import Foundation.HigherHeatFiniteCausalBound

/-! Exact full-zeroing and uniform empty-past signed conditioning bounds. -/
noncomputable section
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.HigherHeatEmptyPastBound
open HigherHeatPolynomialCylinders HigherHeatPolynomialCoordinates HigherHeatPositionVariation
open HigherHeatFiniteCausalBound FiniteCoordinateConditioning MultivariateFactorialSubstitution
open MultivariateFactorialDomain PureOrderPolynomialConditioning MultivariateSignedHeatChain

def zeroAll (n : ℕ) : Test n →ₐ[ℝ] Test n := polynomialSubstitution id (fun _ => 0)

theorem eval_zeroAll (n : ℕ) (P : Test n) (x : Fin (size n) → ℝ) :
    MvPolynomial.eval x (zeroAll n P) = MvPolynomial.eval (fun _ => 0) P := by
  rw [zeroAll, eval_polynomialSubstitution]
  simp only [zero_mul]

theorem zeroAll_coordinates (n : ℕ) (P : Test n) :
    zeroAll n (coordinates n P) = coordinates n (zeroAll n P) := by
  apply MvPolynomial.funext
  intro x
  rw [eval_zeroAll, eval_coordinates, eval_coordinates, eval_zeroAll]
  exact congrArg (fun y : Fin (size n) → ℝ => MvPolynomial.eval y P)
    (map_zero (cumulativeEquiv (size n)))

theorem inverse_zeroAll (n : ℕ) (P : Test n) :
    (coordinates n).symm (zeroAll n P) = zeroAll n ((coordinates n).symm P) := by
  apply (coordinates n).injective
  rw [AlgEquiv.apply_symm_apply, ← zeroAll_coordinates, AlgEquiv.apply_symm_apply]

def zeroAllOperator (n : ℕ) : H (Fin (size n)) →L[ℝ] H (Fin (size n)) :=
  substitute id (fun _ => 0) (by intro _; norm_num)

theorem zeroAllOperator_encode (n : ℕ) (P : Test n) :
    zeroAllOperator n (encode n P) = encode n (zeroAll n P) := by
  rw [encode_apply, encode_apply, inverse_zeroAll]
  exact substitute_polynomial _ _ _ _

theorem encode_zeroAll_bound (n : ℕ) (P : Test n) : ‖encode n (zeroAll n P)‖ ≤ ‖encode n P‖ := by
  rw [← zeroAllOperator_encode]
  simpa only [one_mul] using
    (zeroAllOperator n).le_of_opNorm_le (substitute_bound _ _ _) (encode n P)

theorem zeroChain_full (n : ℕ) (P : Test n) :
    zeroChain (Finset.univ : Finset (Fin (size n))).toList P = zeroAll n P := by
  apply MvPolynomial.funext
  intro x
  rw [eval_zeroChain, eval_zeroAll]
  simp

theorem full_totalTime (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    totalTime (steps n (fun _ => HigherHeatDyadicLaws.duration T n)
      (fun _ => HigherHeatDyadicLaws.duration_pos T hT n) Finset.univ.toList) = (T:ℝ) := by
  rw [totalTime_steps]
  have he (js : List (Fin (size n))) :
      (js.map (fun _ => (HigherHeatDyadicLaws.duration T n:ℝ))).sum =
        (js.length:ℝ) * (HigherHeatDyadicLaws.duration T n:ℝ) := by
    induction js with
    | nil => simp
    | cons j js ih => simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
        Nat.cast_one, ih]; ring
  rw [he, Finset.length_toList, Finset.card_univ, Fintype.card_fin]
  simp only [HigherHeatDyadicLaws.duration, NNReal.coe_div, NNReal.coe_natCast]
  change (size n:ℝ) * ((T:ℝ)/(size n:ℝ)) = (T:ℝ)
  field_simp [Nat.ne_of_gt (HigherHeatDyadicLaws.gridSize_pos n)]

theorem local_empty_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (P : Test n) :
    ‖encode n (HigherHeatDyadicConditioning.localProjection m T n ∅ P)‖ ≤
      Real.exp (T:ℝ) * ‖encode n P‖ := by
  let a : Fin (size n) → ℝ := parameters m (fun _ => HigherHeatDyadicLaws.duration T n)
  have hf := conditioning_factor (2*m) (by omega) a
    (Finset.univ : Finset (Fin (size n))).toList (Finset.nodup_toList _) P
  have hs : (Finset.univ : Finset (Fin (size n))).toList.toFinset = Finset.univ := by
    ext i
    simp
  rw [hs, Finset.sdiff_self] at hf
  change ‖encode n (conditioning (2*m) a ∅ P)‖ ≤ _
  rw [hf, zeroChain_full]
  have hc := heatChain_encode_bound n m hm (fun _ => HigherHeatDyadicLaws.duration T n)
    (fun _ => HigherHeatDyadicLaws.duration_pos T hT n) Finset.univ.toList P
  rw [full_totalTime n T hT] at hc
  exact (encode_zeroAll_bound n _).trans hc

end OperatorDerivativeRewrite.Foundation.HigherHeatEmptyPastBound
