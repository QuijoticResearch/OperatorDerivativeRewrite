import Foundation.HigherHeatPositionTransport
import Foundation.HigherHeatAnalyticClamping
import Foundation.MultivariateSignedHeatChain
import Foundation.HigherHeatDyadicConditioning

/-! Actual finite signed conditioning and its uniform position-coordinate bound. -/
noncomputable section
open scoped NNReal BigOperators

namespace OperatorDerivativeRewrite.Foundation.HigherHeatFiniteCausalBound
open HigherHeatPolynomialCylinders HigherHeatPolynomialCoordinates HigherHeatPositionTransport
open HigherHeatAnalyticClamping FiniteCoordinateConditioning
open PureOrderPolynomialConditioning MultivariateFactorialDomain
open MultivariateSignedHeatChain MultivariateFactorialHeat

def steps (n : ℕ) (t : Fin (size n) → ℝ≥0) (ht : ∀ i, 0 < t i)
    (js : List (Fin (size n))) : List (Step (Fin (size n))) :=
  js.map (fun j => ⟨t j, ht j, direction (size n) j, direction_bound (size n) j⟩)

theorem operator_encode (n m : ℕ) (hm : 0 < m) (t : Fin (size n) → ℝ≥0)
    (ht : ∀ i, 0 < t i) (js : List (Fin (size n))) (P : Test n) :
    operator m (steps n t ht js) (encode n P) =
      encode n (heatChain (2*m) (by omega) (parameters m t) js P) := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    change evolution (2*m) (parameters m t j) (direction (size n) j) (direction_bound (size n) j)
      (operator m (steps n t ht js) (encode n P)) =
        encode n (MultivariateDirectionalKernel.transport (2*m) (by omega) (parameters m t j)
          (Pi.single j 1) (heatChain (2*m) (by omega) (parameters m t) js P))
    rw [ih, evolution_encode n (2*m) (by omega)]

theorem heatChain_encode_bound (n m : ℕ) (hm : 0 < m) (t : Fin (size n) → ℝ≥0)
    (ht : ∀ i, 0 < t i) (js : List (Fin (size n))) (P : Test n) :
    ‖encode n (heatChain (2*m) (by omega) (parameters m t) js P)‖ ≤
      Real.exp (totalTime (steps n t ht js)) * ‖encode n P‖ := by
  rw [← operator_encode n m hm t ht]
  exact (operator m (steps n t ht js)).le_of_opNorm_le (operator_bound m _) _

theorem zeroChain_future (n : ℕ) (r : Fin (size n)) (js : List (Fin (size n)))
    (hjs : ∀ i, i ∈ js ↔ r < i) (P : Test n) : zeroChain js P = zeroFuture n r P := by
  apply MvPolynomial.funext
  intro x
  rw [eval_zeroChain, zeroFuture, MultivariateFactorialSubstitution.eval_polynomialSubstitution]
  apply congrArg (fun y : Fin (size n) → ℝ => MvPolynomial.eval y P)
  funext i
  by_cases hi : i ≤ r
  · simp [hjs i, not_lt_of_ge hi, mask, hi]
  · simp [hjs i, lt_of_not_ge hi, mask, hi]

theorem conditioning_encode_bound (n m : ℕ) (hm : 0 < m) (t : Fin (size n) → ℝ≥0)
    (ht : ∀ i, 0 < t i) (r : Fin (size n)) (js : List (Fin (size n)))
    (hdup : js.Nodup) (hjs : ∀ i, i ∈ js ↔ r < i) (P : Test n) :
    ‖encode n (conditioning (2*m) (parameters m t) (Finset.univ \ js.toFinset) P)‖ ≤
      Real.exp (totalTime (steps n t ht js)) * ‖encode n P‖ := by
  rw [conditioning_factor (2*m) (by omega) (parameters m t) js hdup,
    zeroChain_future n r js hjs]
  exact (encode_zeroFuture_bound n r _).trans (heatChain_encode_bound n m hm t ht js P)

def futureIndices (n : ℕ) (r : Fin (size n)) : List (Fin (size n)) :=
  (Finset.univ.filter (fun i => r < i)).toList

theorem futureIndices_nodup (n : ℕ) (r : Fin (size n)) : (futureIndices n r).Nodup :=
  Finset.nodup_toList _

theorem futureIndices_mem (n : ℕ) (r i : Fin (size n)) : i ∈ futureIndices n r ↔ r < i := by
  simp [futureIndices]

theorem futureIndices_length (n : ℕ) (r : Fin (size n)) : (futureIndices n r).length ≤ size n := by
  simpa only [futureIndices, Finset.length_toList, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_filter_le (s := Finset.univ) (p := fun i : Fin (size n) => r < i))

theorem totalTime_steps (n : ℕ) (t : Fin (size n) → ℝ≥0) (ht : ∀ i, 0 < t i)
    (js : List (Fin (size n))) : totalTime (steps n t ht js) = (js.map (fun i => (t i:ℝ))).sum := by
  simp only [totalTime, steps, List.map_map, Function.comp_def]

theorem totalTime_dyadic (n : ℕ) (T : ℝ≥0) (hT : 0 < T) (r : Fin (size n)) :
    totalTime (steps n (fun _ => HigherHeatDyadicLaws.duration T n)
      (fun _ => HigherHeatDyadicLaws.duration_pos T hT n) (futureIndices n r)) ≤ (T:ℝ) := by
  rw [totalTime_steps]
  have he (js : List (Fin (size n))) :
      (js.map (fun _ => (HigherHeatDyadicLaws.duration T n:ℝ))).sum =
        (js.length:ℝ) * (HigherHeatDyadicLaws.duration T n:ℝ) := by
    induction js with
    | nil => simp
    | cons j js ih => simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
        Nat.cast_one, ih]; ring
  rw [he]
  have hcard : ((futureIndices n r).length:ℝ) ≤ (size n:ℝ) := by
    exact_mod_cast futureIndices_length n r
  calc
    _ ≤ (size n:ℝ) * (HigherHeatDyadicLaws.duration T n:ℝ) :=
      mul_le_mul_of_nonneg_right hcard (HigherHeatDyadicLaws.duration T n).coe_nonneg
    _ = (T:ℝ) := by
      simp only [HigherHeatDyadicLaws.duration, NNReal.coe_div, NNReal.coe_natCast]
      change (size n:ℝ) * ((T:ℝ)/(size n:ℝ)) = (T:ℝ)
      field_simp [Nat.ne_of_gt (HigherHeatDyadicLaws.gridSize_pos n)]

theorem future_retained (n : ℕ) (r : Fin (size n)) :
    Finset.univ \ (futureIndices n r).toFinset =
      HigherHeatDyadicConditioning.initialPast n (r.val+1) := by
  ext i
  simp only [Finset.mem_sdiff, Finset.mem_univ, List.mem_toFinset, futureIndices_mem,
    HigherHeatDyadicConditioning.initialPast, Finset.mem_filter, true_and]
  change ¬r.val < i.val ↔ i.val < r.val+1
  omega

theorem localProjection_encode_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (r : Fin (size n)) (P : Test n) :
    ‖encode n (HigherHeatDyadicConditioning.localProjection m T n
      (HigherHeatDyadicConditioning.initialPast n (r.val+1)) P)‖ ≤
        Real.exp (T:ℝ) * ‖encode n P‖ := by
  have hc := conditioning_encode_bound n m hm
    (fun _ => HigherHeatDyadicLaws.duration T n) (fun _ => HigherHeatDyadicLaws.duration_pos T hT n)
    r (futureIndices n r) (futureIndices_nodup n r) (futureIndices_mem n r) P
  rw [future_retained] at hc
  exact hc.trans (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (totalTime_dyadic n T hT r)) (norm_nonneg _))

end OperatorDerivativeRewrite.Foundation.HigherHeatFiniteCausalBound
