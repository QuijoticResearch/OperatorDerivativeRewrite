import Foundation.HigherHeatCommonDerivative
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Topology.Sequences

/-! All-time cutoff directional derivatives and strongly measurable applied powers. -/
noncomputable section
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatTimeDerivative
open HigherHeatPolynomialCylinders HigherHeatPolynomialCoordinates HigherHeatAnalyticCylinderDomain
open HigherHeatCommonDerivative MeasureTheory Filter Classical

def direction (t : ℝ) (s : Time) : ℝ := if t ≤ (s:ℝ) then 1 else 0

theorem direction_bound (t : ℝ) (s : Time) : |direction t s| ≤ 1 := by
  unfold direction
  split <;> norm_num

def atTime (t : ℝ) : Domain →L[ℝ] Domain := operator (direction t) (direction_bound t)

theorem atTime_pow_bound (t : ℝ) (r : ℕ) (u : Domain) : ‖((atTime t)^r) u‖ ≤ ‖u‖ :=
  operator_pow_bound (direction t) (direction_bound t) r u

def cell (n : ℕ) (S : Finset (Fin (size n))) : Set ℝ :=
  {t | ∀ i, t ≤ (timeEmbedding n i:ℝ) ↔ i ∈ S}

theorem cell_measurable (n : ℕ) (S : Finset (Fin (size n))) : MeasurableSet (cell n S) := by
  simp only [cell, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  by_cases hi : i ∈ S
  · simp only [hi, iff_true]
    exact measurableSet_le measurable_id measurable_const
  · simp only [hi, iff_false, not_le]
    exact measurableSet_lt measurable_const measurable_id

theorem core_field (n r : ℕ) (P : Test n) (t : ℝ) :
    ((atTime t)^r) (core (cylinderOf n P)) =
      ∑ S : Finset (Fin (size n)), if t ∈ cell n S then
        core (cylinderOf n ((gridDerivative n (fun i => if i ∈ S then 1 else 0))^[r] P)) else 0 := by
  let S : Finset (Fin (size n)) := Finset.univ.filter (fun i => t ≤ (timeEmbedding n i:ℝ))
  have hS : t ∈ cell n S := by intro i; simp [S]
  have hu (U : Finset (Fin (size n))) (hU : t ∈ cell n U) : U = S := by
    ext i
    exact (hU i).symm.trans (hS i)
  rw [Finset.sum_eq_single S]
  · rw [ite_eq_left hS, atTime, operator_pow_core]
    have hw : (fun i => direction t (timeEmbedding n i)) =
        (fun i => if i ∈ S then (1:ℝ) else 0) := by
      funext i
      simp only [direction, hS i]
    rw [hw]
  · intro U _ hne
    exact ite_eq_right (fun hU => hne (hu U hU))
  · intro h
    exact (h (Finset.mem_univ S)).elim

theorem core_stronglyMeasurable (n r : ℕ) (P : Test n) :
    StronglyMeasurable (fun t : ℝ => ((atTime t)^r) (core (cylinderOf n P))) := by
  have hs (S : Finset (Fin (size n))) : StronglyMeasurable (fun t : ℝ =>
      if t ∈ cell n S then
        core (cylinderOf n ((gridDerivative n (fun i => if i ∈ S then 1 else 0))^[r] P)) else 0) :=
    stronglyMeasurable_const.piecewise (cell_measurable n S) stronglyMeasurable_const
  have hh := Finset.stronglyMeasurable_fun_sum Finset.univ (fun S _ => hs S)
  simpa only [← core_field] using hh

theorem stronglyMeasurable_pow (r : ℕ) (u : Domain) :
    StronglyMeasurable (fun t : ℝ => ((atTime t)^r) u) := by
  obtain ⟨g, hg, hlim⟩ := mem_closure_iff_seq_limit.mp (core_dense u)
  choose F hF using hg
  have hf (k : ℕ) : StronglyMeasurable (fun t : ℝ => ((atTime t)^r) (g k)) := by
    rw [← hF k]
    induction F k using DirectLimit.induction with
    | _ n P => exact core_stronglyMeasurable n r P
  apply stronglyMeasurable_of_tendsto atTop hf
  apply tendsto_pi_nhds.mpr
  intro t
  exact ((atTime t)^r).continuous.continuousAt.tendsto.comp hlim

end OperatorDerivativeRewrite.Foundation.HigherHeatTimeDerivative
