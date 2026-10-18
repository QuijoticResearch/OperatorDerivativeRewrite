import Foundation.HigherHeatDyadicStepAgreement
import Mathlib.Algebra.MvPolynomial.Monad

/-! Refinement of actual L1 stochastic coefficient fields, preserving adapted support. -/
noncomputable section
open scoped NNReal ENNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatStepRefinement
open MeasureTheory HigherHeatPolynomialCylinders HigherHeatGridDoubling
open HigherHeatPolynomialRefinement HigherHeatDyadicStepAgreement
open HigherHeatWeakTimeAdjoint HigherHeatWeakStepFields HigherHeatCompletedPairing
open HigherHeatAnalyticCylinderDomain

theorem blockVariable_vars {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → κ) (i : κ) {k : ι} (hk : k ∈ (blockVariable p i).vars) : p k = i := by
  classical
  obtain ⟨l, hl, hkl⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_sum_subset _ _ hk)
  have he : k = l := by simpa only [MvPolynomial.vars_X, Finset.mem_singleton] using hkl
  subst l
  exact (Finset.mem_filter.mp hl).2

theorem pullback_vars {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] (p : ι → κ) (F : MvPolynomial κ ℝ) {k : ι}
    (hk : k ∈ (pullback p F).vars) : p k ∈ F.vars := by
  have hb : k ∈ (MvPolynomial.bind₁ (blockVariable p) F).vars := hk
  obtain ⟨i, hi, hki⟩ := MvPolynomial.mem_vars_bind₁ _ _ hb
  exact (blockVariable_vars p i hki) ▸ hi

theorem step_missing (n : ℕ) (j : Fin (size n)) (F : Test n) (hF : j ∉ F.vars)
    (k : Fin (size (n+1))) (hk : pairBlock k = j) :
    k ∉ (HigherHeatPolynomialCylinders.step n F).vars := by
  intro h
  exact hF (hk ▸ pullback_vars pairBlock F h)

theorem cylinder_step (n : ℕ) (F : Test n) :
    cylinderOf (n+1) (HigherHeatPolynomialCylinders.step n F) = cylinderOf n F := by
  have h := cylinder_refinement n (n+1) (Nat.le_succ n) F
  have ht := transfer_succ n n le_rfl F
  simp only [transfer_self] at ht
  rw [ht] at h
  exact h

theorem pair_pullback_X {N : ℕ} (j : Fin N) :
    pullback (@pairBlock N) (MvPolynomial.X j : MvPolynomial (Fin N) ℝ) =
      (MvPolynomial.X (evenIndex j) + MvPolynomial.X (oddIndex j) :
        MvPolynomial (Fin (2*N)) ℝ) := by
  classical
  rw [pullback, MvPolynomial.aeval_X, blockVariable]
  rw [Finset.filter_congr_decidable]
  exact (congrArg (fun S : Finset (Fin (2*N)) =>
    ∑ k ∈ S, (MvPolynomial.X k : MvPolynomial (Fin (2*N)) ℝ)) (pair_fiber j)).trans
      (Finset.sum_pair (even_ne_odd j))

theorem step_X (n : ℕ) (j : Fin (size n)) :
    HigherHeatPolynomialCylinders.step n (MvPolynomial.X j) =
      (MvPolynomial.X (evenIndex j) : Test (n+1)) +
        (MvPolynomial.X (oddIndex j) : Test (n+1)) := pair_pullback_X j

theorem gridCell_split (n : ℕ) (j : Fin (size n)) :
    gridCell n j = gridCell (n+1) (evenIndex j) ∪ gridCell (n+1) (oddIndex j) := by
  have hd : (HigherHeatDyadicLaws.duration 1 n:ℝ) =
      (HigherHeatDyadicLaws.duration 1 (n+1):ℝ) + (HigherHeatDyadicLaws.duration 1 (n+1):ℝ) := by
    exact_mod_cast (HigherHeatDyadicLaws.duration_halves 1 n).symm
  have hn := (HigherHeatDyadicLaws.duration 1 (n+1)).coe_nonneg
  ext t
  simp only [gridCell, Set.mem_union, Set.mem_Ioc, evenIndex, oddIndex, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, hd]
  constructor
  · intro ht
    by_cases hmid : t ≤ (2*(j.val:ℝ)+1)*(HigherHeatDyadicLaws.duration 1 (n+1):ℝ)
    · left; constructor <;> nlinarith only [ht.1, hmid]
    · right; constructor <;> nlinarith only [ht.2, lt_of_not_ge hmid]
  · rintro (ht | ht) <;> constructor <;> nlinarith only [ht.1, ht.2, hn]

theorem gridCell_children_disjoint (n : ℕ) (j : Fin (size n)) :
    Disjoint (gridCell (n+1) (evenIndex j)) (gridCell (n+1) (oddIndex j)) := by
  apply Set.disjoint_left.mpr
  intro t h₁ h₂
  have he : ((evenIndex j).val:ℝ)+1 = ((oddIndex j).val:ℝ) := by simp [evenIndex, oddIndex]
  exact (not_lt_of_ge (he ▸ h₁.2)) h₂.1

theorem coefficientField_split (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (j : Fin (size n)) (F : Test n) :
    coefficientField n m hm T hT j F =
      coefficientField (n+1) m hm T hT (evenIndex j) (HigherHeatPolynomialCylinders.step n F) +
      coefficientField (n+1) m hm T hT (oddIndex j) (HigherHeatPolynomialCylinders.step n F) := by
  unfold coefficientField HigherHeatWeakStepFields.step
  simp only [cylinder_step]
  have h := indicatorConstLp_disjoint_union (p := 1) (μ := timeMeasure)
    (gridCell_measurable (n+1) (evenIndex j)) (gridCell_measurable (n+1) (oddIndex j))
    (gridCell_finite (n+1) (evenIndex j)) (gridCell_finite (n+1) (oddIndex j))
    (gridCell_children_disjoint n j) (pairing m hm T hT (core (cylinderOf n F)))
  simpa only [← gridCell_split] using h

theorem stochastic_polynomial_split (n : ℕ) (j : Fin (size n)) (F : Test n) :
    cylinderOf n (F * MvPolynomial.X j) =
      cylinderOf (n+1) ((HigherHeatPolynomialCylinders.step n F) * MvPolynomial.X (evenIndex j)) +
      cylinderOf (n+1) ((HigherHeatPolynomialCylinders.step n F) * MvPolynomial.X (oddIndex j)) := by
  rw [← cylinder_step n (F * MvPolynomial.X j), map_mul, step_X, mul_add, map_add]
  rfl

end OperatorDerivativeRewrite.Foundation.HigherHeatStepRefinement
