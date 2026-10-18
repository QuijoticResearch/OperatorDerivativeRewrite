import Foundation.HigherHeatConditionalRefinement
import Foundation.HigherHeatDyadicLaws
import Mathlib.Algebra.Colimit.DirectLimit

/-! An actual algebra of unbounded dyadic polynomial cylinders with compatible signed mean. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.HigherHeatPolynomialCylinders
open HigherHeatPolynomialRefinement HigherHeatMultivariateMoments HigherHeatBlockCoarsening
  HigherHeatGridDoubling

abbrev size := HigherHeatDyadicLaws.gridSize
abbrev Test (n : ℕ) := MvPolynomial (Fin (size n)) ℝ

def step (n : ℕ) : Test n →ₐ[ℝ] Test (n+1) := pullback (@pairBlock (size n))

def transfer (i j : ℕ) (h : i ≤ j) (P : Test i) : Test j :=
  Nat.leRecOn h (@fun k Q => step k Q) P

theorem transfer_self (i : ℕ) (P : Test i) : transfer i i le_rfl P = P := Nat.leRecOn_self P

theorem transfer_succ (i j : ℕ) (h : i ≤ j) (P : Test i) :
    transfer i (j+1) (h.trans (Nat.le_succ j)) P = step j (transfer i j h P) :=
  Nat.leRecOn_succ h P

theorem transfer_add (i j : ℕ) (h : i ≤ j) (P Q : Test i) :
    transfer i j h (P+Q) = transfer i j h P + transfer i j h Q := by
  induction j, h using Nat.le_induction with
  | base => simp only [transfer_self]
  | succ j hj ih => rw [transfer_succ i j hj (P+Q), transfer_succ i j hj P, transfer_succ i j hj Q, ih, map_add]

theorem transfer_mul (i j : ℕ) (h : i ≤ j) (P Q : Test i) :
    transfer i j h (P*Q) = transfer i j h P * transfer i j h Q := by
  induction j, h using Nat.le_induction with
  | base => simp only [transfer_self]
  | succ j hj ih => rw [transfer_succ i j hj (P*Q), transfer_succ i j hj P, transfer_succ i j hj Q, ih, map_mul]

theorem transfer_C (i j : ℕ) (h : i ≤ j) (c : ℝ) :
    transfer i j h (MvPolynomial.C c) = MvPolynomial.C c := by
  induction j, h using Nat.le_induction with
  | base => simp only [transfer_self]
  | succ j hj ih =>
    rw [transfer_succ i j hj (MvPolynomial.C c), ih]
    exact MvPolynomial.algHom_C (step j) c

theorem transfer_zero (i j : ℕ) (h : i ≤ j) : transfer i j h 0 = 0 := by
  simpa using transfer_C i j h 0

theorem transfer_one (i j : ℕ) (h : i ≤ j) : transfer i j h 1 = 1 := by
  simpa using transfer_C i j h 1

def transition (i j : ℕ) (h : i ≤ j) : Test i →ₐ[ℝ] Test j where
  toFun := transfer i j h
  map_one' := transfer_one i j h
  map_mul' := transfer_mul i j h
  map_zero' := transfer_zero i j h
  map_add' := transfer_add i j h
  commutes' := transfer_C i j h

instance transition_system : DirectedSystem Test (fun i j h => transition i j h) where
  map_self i P := transfer_self i P
  map_map _ _ _ hij hjk P := (Nat.leRecOn_trans hij hjk P).symm

theorem transfer_injective (i j : ℕ) (h : i ≤ j) : Function.Injective (transfer i j h) := by
  induction j, h using Nat.le_induction with
  | base => intro P Q hPQ; simpa only [transfer_self] using hPQ
  | succ j hj ih =>
    intro P Q hPQ
    rw [transfer_succ i j hj P, transfer_succ i j hj Q] at hPQ
    exact ih (pullback_injective pairBlock (pairBlock_surjective _) hPQ)

abbrev Cylinder := DirectLimit Test transition

def cylinderOf (n : ℕ) : Test n →ₐ[ℝ] Cylinder := DirectLimit.Algebra.of Test transition n

theorem cylinderOf_injective (n : ℕ) : Function.Injective (cylinderOf n) :=
  DirectLimit.mk_injective transition transfer_injective n

theorem cylinder_refinement (i j : ℕ) (h : i ≤ j) (P : Test i) :
    cylinderOf j (transfer i j h P) = cylinderOf i P := DirectLimit.Algebra.of_f h P

def expectation (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) : Test n →ₗ[ℝ] ℂ :=
  mean m hm (fun _ => HigherHeatDyadicLaws.duration T n)
    (fun _ => HigherHeatDyadicLaws.duration_pos T hT n)

theorem expectation_step (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (P : Test n) :
    expectation m hm T hT (n+1) (step n P) = expectation m hm T hT n P := by
  have he := actual_mean_pullback m hm
    (fun _ : Fin (2*size n) => HigherHeatDyadicLaws.duration T (n+1))
    (fun _ => HigherHeatDyadicLaws.duration_pos T hT (n+1))
    pairBlock (pairBlock_surjective (size n)) P
  have hs : blockTimes pairBlock
      (fun _ : Fin (2*size n) => HigherHeatDyadicLaws.duration T (n+1)) =
      (fun _ : Fin (size n) => HigherHeatDyadicLaws.duration T n) := by
    funext i
    rw [pair_times, HigherHeatDyadicLaws.duration_halves]
  change mean m hm (fun _ : Fin (2*size n) => HigherHeatDyadicLaws.duration T (n+1))
      (fun _ => HigherHeatDyadicLaws.duration_pos T hT (n+1)) (pullback pairBlock P) =
    mean m hm (fun _ : Fin (size n) => HigherHeatDyadicLaws.duration T n)
      (fun _ => HigherHeatDyadicLaws.duration_pos T hT n) P
  simpa only [hs] using he

theorem expectation_transfer (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (i j : ℕ) (h : i ≤ j) (P : Test i) :
    expectation m hm T hT j (transfer i j h P) = expectation m hm T hT i P := by
  induction j, h using Nat.le_induction with
  | base => rw [transfer_self]
  | succ j hj ih => rw [transfer_succ i j hj P, expectation_step, ih]

def cylindricalExpectation (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) : Cylinder →ₗ[ℝ] ℂ :=
  DirectLimit.Module.lift ℝ ℕ Test transition (fun n => expectation m hm T hT n)
    (fun i j h P => expectation_transfer m hm T hT i j h P)

theorem cylindricalExpectation_apply (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (P : Test n) :
    cylindricalExpectation m hm T hT (cylinderOf n P) = expectation m hm T hT n P := rfl

theorem cylindricalExpectation_one (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    cylindricalExpectation m hm T hT 1 = 1 := by
  rw [← map_one (cylinderOf 0), cylindricalExpectation_apply]
  change mean m hm _ _ (MvPolynomial.C 1) = 1
  rw [mean_C]
  rfl


def terminalCylinder : Cylinder := cylinderOf 0 (terminal : Test 0)

theorem terminal_moments (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (r : ℕ) :
    cylindricalExpectation m hm T hT (terminalCylinder^r) =
      (PseudoPolynomialStein.moment (2*m) ((-1:ℝ)^(m+1)*(T:ℝ)) r : ℂ) := by
  rw [terminalCylinder, ← map_pow (cylinderOf 0), cylindricalExpectation_apply]
  have hs : (∑ _ : Fin (size 0), HigherHeatDyadicLaws.duration T 0) = T := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp [size, HigherHeatDyadicLaws.gridSize, HigherHeatDyadicLaws.duration]
  have htpos : 0 < ∑ _ : Fin (size 0), HigherHeatDyadicLaws.duration T 0 := by
    rw [hs]
    exact hT
  change mean m hm (fun _ : Fin (size 0) => HigherHeatDyadicLaws.duration T 0)
    (fun _ => HigherHeatDyadicLaws.duration_pos T hT 0) ((terminal : Test 0)^r) = _
  rw [HigherHeatMultivariateMoments.terminal_moment m hm _ _ htpos r, hs]

theorem biharmonic_fourth (T : ℝ≥0) (hT : 0 < T) :
    cylindricalExpectation 2 (by norm_num) T hT (terminalCylinder^4) = -24*((T:ℝ):ℂ) := by
  rw [terminal_moments]
  norm_num [PseudoPolynomialStein.moment]
  ring


end OperatorDerivativeRewrite.Foundation.HigherHeatPolynomialCylinders
