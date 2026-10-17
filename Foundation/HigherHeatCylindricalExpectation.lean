import Foundation.HigherHeatDyadicLaws
import Mathlib.Algebra.Colimit.DirectLimit

/-! A representation-independent normalized cylindrical expectation for higher heat on dyadic grids. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.HigherHeatCylindricalExpectation
open HigherHeatDyadicLaws

def transfer (i j : ℕ) (h : i ≤ j) (f : Test i) : Test j :=
  Nat.leRecOn h (@fun k g => pullback k g) f

theorem transfer_self (i : ℕ) (f : Test i) : transfer i i le_rfl f=f := Nat.leRecOn_self f

theorem transfer_succ (i j : ℕ) (h : i ≤ j) (f : Test i) :
    transfer i (j+1) (h.trans (Nat.le_succ j)) f=pullback j (transfer i j h f) :=
  Nat.leRecOn_succ h f

theorem transfer_add (i j : ℕ) (h : i ≤ j) (f g : Test i) :
    transfer i j h (f+g)=transfer i j h f+transfer i j h g := by
  induction j, h using Nat.le_induction with
  | base => simp only [transfer_self]
  | succ j hj ih =>
    rw [transfer_succ i j hj (f+g),transfer_succ i j hj f,transfer_succ i j hj g,ih,map_add]

theorem transfer_smul (i j : ℕ) (h : i ≤ j) (c : ℝ) (f : Test i) :
    transfer i j h (c • f)=c • transfer i j h f := by
  induction j, h using Nat.le_induction with
  | base => simp only [transfer_self]
  | succ j hj ih =>
    rw [transfer_succ i j hj (c • f),transfer_succ i j hj f,ih,map_smul]

def transition (i j : ℕ) (h : i ≤ j) : Test i →ₗ[ℝ] Test j where
  toFun := transfer i j h
  map_add' := transfer_add i j h
  map_smul' := transfer_smul i j h

instance transition_system : DirectedSystem Test (fun i j h => transition i j h) where
  map_self i f := transfer_self i f
  map_map _ _ _ hij hjk f := (Nat.leRecOn_trans hij hjk f).symm

theorem transfer_injective (i j : ℕ) (h : i ≤ j) : Function.Injective (transfer i j h) := by
  induction j, h using Nat.le_induction with
  | base => intro f g hfg; simpa only [transfer_self] using hfg
  | succ j hj ih =>
    intro f g hfg
    rw [transfer_succ i j hj f,transfer_succ i j hj g] at hfg
    exact ih (pullback_injective j hfg)

abbrev Cylinder := DirectLimit Test transition

def cylinderOf (n : ℕ) : Test n →ₗ[ℝ] Cylinder := DirectLimit.Module.of ℝ ℕ Test transition n

theorem cylinderOf_injective (n : ℕ) : Function.Injective (cylinderOf n) :=
  DirectLimit.mk_injective transition transfer_injective n

theorem cylinder_refinement (i j : ℕ) (h : i ≤ j) (f : Test i) :
    cylinderOf j (transfer i j h f)=cylinderOf i f := DirectLimit.Module.of_f

theorem expectation_transfer (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (i j : ℕ) (h : i ≤ j) (f : Test i) :
    expectation m hm T hT j (transfer i j h f)=expectation m hm T hT i f := by
  induction j, h using Nat.le_induction with
  | base => rw [transfer_self]
  | succ j hj ih =>
    rw [transfer_succ i j hj f,expectation_compatible,ih]

def cylindricalExpectation (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) : Cylinder →ₗ[ℝ] ℝ :=
  DirectLimit.Module.lift ℝ ℕ Test transition (fun n => expectation m hm T hT n)
    (fun i j h f => expectation_transfer m hm T hT i j h f)

theorem cylindricalExpectation_apply (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (f : Test n) : cylindricalExpectation m hm T hT (cylinderOf n f)=expectation m hm T hT n f := rfl

def unitCylinder : Cylinder := cylinderOf 0 (1 : Test 0)

theorem cylindricalExpectation_normalized (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    cylindricalExpectation m hm T hT unitCylinder=1 := expectation_one m hm T hT 0

end OperatorDerivativeRewrite.Foundation.HigherHeatCylindricalExpectation
