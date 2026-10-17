import Foundation.HigherHeatCylindricalOperator
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Topology.Algebra.Polynomial

/-! Faithful realization of dyadic cylinder tests on actual continuous paths starting at zero. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.HigherHeatContinuousCylinders
open HigherHeatDyadicLaws HigherHeatGridDoubling HigherHeatCylindricalExpectation

abbrev Path := {ω : C(ℝ,ℝ) // ω 0=0}

def coordinate (t : ℝ) (ω : Path) : ℝ := ω.val t

theorem coordinate_continuous (t : ℝ) : Continuous (coordinate t) :=
  (continuous_eval_const t).comp continuous_subtype_val

def sampleTime (n : ℕ) (i : Fin (gridSize n)) : ℝ := HigherHeatDyadicLaws.time 1 n i

theorem sampleTime_pos (n : ℕ) (i : Fin (gridSize n)) : 0 < sampleTime n i := by
  exact_mod_cast time_positive 1 (by norm_num) n i

theorem sampleTime_injective (n : ℕ) : Function.Injective (sampleTime n) := by
  intro i j h
  have hd : 0 < (duration 1 n : ℝ) := by exact_mod_cast duration_pos 1 (by norm_num) n
  have he : ((i.val : ℝ)+1)*(duration 1 n : ℝ)=((j.val : ℝ)+1)*(duration 1 n : ℝ) := by
    simpa [sampleTime,HigherHeatDyadicLaws.time] using h
  have hv : (i.val : ℝ)=(j.val : ℝ) := by nlinarith
  apply Fin.ext
  exact_mod_cast hv

def interpolationNode (n : ℕ) : Option (Fin (gridSize n)) → ℝ
  | none => 0
  | some i => sampleTime n i

theorem interpolationNode_injective (n : ℕ) : Function.Injective (interpolationNode n) := by
  intro i j h
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j => exact False.elim ((sampleTime_pos n j).ne' h.symm)
  | some i =>
    cases j with
    | none => exact False.elim ((sampleTime_pos n i).ne' h)
    | some j => exact congrArg some (sampleTime_injective n h)

def sample (n : ℕ) (ω : Path) : Grid n := fun i => coordinate (sampleTime n i) ω

theorem sample_continuous (n : ℕ) : Continuous (sample n) := by
  apply continuous_pi
  intro i
  exact coordinate_continuous _

theorem sample_surjective (n : ℕ) : Function.Surjective (sample n) := by
  classical
  intro y
  let v : Option (Fin (gridSize n)) → ℝ := fun o => o.elim 0 y
  let p : Polynomial ℝ := Lagrange.interpolate Finset.univ (interpolationNode n) v
  have h0 : p.eval 0=0 :=
    Lagrange.eval_interpolate_at_node v (interpolationNode_injective n).injOn
      (Finset.mem_univ (none : Option (Fin (gridSize n))))
  let ω : Path := ⟨⟨fun t => p.eval t,p.continuous⟩,h0⟩
  refine ⟨ω,?_⟩
  funext i
  exact Lagrange.eval_interpolate_at_node v (interpolationNode_injective n).injOn
    (Finset.mem_univ (some i))

theorem sample_restriction (n : ℕ) (ω : Path) : restriction n (sample (n+1) ω)=sample n ω := by
  funext i
  change coordinate (sampleTime (n+1) (oddIndex i)) ω=coordinate (sampleTime n i) ω
  congr 1
  change (HigherHeatDyadicLaws.time 1 (n+1) (oddIndex i) : ℝ)=(HigherHeatDyadicLaws.time 1 n i : ℝ)
  exact_mod_cast time_restriction 1 n i

def sampleLift (n : ℕ) : Test n →L[ℝ] (Path →ᵇ ℝ) :=
  BoundedContinuousFunction.compContinuousCLM ℝ ℝ ⟨sample n,sample_continuous n⟩

theorem sampleLift_apply (n : ℕ) (f : Test n) (ω : Path) : sampleLift n f ω=f (sample n ω) := rfl

theorem sampleLift_injective (n : ℕ) : Function.Injective (sampleLift n) := by
  intro f g h
  ext x
  obtain ⟨ω,hω⟩ := sample_surjective n x
  have he := congrArg (fun F : Path →ᵇ ℝ => F ω) h
  change f (sample n ω)=g (sample n ω) at he
  rwa [hω] at he

theorem sampleLift_step (n : ℕ) (f : Test n) : sampleLift (n+1) (pullback n f)=sampleLift n f := by
  ext ω
  change f (restriction n (sample (n+1) ω))=f (sample n ω)
  rw [sample_restriction]

theorem sampleLift_transfer (i j : ℕ) (h : i ≤ j) (f : Test i) :
    sampleLift j (transfer i j h f)=sampleLift i f := by
  induction j, h using Nat.le_induction with
  | base => rw [transfer_self]
  | succ j hj ih => rw [transfer_succ i j hj f,sampleLift_step,ih]

def realize : Cylinder →ₗ[ℝ] (Path →ᵇ ℝ) :=
  DirectLimit.Module.lift ℝ ℕ Test transition (fun n => (sampleLift n).toLinearMap)
    (fun i j h f => sampleLift_transfer i j h f)

theorem realize_apply (n : ℕ) (f : Test n) (ω : Path) : realize (cylinderOf n f) ω=f (sample n ω) := rfl

theorem realize_injective : Function.Injective realize :=
  DirectLimit.lift_injective transition (fun n f => sampleLift n f)
    (fun i j h f => (sampleLift_transfer i j h f).symm) sampleLift_injective

def realizedSpace : Submodule ℝ (Path →ᵇ ℝ) := LinearMap.range realize

def realizationEquiv : Cylinder ≃ₗ[ℝ] realizedSpace := LinearEquiv.ofInjective realize realize_injective

def pathExpectation (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) : realizedSpace →ₗ[ℝ] ℝ :=
  (cylindricalExpectation m hm T hT).comp realizationEquiv.symm.toLinearMap

theorem pathExpectation_apply (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (c : Cylinder) :
    pathExpectation m hm T hT (realizationEquiv c)=cylindricalExpectation m hm T hT c := by
  simp [pathExpectation]

theorem coordinate_zero (ω : Path) : coordinate 0 ω=0 := ω.property

theorem coordinate_path_continuous (ω : Path) : Continuous (fun t : ℝ => coordinate t ω) :=
  ω.val.continuous

theorem coordinate_jointly_continuous : Continuous (fun p : ℝ × Path => coordinate p.1 p.2) := by
  exact continuous_eval.comp ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)

theorem coordinate_jointly_measurable : Measurable (fun p : ℝ × Path => coordinate p.1 p.2) :=
  coordinate_jointly_continuous.measurable

end OperatorDerivativeRewrite.Foundation.HigherHeatContinuousCylinders
