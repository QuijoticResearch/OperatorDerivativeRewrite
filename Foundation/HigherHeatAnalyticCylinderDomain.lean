import Foundation.HigherHeatPolynomialCoordinates
import Mathlib.Analysis.Normed.Module.Seminorm.Norm
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Normed.Module.Completion

/-! Common analytic cylinder domains and their precise time-topology boundary. -/
noncomputable section
open scoped BigOperators NNReal ENNReal Topology

namespace OperatorDerivativeRewrite.Foundation.HigherHeatAnalyticCylinderDomain
open HigherHeatPolynomialCylinders HigherHeatPolynomialCoordinates
open MultivariateFactorialDomain MultivariateFactorialRenaming

abbrev Time := Set.Ioc (0 : ℝ) 1
abbrev Ambient := H Time

def timeEmbedding (n : ℕ) : Fin (size n) ↪ Time where
  toFun i := ⟨HigherHeatContinuousCylinders.sampleTime n i,
    HigherHeatContinuousCylinders.sampleTime_pos n i,
    by exact_mod_cast HigherHeatDyadicLaws.time_in_horizon 1 n i⟩
  inj' := by
    intro i j he
    have hh : HigherHeatContinuousCylinders.sampleTime n i =
        HigherHeatContinuousCylinders.sampleTime n j := congrArg (fun t : Time => (t : ℝ)) he
    exact HigherHeatContinuousCylinders.sampleTime_injective n hh

theorem timeEmbedding_step (n : ℕ) :
    (oldEmbedding n).trans (timeEmbedding (n+1)) = timeEmbedding n := by
  apply Function.Embedding.ext
  intro i
  apply Subtype.ext
  change (HigherHeatDyadicLaws.time 1 (n+1) (HigherHeatGridDoubling.oddIndex i) : ℝ) =
    (HigherHeatDyadicLaws.time 1 n i : ℝ)
  exact_mod_cast HigherHeatDyadicLaws.time_restriction 1 n i

open Classical in
def gridEmbedding (n : ℕ) : Test n →ₗ[ℝ] Ambient :=
  (renameOperator (timeEmbedding n)).toLinearMap.comp (encode n)

theorem gridEmbedding_apply (n : ℕ) (P : Test n) :
    gridEmbedding n P = renameOperator (timeEmbedding n) (encode n P) := rfl

theorem gridEmbedding_norm (n : ℕ) (P : Test n) : ‖gridEmbedding n P‖ = ‖encode n P‖ := by
  classical
  rw [gridEmbedding_apply]
  exact renaming_norm _ _

theorem gridEmbedding_injective (n : ℕ) : Function.Injective (gridEmbedding n) := by
  classical
  exact (isometricRenaming (timeEmbedding n)).injective.comp (encode_injective n)

theorem gridEmbedding_step (n : ℕ) (P : Test n) : gridEmbedding (n+1) (step n P) = gridEmbedding n P := by
  classical
  rw [gridEmbedding_apply, encode_step, gridEmbedding_apply]
  have he := DFunLike.congr_fun (renaming_comp (oldEmbedding n) (timeEmbedding (n+1)))
    (encode n P)
  change renameOperator (timeEmbedding (n+1))
    (renameOperator (oldEmbedding n) (encode n P)) = _
  exact he.trans (congrArg (fun e => renameOperator e (encode n P)) (timeEmbedding_step n))

theorem gridEmbedding_transfer (i j : ℕ) (h : i ≤ j) (P : Test i) :
    gridEmbedding j (transfer i j h P) = gridEmbedding i P := by
  induction j, h using Nat.le_induction with
  | base => rw [transfer_self]
  | succ j hj ih => rw [transfer_succ i j hj P, gridEmbedding_step, ih]

def embedding : Cylinder →ₗ[ℝ] Ambient :=
  DirectLimit.Module.lift ℝ ℕ Test transition gridEmbedding
    (fun i j h P => gridEmbedding_transfer i j h P)

theorem embedding_apply (n : ℕ) (P : Test n) : embedding (cylinderOf n P) = gridEmbedding n P := rfl

theorem embedding_injective : Function.Injective embedding :=
  DirectLimit.lift_injective transition (fun n P => gridEmbedding n P)
    (fun i j h P => (gridEmbedding_transfer i j h P).symm) gridEmbedding_injective

def cylinderSeminorm : Seminorm ℝ Cylinder := (normSeminorm ℝ Ambient).comp embedding

theorem cylinderSeminorm_apply (F : Cylinder) : cylinderSeminorm F = ‖embedding F‖ := rfl

theorem cylinderSeminorm_zero_iff (F : Cylinder) : cylinderSeminorm F = 0 ↔ F = 0 := by
  rw [cylinderSeminorm_apply, norm_eq_zero]
  exact embedding_injective.eq_iff' embedding.map_zero

theorem cylinderSeminorm_grid (n : ℕ) (P : Test n) :
    cylinderSeminorm (cylinderOf n P) = ‖encode n P‖ := by
  rw [cylinderSeminorm_apply, embedding_apply, gridEmbedding_norm]

def commonClosure : Submodule ℝ Ambient := embedding.range.topologicalClosure

theorem commonClosure_closed : IsClosed (commonClosure : Set Ambient) :=
  embedding.range.isClosed_topologicalClosure

abbrev Domain := commonClosure

instance domain_complete : CompleteSpace Domain :=
  completeSpace_coe_iff_isComplete.mpr commonClosure_closed.isComplete

def core : Cylinder →ₗ[ℝ] Domain := embedding.codRestrict commonClosure
  (fun F => embedding.range.le_topologicalClosure ⟨F, rfl⟩)

theorem core_injective : Function.Injective core := by
  intro F G he
  exact embedding_injective (congrArg Subtype.val he)

theorem core_norm (F : Cylinder) : ‖core F‖ = cylinderSeminorm F := rfl

theorem core_dense : DenseRange core := by
  change DenseRange (Set.inclusion (s := Set.range embedding)
    (t := closure (Set.range embedding)) subset_closure ∘ Set.rangeFactorization embedding)
  exact ((denseRange_inclusion_iff subset_closure).2 subset_rfl).comp
    Set.rangeFactorization_surjective.denseRange (continuous_inclusion subset_closure)

end OperatorDerivativeRewrite.Foundation.HigherHeatAnalyticCylinderDomain
