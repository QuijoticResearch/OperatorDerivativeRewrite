import Foundation.FourierPathLinearDirection
import Foundation.HigherHeatPositionVariation
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Actual dyadic direction increments and their uniform local Lipschitz bound. -/
noncomputable section
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathDyadicDirections
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatCylinderFourier

def increment (h : Path) (N : ℕ) (j : Fin N) : ℝ :=
  h.val ((j.val+1:ℝ)/(N:ℝ))-h.val ((j.val:ℝ)/(N:ℝ))

theorem cumulative_increment (h : Path) (N : ℕ) (i : Fin N) :
    linearImage (cumulativeMatrix N) (increment h N) i=h.val ((i.val+1:ℝ)/(N:ℝ)) := by
  classical
  rw [cumulative_apply]
  have he : Finset.univ.filter (fun j : Fin N => j ≤ i)=Finset.Iic i := by ext j; simp
  rw [he]
  have ht := Fin.sum_Iic_sub i (fun j : Fin (N+1) => h.val ((j.val:ℝ)/(N:ℝ)))
  simpa only [increment, Fin.val_succ, Fin.val_castSucc, Fin.val_zero, Nat.cast_zero,
    Nat.cast_add, Nat.cast_one, zero_div, h.property, sub_zero] using ht

theorem sample_cumulative (h : Path) (n : ℕ) :
    sample n h=linearImage (cumulativeMatrix (gridSize n)) (increment h (gridSize n)) := by
  funext i
  rw [cumulative_increment]
  change h.val (sample n FourierPathLinearDirection.direction i)=_
  rw [FourierPathLinearDirection.sample_direction]

theorem node_mem (N : ℕ) (hN : 0 < N) (k : ℕ) (hk : k ≤ N) :
    (k:ℝ)/(N:ℝ) ∈ Set.Icc (0:ℝ) 1 := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  refine ⟨by positivity, (div_le_one hn).mpr ?_⟩
  exact_mod_cast hk

theorem increment_bound (h : Path) (K : ℝ≥0)
    (hK : LipschitzOnWith K h.val (Set.Icc (0:ℝ) 1)) (N : ℕ) (hN : 0 < N) (j : Fin N) :
    |increment h N j| ≤ (K:ℝ)/(N:ℝ) := by
  have ht := hK.dist_le_mul (((j.val+1:ℕ):ℝ)/(N:ℝ))
    (node_mem N hN _ (Nat.succ_le_of_lt j.isLt)) ((j.val:ℝ)/(N:ℝ))
    (node_mem N hN _ j.isLt.le)
  rw [Real.dist_eq, Real.dist_eq] at ht
  have he : (((j.val+1:ℕ):ℝ)/(N:ℝ))-(j.val:ℝ)/(N:ℝ)=1/(N:ℝ) := by push_cast; ring
  have hn : (0:ℝ) ≤ 1/(N:ℝ) := by positivity
  rw [he, abs_of_nonneg hn] at ht
  simpa only [increment, Nat.cast_add, Nat.cast_one, mul_one_div] using ht

end OperatorDerivativeRewrite.Foundation.FourierPathDyadicDirections
