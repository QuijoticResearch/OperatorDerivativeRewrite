import Foundation.HigherHeatDyadicDualNodes

/-! Actual dyadic endpoint density in the closed normalized time interval. -/
noncomputable section
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatDyadicTimeDensity
open HigherHeatPolynomialCylinders HigherHeatContinuousCylinders HigherHeatDyadicDualNodes
open HigherHeatDyadicPositionRefinement Filter

abbrev Interval := Set.Icc (0:ℝ) 1

def node (n : ℕ) (o : Option (Fin (size n))) : Interval :=
  ⟨interpolationNode n o, interpolationNode_mem n o⟩

def dyadicSet : Set Interval := {t | ∃ n o, node n o = t}

def prefixNode (n c : ℕ) (hc : c ≤ size n) : Option (Fin (size n)) :=
  if hz : c=0 then none else some ⟨c-1, by omega⟩

theorem prefixNode_time (n c : ℕ) (hc : c ≤ size n) :
    interpolationNode n (prefixNode n c hc) = (c:ℝ)/(size n:ℝ) := by
  by_cases hz : c=0
  · simp [prefixNode, hz, interpolationNode]
  · have hs : c-1+1=c := by omega
    simp only [prefixNode, dite_eq_right hz, interpolationNode, sampleTime_formula]
    change (((c-1)+1:ℕ):ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ) = _
    rw [hs]
    simp only [HigherHeatDyadicLaws.duration, NNReal.coe_div, NNReal.coe_one]
    change (c:ℝ)*(1/(size n:ℝ)) = (c:ℝ)/(size n:ℝ)
    ring

def count (n : ℕ) (t : Interval) : ℕ := ⌊(t:ℝ)*(size n:ℝ)⌋₊

theorem count_le (n : ℕ) (t : Interval) : count n t ≤ size n := by
  have hf := Nat.floor_le (mul_nonneg t.property.1 (Nat.cast_nonneg (size n)))
  have ht := mul_le_mul_of_nonneg_right t.property.2 (Nat.cast_nonneg (size n): (0:ℝ)≤size n)
  have hh : (count n t:ℝ) ≤ (size n:ℝ) := by
    change (⌊(t:ℝ)*(size n:ℝ)⌋₊:ℝ) ≤ _
    exact hf.trans (by simpa only [one_mul] using ht)
  exact_mod_cast hh

def approximation (n : ℕ) (t : Interval) : Interval := node n (prefixNode n (count n t) (count_le n t))

theorem approximation_mem (n : ℕ) (t : Interval) : approximation n t ∈ dyadicSet :=
  ⟨n, prefixNode n (count n t) (count_le n t), rfl⟩

theorem approximation_coe (n : ℕ) (t : Interval) :
    (approximation n t:ℝ) = (⌊(t:ℝ)*(2:ℝ)^n⌋₊:ℝ)/(2:ℝ)^n := by
  change interpolationNode n (prefixNode n (count n t) (count_le n t)) = _
  rw [prefixNode_time]
  have hs : (size n:ℝ) = (2:ℝ)^n := by exact_mod_cast HigherHeatDyadicLaws.gridSize_pow n
  rw [count, hs]

theorem approximation_tendsto (t : Interval) : Tendsto (fun n => approximation n t) atTop (𝓝 t) := by
  apply tendsto_subtype_rng.mpr
  simp only [approximation_coe]
  exact (tendsto_nat_floor_mul_div_atTop t.property.1).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2))

theorem dyadicSet_dense : Dense dyadicSet := by
  intro t
  exact isClosed_closure.mem_of_tendsto (approximation_tendsto t)
    (Eventually.of_forall (fun n => subset_closure (approximation_mem n t)))

end OperatorDerivativeRewrite.Foundation.HigherHeatDyadicTimeDensity
