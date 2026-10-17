import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas

/-! Countable-range upper approximations of finite nonnegative stopping times.
The construction does not require a right-continuous filtration. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StoppingTimeRounding
set_option backward.isDefEq.respectTransparency false

def rounded (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  (⌈((n : ℝ≥0)+1)*t⌉₊ : ℝ≥0)/((n : ℝ≥0)+1)

def cutoff (n : ℕ) (s : ℝ≥0) : ℝ≥0 :=
  (⌊((n : ℝ≥0)+1)*s⌋₊ : ℝ≥0)/((n : ℝ≥0)+1)

theorem le_rounded (n : ℕ) (t : ℝ≥0) : t ≤ rounded n t := by
  rw [rounded, le_div_iff₀ (by positivity)]
  simpa only [mul_comm] using Nat.le_ceil (((n : ℝ≥0)+1)*t)

theorem rounded_lt (n : ℕ) (t : ℝ≥0) : rounded n t < t+1/((n : ℝ≥0)+1) := by
  rw [rounded, div_lt_iff₀ (by positivity)]
  have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ ((n : ℝ≥0)+1)*t)
  calc
    _ < ((n : ℝ≥0)+1)*t+1 := h
    _ = _ := by field_simp <;> ring

theorem cutoff_le (n : ℕ) (s : ℝ≥0) : cutoff n s ≤ s := by
  rw [cutoff, div_le_iff₀ (by positivity)]
  simpa only [mul_comm] using Nat.floor_le (by positivity : 0 ≤ ((n : ℝ≥0)+1)*s)

theorem rounded_le_iff (n : ℕ) (s t : ℝ≥0) : rounded n t ≤ s ↔ t ≤ cutoff n s := by
  unfold rounded cutoff
  rw [div_le_iff₀ (by positivity), le_div_iff₀ (by positivity)]
  rw [← Nat.le_floor_iff (by positivity : 0 ≤ s*((n : ℝ≥0)+1)), Nat.ceil_le]
  simp only [mul_comm]

theorem rounded_monotone (n : ℕ) : Monotone (rounded n) := by
  intro s t hst
  unfold rounded
  have hc := Nat.ceil_mono (mul_le_mul_of_nonneg_left hst
    (by positivity : 0 ≤ (n : ℝ≥0)+1))
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)

theorem rounded_zero (n : ℕ) : rounded n 0 = 0 := by simp [rounded]

theorem rounded_tendsto (t : ℝ≥0) : Tendsto (fun n => rounded n t) atTop (𝓝 t) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using (tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1/((n : ℝ≥0)+1)) atTop (𝓝 0))))
    (fun n => le_rounded n t) (fun n => (rounded_lt n t).le)

theorem rounded_countable_range {Ω : Type*} (n : ℕ) (τ : Ω → ℝ≥0) :
    (range (fun ω => (rounded n (τ ω) : WithTop ℝ≥0))).Countable := by
  apply (Set.countable_range (fun k : ℕ =>
    (((k : ℝ≥0)/((n : ℝ≥0)+1) : ℝ≥0) : WithTop ℝ≥0))).mono
  rintro _ ⟨ω,rfl⟩
  exact ⟨_,rfl⟩

theorem rounded_bounded (n : ℕ) (t : ℝ≥0) {N : ℕ} (ht : t ≤ N) :
    rounded n t ≤ N := by
  unfold rounded
  rw [div_le_iff₀ (by positivity)]
  have he : (N : ℝ≥0)*((n : ℝ≥0)+1) = (N*(n+1) : ℕ) := by push_cast; ring
  rw [he]
  have hc : ⌈((n : ℝ≥0)+1)*t⌉₊ ≤ N*(n+1) := Nat.ceil_le.mpr (by
    push_cast
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ (n : ℝ≥0)+1))
  exact_mod_cast hc

theorem rounded_isStoppingTime {Ω : Type*} [m : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 m) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) (n : ℕ) :
    IsStoppingTime ℱ (fun ω => (rounded n (τ ω) : WithTop ℝ≥0)) := by
  intro s
  have he : {ω | (rounded n (τ ω) : WithTop ℝ≥0) ≤ s} =
      {ω | (τ ω : WithTop ℝ≥0) ≤ cutoff n s} := by
    ext ω
    simp only [mem_setOf_eq, WithTop.coe_le_coe, rounded_le_iff]
  rw [he]
  exact ℱ.mono (cutoff_le n s) _ (hτ (cutoff n s))

end OperatorDerivativeRewrite.Foundation.StoppingTimeRounding
