import Foundation.HigherHeatUniformQuarticVariation

/-! Exact left-point quadratic defect under genuine finite signed biharmonic laws. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BiharmonicLeftSumObstruction
open HigherHeatPowerVariation HigherHeatUniformQuarticVariation

def partialSum (z : ℕ → ℂ) (n : ℕ) : ℂ := ∑ k ∈ Finset.range n, z k

def leftSum (z : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range n, 2 * partialSum z k * z k

theorem discrete_square (z : ℕ → ℂ) (n : ℕ) :
    partialSum z n ^ 2 - leftSum z n = ∑ k ∈ Finset.range n, z k ^ 2 := by
  induction n with
  | zero => simp [partialSum, leftSum]
  | succ n ih =>
    simp only [partialSum, leftSum, Finset.sum_range_succ] at ih ⊢
    change (partialSum z n + z n)^2 - (leftSum z n + 2*partialSum z n*z n) = _
    dsimp only [partialSum, leftSum]
    linear_combination ih

def lift {N : ℕ} (x : Fin N → ℝ) (k : ℕ) : ℂ :=
  if h : k < N then (x ⟨k,h⟩ : ℂ) else 0

def defect {N : ℕ} (x : Fin N → ℝ) : ℂ :=
  partialSum (lift x) N ^ 2 - leftSum (lift x) N

theorem defect_eq {N : ℕ} (x : Fin N → ℝ) : defect x = powerSum 2 x := by
  rw [defect, discrete_square]
  have he := Fin.sum_univ_eq_sum_range (fun k => lift x k ^ 2) N
  simpa only [lift, Fin.is_lt, dite_eq_left, powerSum] using he.symm

theorem defect_square_integrable (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    (law T hT n).Integrable (fun x => defect x ^ 2) := by
  simp_rw [defect_eq]
  exact HigherHeatQuarticVariation.square_sum_integrable
    (fun _ : Fin (n+1) => duration T n) (fun _ => duration_pos T hT n) 2

theorem defect_second_moment (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    (∫ᵛ x, defect x ^ 2 ∂<•law T hT n) = -24 * ((T:ℝ):ℂ) := by
  simp_rw [defect_eq]
  exact quadratic_second_moment T hT n

theorem defect_not_tendsto_zero (T : ℝ≥0) (hT : 0 < T) :
    ¬ Tendsto (fun n => ∫ᵛ x, defect x ^ 2 ∂<•law T hT n) atTop (𝓝 0) := by
  simp_rw [defect_second_moment]
  intro h
  have he := tendsto_nhds_unique h tendsto_const_nhds
  have hn : (-24:ℂ) * ((T:ℝ):ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (ne_of_gt hT))
  exact hn he.symm

end OperatorDerivativeRewrite.Foundation.BiharmonicLeftSumObstruction
