import Foundation.IBMUniformClockMaximum
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! A genuine in-probability limit for the weighted traversal occupation energy
of the existing reflected Brownian clock, combining envelope decay and maximum
increment tails. This is not yet the product-space quartic fluctuation limit. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMUniformClockOccupation
open InfiniteGaussian IBMUniformClockGridEnergy IBMUniformClockMaximum
open IBMClockTraversalEnvelope IBMQuarticOccupationEnergy
attribute [local irreducible] IBMConstructedSources.clockPath

def occupation (T : ℝ≥0) (n : ℕ) (ω : SampleSpace) : ℝ :=
  ∫ x, count (Finset.range n)
    (fun k => |IBMConstructedSources.clockPath ω (grid (T / n) k)|)
    (fun k => |IBMConstructedSources.clockPath ω (grid (T / n) (k + 1))|) x ^ 2

theorem occupation_nonneg (T : ℝ≥0) (n : ℕ) (ω : SampleSpace) :
    0 ≤ occupation T n ω := integral_nonneg fun _ => sq_nonneg _

theorem occupation_measurable (T : ℝ≥0) (n : ℕ) : Measurable (occupation T n) := by
  have hm (k : ℕ) : Measurable (fun ω => |IBMConstructedSources.clockPath ω (grid (T / n) k)|) :=
    continuous_abs.measurable.comp
      ((ContinuousMap.measurable_eval _).comp IBMConstructedSources.clockPath_measurable)
  unfold occupation
  simp_rw [count_square_mass, abs_overlap]
  apply Finset.measurable_sum
  intro i hi
  apply Finset.measurable_sum
  intro j hj
  exact ((((hm i).max (hm (i + 1))).min ((hm j).max (hm (j + 1)))).sub
    (((hm i).min (hm (i + 1))).max ((hm j).min (hm (j + 1))))).max measurable_const

theorem occupation_le_envelope (T : ℝ≥0) (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    {ω : SampleSpace} (hω : ω ∉ bad T n δ) :
    occupation T n ω ≤ energy (Finset.range n) (grid (T / n)) δ ω := by
  rw [occupation, count_square_mass]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  exact overlap_le_tent hδ
    (reflected_mesh_of_not_bad T n δ hω ⟨i, Finset.mem_range.mp hi⟩)
    (reflected_mesh_of_not_bad T n δ hω ⟨j, Finset.mem_range.mp hj⟩)

/-- Every large weighted traversal energy occurs either on the bad-clock
event or on a large integrable endpoint envelope. -/
theorem weighted_occupation_tail_le (T : ℝ≥0) (n : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) :
    gaussianProduct.real {ω | ε ≤ δ ^ 3 * occupation T n ω} ≤
      gaussianProduct.real (bad T n δ) +
        (∫ ω, δ ^ 3 * energy (Finset.range n) (grid (T / n)) δ ω ∂gaussianProduct) / ε := by
  let E := fun ω => δ ^ 3 * energy (Finset.range n) (grid (T / n)) δ ω
  have hn (ω : SampleSpace) : 0 ≤ E ω := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => tent_nonneg _ _
  have hi : Integrable E gaussianProduct :=
    (energy_integrable (Finset.range n) (grid (T / n)) hδ.le).const_mul _
  have hm : gaussianProduct.real {ω | ε ≤ E ω} ≤ (∫ ω, E ω ∂gaussianProduct) / ε := by
    apply (le_div_iff₀ hε).mpr
    rw [mul_comm]
    exact mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hn) hi ε
  have hs : {ω | ε ≤ δ ^ 3 * occupation T n ω} ⊆ bad T n δ ∪ {ω | ε ≤ E ω} := by
    intro ω h
    by_cases hw : ω ∈ bad T n δ
    · exact Or.inl hw
    · exact Or.inr (h.trans (mul_le_mul_of_nonneg_left
        (occupation_le_envelope T n hδ.le hw) (by positivity)))
  exact ((measureReal_mono hs (by finiteness)).trans (measureReal_union_le _ _)).trans
    (add_le_add le_rfl hm)

attribute [local irreducible] occupation IBMClockTraversalEnvelope.energy IBMUniformClockMaximum.bad

/-- Explicit probability tails of the ACTUAL traversal energy vanish, not just
those of a dominating endpoint functional. -/
theorem weighted_occupation_tail_tendsto {T : ℝ≥0} (hT : 0 < T)
    {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto (fun n : ℕ => gaussianProduct.real {ω |
      ε ≤ ((n + 1 : ℝ) ^ (-(4/9 : ℝ))) ^ 3 * occupation T (n + 1) ω})
      Filter.atTop (nhds 0) := by
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun n =>
    weighted_occupation_tail_le T (n + 1)
      (δ := (n + 1 : ℝ) ^ (-(4/9 : ℝ)))
      (Real.rpow_pos_of_pos (by positivity : 0 < (n + 1 : ℝ)) (-(4/9 : ℝ))) hε)
  simpa only [Nat.cast_add, Nat.cast_one, zero_div, add_zero] using
    (bad_probability_tendsto T).add ((actual_weighted_energy_tendsto hT).div_const ε)

/-- The weighted traversal energy of the genuine reflected Brownian clock
converges to zero in probability along ALL uniform-grid sizes. -/
theorem weighted_occupation_tendstoInMeasure {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure gaussianProduct
      (fun n : ℕ => fun ω => ((n + 1 : ℝ) ^ (-(4/9 : ℝ))) ^ 3 * occupation T (n + 1) ω)
      Filter.atTop (fun _ => (0 : ℝ)) := by
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro ε hε
  have he (n : ℕ) (ω : SampleSpace) :
      ‖((n + 1 : ℝ) ^ (-(4/9 : ℝ))) ^ 3 * occupation T (n + 1) ω - 0‖ =
        ((n + 1 : ℝ) ^ (-(4/9 : ℝ))) ^ 3 * occupation T (n + 1) ω := by
    rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg]
    exact mul_nonneg (by positivity) (occupation_nonneg T (n + 1) ω)
  simp_rw [he]
  exact weighted_occupation_tail_tendsto hT hε

end OperatorDerivativeRewrite.Foundation.IBMUniformClockOccupation
