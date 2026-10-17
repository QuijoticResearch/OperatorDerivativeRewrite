import Foundation.BrownianSmoothFiniteSetMaximal
import Mathlib.Topology.Bases

/-! A maximal probability estimate on the whole compact time interval,
obtained from arbitrary finite time sets and path continuity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianSmoothCompactMaximal
open InfiniteGaussian BrownianTanakaApproximation BrownianSmoothMassRealization
open BrownianSmoothFiniteSetMaximal

theorem crossing_countable (n m : ℕ) (T ε : ℝ≥0) :
    ∃ u : ℕ → ℝ≥0, (∀ i, u i ≤ T) ∧
      {ω | ∃ t : ℝ≥0, t ≤ T ∧
        (ε : ℝ) < ‖compensatedPath n ω t - compensatedPath m ω t‖} =
      {ω | ∃ i, (ε : ℝ) < ‖compensatedPath n ω (u i) - compensatedPath m ω (u i)‖} := by
  let K := {t : ℝ≥0 // t ≤ T}
  letI : Nonempty K := ⟨⟨0, T.property⟩⟩
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq K
  refine ⟨fun i => (d i).val, fun i => (d i).property, ?_⟩
  ext ω
  constructor
  · rintro ⟨t, ht, he⟩
    have hc : Continuous (fun s : K =>
        ‖compensatedPath n ω s.val - compensatedPath m ω s.val‖) :=
      (((compensatedPath n ω).continuous.comp continuous_subtype_val).sub
        ((compensatedPath m ω).continuous.comp continuous_subtype_val)).norm
    obtain ⟨i, hi⟩ := hd.exists_mem_open (isOpen_lt continuous_const hc) ⟨⟨t, ht⟩, he⟩
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨(d i).val, (d i).property, hi⟩

theorem crossing_measurable (n m : ℕ) (T ε : ℝ≥0) :
    MeasurableSet {ω | ∃ t : ℝ≥0, t ≤ T ∧
      (ε : ℝ) < ‖compensatedPath n ω t - compensatedPath m ω t‖} := by
  obtain ⟨u, _, he⟩ := crossing_countable n m T ε
  rw [he]
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro i
  exact measurableSet_lt measurable_const
    (((compensatedPath_coordinate_measurable n (u i)).sub
      (compensatedPath_coordinate_measurable m (u i))).norm)

theorem compact_maximal (n m : ℕ) (T ε : ℝ≥0) :
    (ε : ℝ≥0∞) * gaussianProduct {ω | ∃ t : ℝ≥0, t ≤ T ∧
      (ε : ℝ) < ‖compensatedPath n ω t - compensatedPath m ω t‖} ≤
      ENNReal.ofReal ‖approximateField n T - approximateField m T‖ := by
  obtain ⟨u, hu, he⟩ := crossing_countable n m T ε
  rw [he]
  calc
    _ ≤ (ε : ℝ≥0∞) * gaussianProduct {ω | ∃ i,
        (ε : ℝ) ≤ ‖compensatedPath n ω (u i) - compensatedPath m ω (u i)‖} := by
      gcongr
      exact fun hi => hi.le
    _ ≤ _ := countable_maximal n m T u hu ε

end OperatorDerivativeRewrite.Foundation.BrownianSmoothCompactMaximal
