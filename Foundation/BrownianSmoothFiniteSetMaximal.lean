import Foundation.BrownianSmoothGridMaximal
import Mathlib.Data.Finset.Sort

/-! Sorting arbitrary finite time sets and passing to countable collections
without any grid-cardinality loss in the maximal estimate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianSmoothFiniteSetMaximal
open InfiniteGaussian BrownianTanakaApproximation BrownianSmoothMassRealization
open BrownianSmoothGridMaximal

theorem finite_set_maximal (n m : ℕ) (T : ℝ≥0) (s : Finset ℝ≥0)
    (hT : ∀ t ∈ s, t ≤ T) (ε : ℝ≥0) :
    (ε : ℝ≥0∞) * gaussianProduct {ω | ∃ t ∈ s,
      (ε : ℝ) ≤ ‖compensatedPath n ω t - compensatedPath m ω t‖} ≤
      ENNReal.ofReal ‖approximateField n T - approximateField m T‖ := by
  classical
  by_cases hs : s.Nonempty
  · have hc : 0 < s.card := Finset.card_pos.mpr hs
    let e : Fin s.card ↪o ℝ≥0 := s.orderEmbOfFin rfl
    let τ : ℕ → ℝ≥0 := fun i => e ⟨min i (s.card - 1), by omega⟩
    have hτ : Monotone τ := by
      intro i j hij
      exact e.monotone (show min i (s.card - 1) ≤ min j (s.card - 1) from
        min_le_min_right _ hij)
    have hτT : ∀ i, τ i ≤ T := by
      intro i
      exact hT _ (s.orderEmbOfFin_mem rfl _)
    have h := finite_grid_maximal n m T τ hτ hτT ε (s.card - 1)
    have he : {ω | ∃ t ∈ s, (ε : ℝ) ≤ ‖compensatedPath n ω t - compensatedPath m ω t‖} ⊆
        {ω | ∃ i ≤ s.card - 1,
          (ε : ℝ) ≤ ‖compensatedPath n ω (τ i) - compensatedPath m ω (τ i)‖} := by
      rintro ω ⟨t, ht, hb⟩
      obtain ⟨i, hi⟩ := (s.range_orderEmbOfFin rfl).symm ▸ (show t ∈ (s : Set ℝ≥0) from ht)
      have hit : τ i.val = t := by
        change e ⟨min i.val (s.card - 1), _⟩ = t
        have hmin : min i.val (s.card - 1) = i.val := min_eq_left (by omega)
        simpa only [hmin] using hi
      exact ⟨i.val, by omega, by simpa only [hit] using hb⟩
    calc
      _ ≤ (ε : ℝ≥0∞) * gaussianProduct {ω | ∃ i ≤ s.card - 1,
          (ε : ℝ) ≤ ‖compensatedPath n ω (τ i) - compensatedPath m ω (τ i)‖} := by
        gcongr
      _ ≤ _ := h
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]

theorem countable_maximal (n m : ℕ) (T : ℝ≥0) (u : ℕ → ℝ≥0)
    (hu : ∀ i, u i ≤ T) (ε : ℝ≥0) :
    (ε : ℝ≥0∞) * gaussianProduct {ω | ∃ i,
      (ε : ℝ) ≤ ‖compensatedPath n ω (u i) - compensatedPath m ω (u i)‖} ≤
      ENNReal.ofReal ‖approximateField n T - approximateField m T‖ := by
  classical
  let A : ℕ → Set SampleSpace := fun N => {ω | ∃ i ≤ N,
    (ε : ℝ) ≤ ‖compensatedPath n ω (u i) - compensatedPath m ω (u i)‖}
  have hA : Monotone A := by
    intro N M hNM ω hω
    obtain ⟨i, hi, he⟩ := hω
    exact ⟨i, hi.trans hNM, he⟩
  have hU : {ω | ∃ i, (ε : ℝ) ≤ ‖compensatedPath n ω (u i) - compensatedPath m ω (u i)‖} =
      ⋃ N, A N := by
    ext ω
    simp only [A, mem_ofPred_eq, mem_iUnion]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, i, le_rfl, hi⟩, fun ⟨_, i, _, hi⟩ => ⟨i, hi⟩⟩
  rw [hU, hA.measure_iUnion, ENNReal.mul_iSup]
  apply iSup_le
  intro N
  have h := finite_set_maximal n m T ((Finset.range (N + 1)).image u) (by
    intro t ht
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
    exact hu i) ε
  simpa only [A, Finset.mem_image, Finset.mem_range, Nat.lt_succ_iff, exists_exists_and_eq_and]
    using h

end OperatorDerivativeRewrite.Foundation.BrownianSmoothFiniteSetMaximal
