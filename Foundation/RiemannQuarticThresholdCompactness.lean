import Foundation.RiemannQuarticCompactTimeFarZeros
import Mathlib.Topology.Sequences

/-! Nonreal zeros immediately below the actual threshold have a common
finite bound and possess a subsequence converging to a real threshold zero. -/
noncomputable section
open Set Filter Metric Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticThresholdCompactness
open RiemannQuarticFlow RiemannQuarticOpenObstruction RiemannQuarticActualPolynomialLimit
open RiemannQuarticThresholdZeros

theorem bounded_nonreal_zeros_all_times_ge_one :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ, 1 ≤ t →
      ∀ z : ℂ, flow t z = 0 → z.im ≠ 0 → ‖z‖ < B := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp RiemannQuarticUniformFarScale.eventually_all_zeros_real
  obtain ⟨B,hB,hfar⟩ := RiemannQuarticCompactTimeFarZeros.uniform_far_zeros_real T
  refine ⟨B,hB,?_⟩
  intro t ht z hz hi
  by_cases htT : t ≤ T
  · by_contra h
    exact hi (hfar t ht htT z (le_of_not_gt h) hz)
  · exact False.elim (hi (hT t (le_of_not_ge htT) z hz))

theorem bounded_nonreal_zeros_below_threshold :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ, 1 ≤ t → t ≤ sInf polynomialLimitStarts →
      ∀ z : ℂ, flow t z = 0 → z.im ≠ 0 → ‖z‖ < B := by
  obtain ⟨B,hB,hfar⟩ := RiemannQuarticCompactTimeFarZeros.uniform_far_zeros_real
    (sInf polynomialLimitStarts)
  refine ⟨B,hB,?_⟩
  intro t ht htA z hz hi
  by_contra h
  exact hi (hfar t ht htA z (le_of_not_gt h) hz)

theorem exists_convergent_nonreal_zeros_before_threshold :
    ∃ (s : ℕ → ℝ) (z : ℕ → ℂ) (w : ℂ),
      Tendsto s atTop (𝓝 (sInf polynomialLimitStarts)) ∧
      Tendsto z atTop (𝓝 w) ∧
      (∀ n, s n < sInf polynomialLimitStarts ∧ flow (s n) (z n) = 0 ∧ (z n).im ≠ 0) ∧
      flow (sInf polynomialLimitStarts) w = 0 ∧ w.im = 0 := by
  classical
  let A := sInf polynomialLimitStarts
  have hA : 8 < A := actual_start_infimum_strictly_above_eight
  have hex (n : ℕ) : ∃ t : ℝ, ∃ z : ℂ,
      A-1/((n : ℝ)+1) < t ∧ t < A ∧ flow t z = 0 ∧ z.im ≠ 0 := by
    obtain ⟨t,hlo,hhi,z,hz,hi⟩ := nonreal_zeros_arbitrarily_before_threshold
      (1/((n : ℝ)+1)) (by positivity)
    exact ⟨t,z,hlo,hhi,hz,hi⟩
  choose s z hlow hhigh hzero hnon using hex
  have hs1 (n : ℕ) : 1 ≤ s n := by
    have hden : 1 ≤ (n : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have he : 1/((n : ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr hden
    linarith [hlow n]
  have hs : Tendsto s atTop (𝓝 A) := by
    have hlo : Tendsto (fun n : ℕ => A-1/((n : ℝ)+1)) atTop (𝓝 A) := by
      simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
      (fun n => (hlow n).le) (fun n => (hhigh n).le)
  obtain ⟨B,hB,hbound⟩ := bounded_nonreal_zeros_below_threshold
  have hzB (n : ℕ) : z n ∈ closedBall (0 : ℂ) B := by
    rw [mem_closedBall_zero_iff]
    exact (hbound (s n) (hs1 n) (hhigh n).le (z n) (hzero n) (hnon n)).le
  obtain ⟨w,_,φ,hφ,hw⟩ := (isCompact_closedBall (0 : ℂ) B).tendsto_subseq hzB
  have hstime : Tendsto (s ∘ φ) atTop (𝓝 A) := hs.comp hφ.tendsto_atTop
  have hlimit := convergent_zeros_at_threshold_are_real (s ∘ φ) (z ∘ φ) w
    hstime hw (fun n => hzero (φ n))
  exact ⟨s ∘ φ,z ∘ φ,w,hstime,hw,fun n => ⟨hhigh (φ n),hzero (φ n),hnon (φ n)⟩,
    hlimit.1,hlimit.2⟩

end OperatorDerivativeRewrite.Foundation.RiemannQuarticThresholdCompactness
