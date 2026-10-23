import Foundation.IBMUniformCrossingPenalty
import Foundation.GaussianBrownianQuadraticVariation

/-! The actual IBM quartic variation is 3T in probability along all uniform
grids. The raw Brownian quadratic-variation theorem is reused, not assumed. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMUniformQuarticVariation
open InfiniteGaussian IBMSourceLaws IBMConstructedSources IBMUniformClockGridEnergy
open IBMUniformQuarticFamily IBMUniformQuarticProbability IBMUniformCrossingPenalty
open GaussianBrownianQuadraticVariation
attribute [local irreducible] IBMConstructedSources.clockPath

def clockSquare (T : ℝ≥0) (n : ℕ) (ω : SampleSpace) : ℝ :=
  ∑ i ∈ Finset.range n, (clockPath ω (grid (T / n) (i + 1)) -
    clockPath ω (grid (T / n) i)) ^ 2

theorem clockSquare_measurable (T : ℝ≥0) (n : ℕ) : Measurable (clockSquare T n) := by
  apply Finset.measurable_sum
  intro i hi
  exact (((ContinuousMap.measurable_eval _).comp clockPath_measurable).sub
    ((ContinuousMap.measurable_eval _).comp clockPath_measurable)).pow_const 2

theorem uniformTime_grid (T : ℝ≥0) (n : ℕ) (i : Fin (n + 2)) :
    uniformTime T n i = grid (T / (n + 1)) i.val := by
  unfold uniformTime grid
  push_cast
  ring

theorem quadraticVariation_actual_ae (T : ℝ≥0) (n : ℕ) :
    (quadraticVariation (uniformTime T n) : SampleSpace → ℝ) =ᵐ[gaussianProduct]
      clockSquare T (n + 1) := by
  have hc : ∀ᵐ ω ∂gaussianProduct, ∀ i : Fin (n + 2),
      clockPath ω (uniformTime T n i) = GaussianTimeProcess.process (uniformTime T n i) ω :=
    ae_all_iff.mpr fun i => clockPath_coordinate_ae _
  filter_upwards [quadraticVariation_coeFn (uniformTime T n) (uniformTime_monotone T n), hc]
    with ω hq hω
  rw [hq]
  rw [clockSquare, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← hω i.succ, ← hω i.castSucc]
  simp only [uniformTime_grid, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]

theorem actual_clockSquare_tendstoInMeasure (T : ℝ≥0) :
    TendstoInMeasure gaussianProduct (fun n : ℕ => clockSquare T (n + 1))
      Filter.atTop (fun _ => (T : ℝ)) := by
  have h := tendstoInMeasure_of_tendsto_Lp (uniform_quadraticVariation_tendsto T)
  have he : ((T : ℝ) • gaussianOne : GaussianL2) =ᵐ[gaussianProduct]
      (fun _ => (T : ℝ)) := by
    filter_upwards [Lp.coeFn_smul (T : ℝ) gaussianOne,
      gaussianOne_coeFn] with ω hs h1
    rw [hs]
    simp only [Pi.smul_apply, h1, smul_eq_mul, mul_one]
  exact h.congr (quadraticVariation_actual_ae T) he

/-- Exact decomposition of the clock-conditional quartic mean. -/
theorem clockMean_identity (T : ℝ≥0) (n : ℕ) (ω : SampleSpace) :
    clockMean T n ω = 3 * clockSquare T n ω - 3 * penalty T n ω := by
  unfold clockMean clockSquare penalty IBMUniformQuarticFamily.segment
  simp_rw [IBMReflectedClockCorrection.reflected_increment_sq, mul_sub,
    Finset.sum_sub_distrib, ← Finset.mul_sum]

attribute [local irreducible] clockSquare IBMUniformQuarticFamily.clockMean
  IBMUniformCrossingPenalty.penalty

theorem clockMean_tendstoInMeasure {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure gaussianProduct (fun n : ℕ => clockMean T (n + 1))
      Filter.atTop (fun _ => 3 * (T : ℝ)) := by
  have hq := tendstoInMeasure_iff_measureReal_norm.mp (actual_clockSquare_tendstoInMeasure T)
  have hp := tendstoInMeasure_iff_measureReal_norm.mp (penalty_tendstoInMeasure hT)
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro ε hε
  have he : 0 < ε / 6 := by positivity
  have hb (n : ℕ) :
      gaussianProduct.real {ω | ε ≤ |clockMean T (n + 1) ω - 3 * (T : ℝ)|} ≤
      gaussianProduct.real {ω | ε / 6 ≤ |clockSquare T (n + 1) ω - T|} +
      gaussianProduct.real {ω | ε / 6 ≤ penalty T (n + 1) ω} := by
    have hs : {ω | ε ≤ |clockMean T (n + 1) ω - 3 * (T : ℝ)|} ⊆
        {ω | ε / 6 ≤ |clockSquare T (n + 1) ω - T|} ∪
        {ω | ε / 6 ≤ penalty T (n + 1) ω} := by
      intro ω hω
      change ε ≤ |clockMean T (n + 1) ω - 3 * (T : ℝ)| at hω
      by_contra hnot
      have h1 : |clockSquare T (n + 1) ω - T| < ε / 6 := by
        by_contra h; exact hnot (Or.inl (le_of_not_gt h))
      have h2 : penalty T (n + 1) ω < ε / 6 := by
        by_contra h; exact hnot (Or.inr (le_of_not_gt h))
      have heq : clockMean T (n + 1) ω - 3 * (T : ℝ) =
          3 * (clockSquare T (n + 1) ω - T) - 3 * penalty T (n + 1) ω := by
        rw [clockMean_identity]; ring
      rw [heq] at hω
      have hab := abs_sub_le (3 * (clockSquare T (n + 1) ω - T)) 0
        (3 * penalty T (n + 1) ω)
      simp only [sub_zero, zero_sub, abs_neg] at hab
      rw [abs_mul, abs_mul, abs_of_nonneg (penalty_nonneg _ _ _)] at hab
      norm_num at hab
      linarith
    exact (measureReal_mono hs (by finiteness)).trans (measureReal_union_le _ _)
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) hb
  have hq' := hq (ε / 6) he
  have hp' := hp (ε / 6) he
  simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg (penalty_nonneg _ _ _), add_zero] using
    hq'.add hp'

theorem clock_event_measure (s : Set SampleSpace) :
    jointMeasure.real {ω : JointSample | ω.2 ∈ s} = gaussianProduct.real s := by
  have he : {ω : JointSample | ω.2 ∈ s} = univ ×ˢ s := by ext ω; simp
  rw [he, Measure.real, jointMeasure, Measure.prod_prod, measure_univ, one_mul]
  rfl

/-- Uniform quartic variation of the existing actual reflected-clock IBM,
under the original independent scenery-clock product law. -/
theorem quartic_tendstoInMeasure {T : ℝ≥0} (hT : 0 < T) :
    TendstoInMeasure jointMeasure (fun n : ℕ => quartic T (n + 1))
      Filter.atTop (fun _ => 3 * (T : ℝ)) := by
  have hr := tendstoInMeasure_iff_measureReal_norm.mp (residual_tendstoInMeasure hT)
  have hm := tendstoInMeasure_iff_measureReal_norm.mp (clockMean_tendstoInMeasure hT)
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro ε hε
  have he : 0 < ε / 2 := by positivity
  have hb (n : ℕ) :
      jointMeasure.real {ω | ε ≤ |quartic T (n + 1) ω - 3 * (T : ℝ)|} ≤
      jointMeasure.real {ω | ε / 2 ≤ |residual T (n + 1) ω|} +
      gaussianProduct.real {y | ε / 2 ≤ |clockMean T (n + 1) y - 3 * (T : ℝ)|} := by
    have hs : {ω : JointSample | ε ≤ |quartic T (n + 1) ω - 3 * (T : ℝ)|} ⊆
        {ω | ε / 2 ≤ |residual T (n + 1) ω|} ∪
        {ω | ε / 2 ≤ |clockMean T (n + 1) ω.2 - 3 * (T : ℝ)|} := by
      intro ω hω
      change ε ≤ |quartic T (n + 1) ω - 3 * (T : ℝ)| at hω
      by_contra hnot
      have h1 : |residual T (n + 1) ω| < ε / 2 := by
        by_contra h; exact hnot (Or.inl (le_of_not_gt h))
      have h2 : |clockMean T (n + 1) ω.2 - 3 * (T : ℝ)| < ε / 2 := by
        by_contra h; exact hnot (Or.inr (le_of_not_gt h))
      have hab := abs_add_le (residual T (n + 1) ω)
        (clockMean T (n + 1) ω.2 - 3 * (T : ℝ))
      have heq : residual T (n + 1) ω + (clockMean T (n + 1) ω.2 - 3 * (T : ℝ)) =
          quartic T (n + 1) ω - 3 * (T : ℝ) := by unfold IBMUniformQuarticFamily.residual; ring
      rw [heq] at hab
      linarith
    have h := (measureReal_mono (μ := jointMeasure) hs (by finiteness)).trans
      (measureReal_union_le _ _)
    have hmarg : jointMeasure.real {ω : JointSample |
        ε / 2 ≤ |clockMean T (n + 1) ω.2 - 3 * (T : ℝ)|} =
        gaussianProduct.real {y | ε / 2 ≤ |clockMean T (n + 1) y - 3 * (T : ℝ)|} :=
      clock_event_measure {y | ε / 2 ≤ |clockMean T (n + 1) y - 3 * (T : ℝ)|}
    rw [hmarg] at h
    exact h
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) hb
  have hr' := hr (ε / 2) he
  have hm' := hm (ε / 2) he
  simpa only [Real.norm_eq_abs, sub_zero, add_zero] using hr'.add hm'

end OperatorDerivativeRewrite.Foundation.IBMUniformQuarticVariation
