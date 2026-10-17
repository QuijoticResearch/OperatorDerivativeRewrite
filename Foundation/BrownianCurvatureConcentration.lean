import Foundation.BrownianSmoothMassPath

/-! Quantitative vanishing of the actual smooth curvature mass on intervals
where the Brownian path stays a positive distance from zero. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianCurvatureConcentration
open InfiniteGaussian IBMConstructedSources SmoothAbsoluteApproximation
open BrownianSmoothMassPath RealSteklovApprox

theorem curvature_away_zero {e δ : ℝ} (he : 0 < e) (hδ : 0 < δ) {x : ℝ}
    (hx : δ ≤ |x|) : curvature e x ≤ e ^ 2 / δ ^ 3 := by
  unfold curvature
  exact div_le_div_of_nonneg_left (sq_nonneg e) (pow_pos hδ 3)
    (pow_le_pow_left₀ hδ.le (hx.trans (abs_le_radius he x)) 3)

theorem path_increment (n : ℕ) (ω : SampleSpace) (s t : ℝ≥0) :
    path n ω t - path n ω s = (1 / 2 : ℝ) *
      ∫ u in (s : ℝ)..(t : ℝ), rate (width n) ω u := by
  have hc := rate_continuous (width_pos n) ω
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := (volume : Measure ℝ))
    (hc.intervalIntegrable 0 (s : ℝ)) (hc.intervalIntegrable (s : ℝ) (t : ℝ))
  simp only [path, ContinuousMap.coe_mk, primitive]
  linarith

theorem path_increment_bound (n : ℕ) (ω : SampleSpace) (s t : ℝ≥0) (hst : s ≤ t)
    {δ : ℝ} (hδ : 0 < δ)
    (hb : ∀ u : ℝ≥0, u ∈ Icc s t → δ ≤ |clockPath ω u|) :
    0 ≤ path n ω t - path n ω s ∧
      path n ω t - path n ω s ≤
        (1 / 2 : ℝ) * ((t : ℝ) - s) * (width n ^ 2 / δ ^ 3) := by
  refine ⟨sub_nonneg.mpr (path_monotone n ω hst), ?_⟩
  have hc := rate_continuous (width_pos n) ω
  have hi := intervalIntegral.integral_mono_on (show (s : ℝ) ≤ t from hst)
    (hc.intervalIntegrable (s : ℝ) (t : ℝ))
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => width n ^ 2 / δ ^ 3)
      volume (s : ℝ) (t : ℝ)) (by
      intro u hu
      have hu0 : 0 ≤ u := s.property.trans hu.1
      have hs : s ≤ u.toNNReal := by
        change (s : ℝ) ≤ (u.toNNReal : ℝ)
        rw [Real.coe_toNNReal _ hu0]
        exact hu.1
      have ht : u.toNNReal ≤ t := by
        change (u.toNNReal : ℝ) ≤ (t : ℝ)
        rw [Real.coe_toNNReal _ hu0]
        exact hu.2
      exact curvature_away_zero (width_pos n) hδ (hb u.toNNReal ⟨hs, ht⟩))
  rw [path_increment]
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
  nlinarith

end OperatorDerivativeRewrite.Foundation.BrownianCurvatureConcentration
