import Foundation.BrownianCurvatureConcentration
import Foundation.BrownianMassLimitIdentification

/-! The constructed continuous mass cannot increase across a compact interval
that contains no Brownian zero. No Stieltjes support theorem is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianMassZeroFreeIntervals
open InfiniteGaussian IBMConstructedSources BrownianSmoothMassPath
open BrownianMassFastSubsequence BrownianMassContinuousLimit BrownianCurvatureConcentration
open RealSteklovApprox

theorem constant_of_away_zero {ω : SampleSpace}
    (hω : Tendsto (fun j => path (subsequence j) ω) atTop (𝓝 (limitPath ω)))
    (s t : ℝ≥0) (hst : s ≤ t) {δ : ℝ} (hδ : 0 < δ)
    (hb : ∀ u : ℝ≥0, u ∈ Icc s t → δ ≤ |clockPath ω u|) :
    limitPath ω s = limitPath ω t := by
  have hp (r : ℝ≥0) : Tendsto (fun j => path (subsequence j) ω r) atTop (𝓝 (limitPath ω r)) := by
    have he : Continuous (fun f : C(ℝ≥0, ℝ) => f r) := by fun_prop
    exact he.continuousAt.tendsto.comp hω
  have hd := (hp t).sub (hp s)
  have hw := (width_tendsto.mono_right nhdsWithin_le_nhds).comp
    subsequence_strictMono.tendsto_atTop
  have hu := ((hw.pow 2).div_const (δ ^ 3)).const_mul ((1 / 2 : ℝ) * ((t : ℝ) - s))
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, mul_zero] at hu
  have hle : limitPath ω t - limitPath ω s ≤ 0 :=
    le_of_tendsto_of_tendsto' hd hu
      (fun j => (path_increment_bound (subsequence j) ω s t hst hδ hb).2)
  have hge : 0 ≤ limitPath ω t - limitPath ω s :=
    ge_of_tendsto' hd (fun j => (path_increment_bound (subsequence j) ω s t hst hδ hb).1)
  linarith

theorem zero_free_constant : ∀ᵐ ω ∂gaussianProduct, ∀ s t : ℝ≥0, s ≤ t →
    (∀ u : ℝ≥0, u ∈ Icc s t → clockPath ω u ≠ 0) →
      limitPath ω s = limitPath ω t := by
  filter_upwards [limitPath_tendsto] with ω hω s t hst hn
  have hc : Continuous (fun u : ℝ≥0 => |clockPath ω u|) := (clockPath ω).continuous.abs
  obtain ⟨u, hu, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hst) hc.continuousOn
  exact constant_of_away_zero hω s t hst (abs_pos.mpr (hn u hu)) (fun v hv => hmin hv)

theorem increase_forces_zero : ∀ᵐ ω ∂gaussianProduct, ∀ s t : ℝ≥0, s ≤ t →
    limitPath ω s < limitPath ω t → ∃ u ∈ Icc s t, clockPath ω u = 0 := by
  filter_upwards [zero_free_constant] with ω hω s t hst hinc
  by_contra! hn
  exact (ne_of_lt hinc) (hω s t hst hn)

end OperatorDerivativeRewrite.Foundation.BrownianMassZeroFreeIntervals
