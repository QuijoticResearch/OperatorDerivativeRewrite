import Foundation.SPDEFiniteGalerkin

/-! Exact temporal covariance of finite Brownian spectral forcing responses. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace OperatorDerivativeRewrite.Foundation.SPDETemporalCovariance
open GaussianTimeHilbert InfiniteGaussian GaussianHilbertProcess
open SPDEFiniteModes SPDEModulatedResponse
attribute [local instance] timeHilbert_secondCountable

theorem modulated_cross_time_moment (α : ℝ) (hα : 1 / 2 < α)
    (t u : ℝ≥0) (g h : ℝ → ℝ) (hg : Measurable g) (hh : Measurable h)
    (Mg Mh : ℝ) (hgM : ∀ s, |g s| ≤ Mg) (hhM : ∀ s, |h s| ≤ Mh) :
    (∫ ω, isonormal TimeHilbert (modulatedVector α hα t g hg Mg hgM) ω *
      isonormal TimeHilbert (modulatedVector α hα u h hh Mh hhM) ω ∂gaussianProduct) =
      ∫ s, modulatedResponse α t g s * modulatedResponse α u h s := by
  rw [isonormal_product_integral, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [modulatedVector_coeFn α hα t g hg Mg hgM,
    modulatedVector_coeFn α hα u h hh Mh hhM] with s hgs hhs
  simp [hgs, hhs, mul_comm]

theorem mode_cross_time_moment {n : ℕ} (i j : Fin n)
    (α : ℝ) (hα : 1 / 2 < α) (t u : ℝ≥0)
    (g h : ℝ → ℝ) (hg : Measurable g) (hh : Measurable h)
    (Mg Mh : ℝ) (hgM : ∀ s, |g s| ≤ Mg) (hhM : ∀ s, |h s| ≤ Mh) :
    (∫ ω, isonormal (ModeHilbert n)
        (modeVector i (modulatedVector α hα t g hg Mg hgM)) ω *
      isonormal (ModeHilbert n)
        (modeVector j (modulatedVector α hα u h hh Mh hhM)) ω
      ∂gaussianProduct) =
      if i = j then
        ∫ s, modulatedResponse α t g s * modulatedResponse α u h s
      else 0 := by
  rw [isonormal_product_integral, modeVector_inner]
  split_ifs with hij
  · have hc := modulated_cross_time_moment α hα t u g h hg hh Mg Mh hgM hhM
    simpa only [isonormal_product_integral] using hc
  · rfl

theorem finiteGaussianResponse_cross_inner {n : ℕ} (c d : Fin n → ℝ)
    (v w : Fin n → TimeHilbert) :
    inner ℝ (finiteGaussianResponse c v) (finiteGaussianResponse d w) =
      ∑ i, c i * d i * inner ℝ (v i) (w i) := by
  classical
  rw [finiteGaussianResponse, finiteGaussianResponse,
    LinearIsometry.inner_map_map, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have hv : ((∑ j, c j • modeVector j (v j) : ModeHilbert n).ofLp i) =
      c i • v i := by simp [modeVector, Pi.single_apply]
  have hw : ((∑ j, d j • modeVector j (w j) : ModeHilbert n).ofLp i) =
      d i • w i := by simp [modeVector, Pi.single_apply]
  rw [hv, hw]
  simp only [real_inner_smul_left, real_inner_smul_right]
  ring

theorem finiteModulatedResponse_cross_time_inner {n : ℕ}
    (α : ℝ) (hα : 1 / 2 < α) (t u : ℝ≥0)
    (g h : Fin n → ℝ → ℝ)
    (hg : ∀ i, Measurable (g i)) (hh : ∀ i, Measurable (h i))
    (Mg Mh : Fin n → ℝ)
    (hgM : ∀ i s, |g i s| ≤ Mg i)
    (hhM : ∀ i s, |h i s| ≤ Mh i)
    (c d : Fin n → ℝ) :
    inner ℝ (finiteModulatedResponse α hα t g hg Mg hgM c)
      (finiteModulatedResponse α hα u h hh Mh hhM d) =
      ∑ i, c i * d i *
        ∫ s, modulatedResponse α t (g i) s * modulatedResponse α u (h i) s := by
  rw [finiteModulatedResponse, finiteModulatedResponse,
    finiteGaussianResponse_cross_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [L2_inner_eq_integral]
  congr 1
  apply integral_congr_ae
  filter_upwards [modulatedVector_coeFn α hα t (g i) (hg i) (Mg i) (hgM i),
    modulatedVector_coeFn α hα u (h i) (hh i) (Mh i) (hhM i)] with s hs ht
  simp [hs, ht, mul_comm]

end OperatorDerivativeRewrite.Foundation.SPDETemporalCovariance
