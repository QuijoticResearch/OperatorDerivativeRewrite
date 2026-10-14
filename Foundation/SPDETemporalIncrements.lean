import Foundation.SPDETemporalCovariance

/-! Exact mean-square increments for deterministic-kernel Gaussian convolutions. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace OperatorDerivativeRewrite.Foundation.SPDETemporalIncrements
open GaussianTimeHilbert InfiniteGaussian GaussianHilbertProcess
open SPDEFiniteModes SPDEModulatedResponse
attribute [local instance] timeHilbert_secondCountable

theorem stochasticModulatedResponse_increment_energy (α : ℝ) (hα : 1 / 2 < α)
    (t u : ℝ≥0) (g h : ℝ → ℝ) (hg : Measurable g) (hh : Measurable h)
    (Mg Mh : ℝ) (hgM : ∀ s, |g s| ≤ Mg) (hhM : ∀ s, |h s| ≤ Mh) :
    ‖stochasticModulatedResponse α hα t g hg Mg hgM -
      stochasticModulatedResponse α hα u h hh Mh hhM‖^2 =
      ∫ s, (modulatedResponse α t g s - modulatedResponse α u h s)^2 := by
  change ‖isonormalEmbedding TimeHilbert _ - isonormalEmbedding TimeHilbert _‖^2 = _
  rw [← map_sub, LinearIsometry.norm_map,
    ← real_inner_self_eq_norm_sq, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (modulatedVector α hα t g hg Mg hgM)
    (modulatedVector α hα u h hh Mh hhM),
    modulatedVector_coeFn α hα t g hg Mg hgM,
    modulatedVector_coeFn α hα u h hh Mh hhM] with s hs hgs hhs
  simp only [hs, Pi.sub_apply, hgs, hhs]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem finiteGaussianResponse_increment_energy {n : ℕ} (c : Fin n → ℝ)
    (v w : Fin n → TimeHilbert) :
    ‖finiteGaussianResponse c v - finiteGaussianResponse c w‖^2 =
      ∑ i, (c i)^2 * ‖v i - w i‖^2 := by
  classical
  have hsum : (∑ i, c i • modeVector i (v i) : ModeHilbert n) -
      (∑ i, c i • modeVector i (w i) : ModeHilbert n) =
      ∑ i, c i • modeVector i (v i - w i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [modeVector, PiLp.single_sub, smul_sub]
  change ‖isonormalEmbedding (ModeHilbert n) _ -
    isonormalEmbedding (ModeHilbert n) _‖^2 = _
  rw [← map_sub, hsum]
  exact finiteGaussianResponse_energy c (fun i => v i - w i)

theorem finiteModulatedResponse_increment_energy {n : ℕ}
    (α : ℝ) (hα : 1 / 2 < α) (t u : ℝ≥0)
    (g : Fin n → ℝ → ℝ) (hg : ∀ i, Measurable (g i))
    (M : Fin n → ℝ) (hM : ∀ i s, |g i s| ≤ M i)
    (c : Fin n → ℝ) :
    ‖finiteModulatedResponse α hα t g hg M hM c -
      finiteModulatedResponse α hα u g hg M hM c‖^2 =
      ∑ i, (c i)^2 *
        ∫ s, (modulatedResponse α t (g i) s -
          modulatedResponse α u (g i) s)^2 := by
  rw [finiteModulatedResponse, finiteModulatedResponse,
    finiteGaussianResponse_increment_energy]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [← real_inner_self_eq_norm_sq, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub
      (modulatedVector α hα t (g i) (hg i) (M i) (hM i))
      (modulatedVector α hα u (g i) (hg i) (M i) (hM i)),
    modulatedVector_coeFn α hα t (g i) (hg i) (M i) (hM i),
    modulatedVector_coeFn α hα u (g i) (hg i) (M i) (hM i)] with s hs ht hu
  simp only [hs, Pi.sub_apply, ht, hu]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

end OperatorDerivativeRewrite.Foundation.SPDETemporalIncrements
