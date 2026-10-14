import Foundation.GaussianTerminalPredictionSpectrum

/-! Sharp Gaussian maximal-correlation inequality between a terminal
coordinate's full L2 space and arbitrary Gaussian observations. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianTerminalMaximalCorrelation
open InfiniteGaussian GaussianTimeSpaceHermite GaussianConditionalGraph
open GaussianWickConditionalProjection GaussianSingleObservationPrediction GaussianTerminalPredictionSpectrum

theorem coefficient_zero_eq_mean (u : CoefficientSpace) (f : GaussianL2) :
    coefficient u f 0=∫ ω, f ω ∂gaussianProduct := by
  rw [coefficient,show (wick u 0 : GaussianL2)=gaussianOne from core_zero u _,
    gaussianOne_inner_eq_integral]
  simp

theorem terminal_prediction_efficiency {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) (hu : ‖u‖^2=1) (f : GaussianL2)
    (hf : f∈singleGenerated u) (hmean : ∫ ω, f ω ∂gaussianProduct=0) :
    ‖conditionalProjection h f‖^2 ≤ ‖sourceProjection h u‖^2*‖f‖^2 := by
  have hr : ∀ n, n<1 → coefficient u f n=0 := by
    intro n hn
    have he : n=0 := Nat.lt_one_iff.mp hn
    rw [he,coefficient_zero_eq_mean,hmean]
  simpa only [pow_one] using terminal_prediction_rank_upper h u hu f hf 1 hr

theorem terminal_observation_covariance_bound {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) (hu : ‖u‖^2=1) (f : GaussianL2)
    (hf : f∈singleGenerated u) (hmean : ∫ ω, f ω ∂gaussianProduct=0)
    (g : GaussianL2) (hg : g∈generated h) :
    (inner ℝ f g)^2 ≤ ‖sourceProjection h u‖^2*‖f‖^2*‖g‖^2 := by
  have he := (generated h).starProjection_inner_eq_zero f g hg
  change inner ℝ (f-conditionalProjection h f) g=0 at he
  rw [inner_sub_left] at he
  have hp := terminal_prediction_efficiency h u hu f hf hmean
  have hc := abs_real_inner_le_norm (conditionalProjection h f) g
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hc
  rw [sq_abs,mul_pow] at hs
  have hm := mul_le_mul_of_nonneg_right hp (sq_nonneg ‖g‖)
  have hi : inner ℝ f g=inner ℝ (conditionalProjection h f) g := by linarith
  rw [hi]
  exact hs.trans hm

theorem linear_prediction_attains_bound {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) (hu : ‖u‖^2=1) :
    ‖conditionalProjection h (firstChaosEmbedding u)‖^2=
      ‖sourceProjection h u‖^2*‖firstChaosEmbedding u‖^2 := by
  rw [conditional_firstChaos_projection,LinearIsometry.norm_map,LinearIsometry.norm_map,hu,mul_one]

theorem linear_covariance_attains_bound {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) (hu : ‖u‖^2=1) :
    (inner ℝ (firstChaosEmbedding u) (firstChaosEmbedding (sourceProjection h u)))^2=
      ‖sourceProjection h u‖^2*‖firstChaosEmbedding u‖^2*
        ‖firstChaosEmbedding (sourceProjection h u)‖^2 := by
  have hp := (sourceSpan h).starProjection_inner_eq_zero u (sourceProjection h u)
    ((sourceSpan h).starProjection_apply_mem u)
  change inner ℝ (u-sourceProjection h u) (sourceProjection h u)=0 at hp
  rw [inner_sub_left,real_inner_self_eq_norm_sq] at hp
  rw [LinearIsometry.inner_map_map,LinearIsometry.norm_map,LinearIsometry.norm_map,hu]
  nlinarith

end OperatorDerivativeRewrite.Foundation.GaussianTerminalMaximalCorrelation
