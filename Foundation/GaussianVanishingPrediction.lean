import Foundation.GaussianSingleObservationPrediction
import Mathlib.Topology.MetricSpace.UniformConvergence

/-! Nonlinear one-observation prediction from vanishing first-chaos prediction.
This supplies a Gaussian germ reduction for IBM localization. No assertion that
the actual IBM germ satisfies the hypothesis, or is trivial, is made here. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianVanishingPrediction
open InfiniteGaussian GaussianConditionalGraph GaussianWickConditionalProjection
open GaussianTimeSpaceHermite GaussianSingleObservationPrediction

def meanProjection : GaussianL2 →L[ℝ] GaussianL2 :=
  (innerSL ℝ gaussianOne).smulRight gaussianOne

theorem meanProjection_apply (F : GaussianL2) :
    meanProjection F = (∫ ω, F ω ∂gaussianProduct) • gaussianOne := by
  change inner ℝ gaussianOne F • gaussianOne = _
  rw [gaussianOne_inner_eq_integral]

theorem scaled_source_prediction (u : CoefficientSpace) (c : ℝ) (hc : c ≠ 0) :
    sourceProjection (fun _ : Unit => c • u) u = u := by
  have hm : c • u ∈ sourceSpan (fun _ : Unit => c • u) :=
    (Submodule.span ℝ (range (fun _ : Unit => c • u))).le_topologicalClosure
      (Submodule.subset_span ⟨(), rfl⟩)
  have hu : u ∈ sourceSpan (fun _ : Unit => c • u) := by
    have hs := (sourceSpan (fun _ : Unit => c • u)).smul_mem c⁻¹ hm
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hs
  exact (sourceSpan (fun _ : Unit => c • u)).starProjection_eq_self_iff.mpr hu

theorem wick_zero_succ (n : ℕ) : (wick (0 : CoefficientSpace) (n+1) : GaussianL2) = 0 := by
  apply norm_eq_zero.mp
  have h := GaussianWickContinuity.wick_norm_sq (0 : CoefficientSpace) (n+1)
  simp only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    zero_pow (Nat.succ_ne_zero n), mul_zero] at h
  nlinarith [norm_nonneg (wick (0 : CoefficientSpace) (n+1) : GaussianL2)]

theorem mean_wick (u : CoefficientSpace) (n : ℕ) :
    meanProjection (wick u n) = (wick (0 : CoefficientSpace) n : GaussianL2) := by
  cases n with
  | zero =>
    simp only [wick, core_zero]
    change inner ℝ gaussianOne gaussianOne • gaussianOne = gaussianOne
    rw [GaussianDeterministicGraphCore.gaussianOne_inner_self, one_smul]
  | succ n =>
    change inner ℝ gaussianOne (wick u (n+1) : GaussianL2) • gaussianOne = _
    rw [wick_centered, zero_smul, wick_zero_succ]

variable {I : Type*} (h : ℕ → I → CoefficientSpace)

def convergenceSpace : Submodule ℝ GaussianL2 where
  carrier := {F | Tendsto (fun n => conditionalProjection (h n) F) atTop (𝓝 (meanProjection F))}
  zero_mem' := by
    change Tendsto (fun n => conditionalProjection (h n) 0) atTop (𝓝 (meanProjection 0))
    simpa only [map_zero] using (tendsto_const_nhds (x := (0 : GaussianL2)))
  add_mem' := by
    intro F G hF hG
    change Tendsto (fun n => conditionalProjection (h n) (F+G)) atTop
      (𝓝 (meanProjection (F+G)))
    simpa only [map_add] using hF.add hG
  smul_mem' := by
    intro c F hF
    change Tendsto (fun n => conditionalProjection (h n) (c • F)) atTop
      (𝓝 (meanProjection (c • F)))
    simpa only [map_smul] using hF.const_smul c

theorem convergenceSpace_isClosed : IsClosed (convergenceSpace h : Set GaussianL2) := by
  have he : Equicontinuous (fun n => conditionalProjection (h n)) :=
    (LipschitzWith.uniformEquicontinuous (fun n => conditionalProjection (h n)) 1
      (fun n => (generated (h n)).lipschitzWith_starProjection)).equicontinuous
  exact he.isClosed_setOfPred_tendsto meanProjection.continuous

theorem wick_tendsto (u : CoefficientSpace)
    (hu : Tendsto (fun n => sourceProjection (h n) u) atTop (𝓝 0)) (d : ℕ) :
    Tendsto (fun n => conditionalProjection (h n) (wick u d)) atTop
      (𝓝 (meanProjection (wick u d))) := by
  simpa only [Function.comp_def, conditional_wick_projection, mean_wick] using
    ((GaussianWickContinuity.wick_continuous d).tendsto (0 : CoefficientSpace)).comp hu

theorem single_tendsto (u : CoefficientSpace)
    (hu : Tendsto (fun n => sourceProjection (h n) u) atTop (𝓝 0))
    (F : GaussianL2) (hF : F ∈ singleGenerated u) :
    Tendsto (fun n => conditionalProjection (h n) F) atTop (𝓝 (meanProjection F)) := by
  have hs : wickSpan u ≤ convergenceSpace h := by
    apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    exact wick_tendsto h u hu d
  have hc := (wickSpan u).topologicalClosure_minimal hs (convergenceSpace_isClosed h)
  rw [wickSpan_closure] at hc
  exact hc hF

theorem single_prediction_zero (u : CoefficientSpace)
    (hu : Tendsto (fun n => sourceProjection (h n) u) atTop (𝓝 0))
    (F : GaussianL2) (hF : F ∈ singleGenerated u)
    (hmean : ∫ ω, F ω ∂gaussianProduct = 0) :
    Tendsto (fun n => conditionalProjection (h n) F) atTop (𝓝 0) := by
  simpa only [meanProjection_apply, hmean, zero_smul] using single_tendsto h u hu F hF

theorem single_from_linear_prediction (u : CoefficientSpace)
    (hu : Tendsto (fun n => conditionalProjection (h n) (firstChaosEmbedding u))
      atTop (𝓝 0)) (F : GaussianL2) (hF : F ∈ singleGenerated u) :
    Tendsto (fun n => conditionalProjection (h n) F) atTop (𝓝 (meanProjection F)) := by
  have hp : Tendsto (fun n => sourceProjection (h n) u) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [conditional_firstChaos_projection, LinearIsometry.norm_map, norm_zero] using hu.norm
  exact single_tendsto h u hp F hF

theorem persistent_single_constant (u : CoefficientSpace)
    (hu : Tendsto (fun n => sourceProjection (h n) u) atTop (𝓝 0))
    (F : GaussianL2) (hF : F ∈ singleGenerated u) (hp : ∀ n, F ∈ generated (h n)) :
    F = (∫ ω, F ω ∂gaussianProduct) • gaussianOne := by
  have he (n : ℕ) : conditionalProjection (h n) F = F :=
    (generated (h n)).starProjection_eq_self_iff.mpr (hp n)
  have ht := single_tendsto h u hu F hF
  simp only [he, meanProjection_apply] at ht
  exact tendsto_nhds_unique tendsto_const_nhds ht

end OperatorDerivativeRewrite.Foundation.GaussianVanishingPrediction
