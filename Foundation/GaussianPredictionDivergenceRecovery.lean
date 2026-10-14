import Foundation.GaussianTerminalPredictionSpectrum
import Foundation.GaussianDivergenceRecovery

/-! Conditional prediction contracts the minimal full source-divergence
primitive; terminal chaos rank quantifies the contraction. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianPredictionDivergenceRecovery
open InfiniteGaussian GaussianNumberSectors GaussianConditionalGraph
open GaussianWickConditionalProjection GaussianSingleObservationPrediction GaussianTerminalPredictionSpectrum
open GaussianDivergenceRecovery

theorem conditional_recovery_norm_le {I : Type*} (h : I → CoefficientSpace) (f : GaussianL2) :
    ‖recovery (conditionalProjection h f)‖ ≤ ‖recovery f‖ := by
  have hl (n : ℕ) : (n : ℝ)⁻¹*‖projection n (conditionalProjection h f)‖^2 ≤
      (n : ℝ)⁻¹*‖projection n f‖^2 := by
    rw [projection_conditional_commute]
    exact mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (conditionalProjection_norm_le h _))
      (inv_nonneg.mpr (Nat.cast_nonneg n))
  have hs := hasSum_le hl (recovery_inverse_energy_hasSum (conditionalProjection h f))
    (recovery_inverse_energy_hasSum f)
  nlinarith [norm_nonneg (recovery (conditionalProjection h f)),norm_nonneg (recovery f)]

theorem terminal_recovery_energy_hasSum (u : CoefficientSpace) (hu : ‖u‖^2=1)
    (f : GaussianL2) (hf : f∈singleGenerated u) :
    HasSum (fun n : ℕ => (n : ℝ)⁻¹*(coefficient u f n)^2*(n.factorial : ℝ)) (‖recovery f‖^2) := by
  have he := recovery_inverse_energy_hasSum f
  simp only [terminal_projection u hu f hf,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,
    GaussianWickContinuity.wick_norm_sq,hu,one_pow,mul_one] at he
  simpa only [mul_assoc] using he

theorem terminal_prediction_recovery_energy_hasSum {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) (hu : ‖u‖^2=1) (f : GaussianL2) (hf : f∈singleGenerated u) :
    HasSum (fun n : ℕ => (n : ℝ)⁻¹*(coefficient u f n)^2*(n.factorial : ℝ)*
      (‖sourceProjection h u‖^2)^n) (‖recovery (conditionalProjection h f)‖^2) := by
  have hp (n : ℕ) : projection n (conditionalProjection h f)=
      coefficient u f n • (GaussianTimeSpaceHermite.wick (sourceProjection h u) n : GaussianL2) := by
    rw [projection_conditional_commute,terminal_projection u hu f hf,map_smul,
      conditional_wick_projection]
  have he := recovery_inverse_energy_hasSum (conditionalProjection h f)
  simp only [hp,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,
    GaussianWickContinuity.wick_norm_sq] at he
  simpa only [mul_assoc] using he

theorem terminal_recovery_rank_upper {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) (hu : ‖u‖^2=1) (f : GaussianL2) (hf : f∈singleGenerated u)
    (m : ℕ) (hrank : ∀ n, n<m → coefficient u f n=0) :
    ‖recovery (conditionalProjection h f)‖^2 ≤
      (‖sourceProjection h u‖^2)^m*‖recovery f‖^2 := by
  have hv : ‖sourceProjection h u‖^2 ≤ 1 := by
    rw [← hu]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      ((sourceSpan h).norm_starProjection_apply_le u)
  apply hasSum_le _ (terminal_prediction_recovery_energy_hasSum h u hu f hf)
    ((terminal_recovery_energy_hasSum u hu f hf).mul_left ((‖sourceProjection h u‖^2)^m))
  intro n
  by_cases hn : n<m
  · simp [hrank n hn]
  · have hp := pow_le_pow_of_le_one (sq_nonneg ‖sourceProjection h u‖) hv (Nat.le_of_not_gt hn)
    have hc : 0 ≤ (n : ℝ)⁻¹*(coefficient u f n)^2*(n.factorial : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hp hc]

end OperatorDerivativeRewrite.Foundation.GaussianPredictionDivergenceRecovery

