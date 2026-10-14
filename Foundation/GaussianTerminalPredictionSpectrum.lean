import Foundation.GaussianSingleObservationPrediction
import Foundation.GaussianPolynomialPredictionRank

/-! The full terminal L2 prediction spectrum, with actual Gaussian chaos
projections and no assumed Hermite expansion or density hypothesis. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianTerminalPredictionSpectrum
open InfiniteGaussian GaussianTimeSpaceHermite GaussianNumberSectors IBMCubicFirstChaos
open GaussianConditionalGraph GaussianWickConditionalProjection GaussianSingleObservationPrediction

def coefficient (u : CoefficientSpace) (f : GaussianL2) (n : ℕ) : ℝ :=
  inner ℝ (wick u n : GaussianL2) f/(n.factorial : ℝ)

def rankProjection (u : CoefficientSpace) (n : ℕ) : GaussianL2 →L[ℝ] GaussianL2 :=
  (n.factorial : ℝ)⁻¹ • (innerSL ℝ (wick u n : GaussianL2)).smulRight (wick u n : GaussianL2)

theorem rankProjection_apply (u : CoefficientSpace) (n : ℕ) (f : GaussianL2) :
    rankProjection u n f=coefficient u f n • (wick u n : GaussianL2) := by
  simp [rankProjection,coefficient,div_eq_mul_inv,smul_smul,mul_comm]

theorem projection_wick (u : CoefficientSpace) (n m : ℕ) :
    projection n (wick u m : GaussianL2)=if n=m then (wick u m : GaussianL2) else 0 := by
  by_cases hn : n=m
  · subst m
    rw [if_pos rfl]
    exact projection_fix n ⟨_,wick_mem_sector u n⟩
  · rw [if_neg hn]
    change (sector n).starProjection (wick u m : GaussianL2)=0
    apply (sector n).eq_starProjection_of_mem_of_inner_eq_zero (sector n).zero_mem
    intro w hw
    rw [sub_zero]
    exact sectors_orthogonal (Ne.symm hn) ⟨_,wick_mem_sector u m⟩ ⟨w,hw⟩

theorem terminal_projection (u : CoefficientSpace) (hu : ‖u‖^2=1)
    (f : GaussianL2) (hf : f∈singleGenerated u) (n : ℕ) :
    projection n f=coefficient u f n • (wick u n : GaussianL2) := by
  let L := projection n-rankProjection u n
  have hs : wickSpan u≤L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨m,rfl⟩
    change projection n (wick u m : GaussianL2)-rankProjection u n (wick u m : GaussianL2)=0
    rw [projection_wick,rankProjection_apply,coefficient,wick_inner,
      real_inner_self_eq_norm_sq,hu,one_pow]
    by_cases hn : n=m
    · subst m
      simp [show (n.factorial : ℝ)≠0 by positivity]
    · simp [hn]
  have hc := (wickSpan u).topologicalClosure_minimal hs L.isClosed_ker
  rw [wickSpan_closure] at hc
  have he := hc hf
  change projection n f-rankProjection u n f=0 at he
  rw [rankProjection_apply] at he
  exact sub_eq_zero.mp he

theorem terminal_expansion_hasSum (u : CoefficientSpace) (hu : ‖u‖^2=1)
    (f : GaussianL2) (hf : f∈singleGenerated u) :
    HasSum (fun n => coefficient u f n • (wick u n : GaussianL2)) f := by
  simpa only [terminal_projection u hu f hf] using projection_hasSum f

theorem terminal_prediction_expansion {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) (hu : ‖u‖^2=1) (f : GaussianL2) (hf : f∈singleGenerated u) :
    HasSum (fun n => coefficient u f n • (wick (sourceProjection h u) n : GaussianL2))
      (conditionalProjection h f) := by
  simpa only [map_smul,conditional_wick_projection] using
    (conditionalProjection h).hasSum (terminal_expansion_hasSum u hu f hf)

theorem terminal_prediction_energy_hasSum {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) (hu : ‖u‖^2=1) (f : GaussianL2) (hf : f∈singleGenerated u) :
    HasSum (fun n => (coefficient u f n)^2*(n.factorial : ℝ)*(‖sourceProjection h u‖^2)^n)
      (‖conditionalProjection h f‖^2) := by
  have hp (n : ℕ) : projection n (conditionalProjection h f)=
      coefficient u f n • (wick (sourceProjection h u) n : GaussianL2) := by
    rw [projection_conditional_commute,terminal_projection u hu f hf,map_smul,
      conditional_wick_projection]
  have he := projection_hasSum_norm_sq (conditionalProjection h f)
  simp only [hp,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,
    GaussianWickContinuity.wick_norm_sq] at he
  simpa only [mul_assoc] using he

theorem terminal_energy_hasSum (u : CoefficientSpace) (hu : ‖u‖^2=1)
    (f : GaussianL2) (hf : f∈singleGenerated u) :
    HasSum (fun n => (coefficient u f n)^2*(n.factorial : ℝ)) (‖f‖^2) := by
  have he := projection_hasSum_norm_sq f
  simp only [terminal_projection u hu f hf,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,
    GaussianWickContinuity.wick_norm_sq,hu,one_pow,mul_one] at he
  exact he

theorem terminal_prediction_rank_upper {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) (hu : ‖u‖^2=1) (f : GaussianL2) (hf : f∈singleGenerated u)
    (m : ℕ) (hrank : ∀ n, n<m → coefficient u f n=0) :
    ‖conditionalProjection h f‖^2 ≤ (‖sourceProjection h u‖^2)^m*‖f‖^2 := by
  have hv : ‖sourceProjection h u‖^2 ≤ 1 := by
    rw [← hu]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      ((sourceSpan h).norm_starProjection_apply_le u)
  apply hasSum_le _ (terminal_prediction_energy_hasSum h u hu f hf)
    ((terminal_energy_hasSum u hu f hf).mul_left ((‖sourceProjection h u‖^2)^m))
  intro n
  by_cases hn : n<m
  · simp [hrank n hn]
  · have hp := pow_le_pow_of_le_one (sq_nonneg ‖sourceProjection h u‖) hv (Nat.le_of_not_gt hn)
    have hc : 0 ≤ (coefficient u f n)^2*(n.factorial : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hp hc]

theorem terminal_prediction_rank_lower {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) (hu : ‖u‖^2=1) (f : GaussianL2) (hf : f∈singleGenerated u) (m : ℕ) :
    (coefficient u f m)^2*(m.factorial : ℝ)*(‖sourceProjection h u‖^2)^m ≤
      ‖conditionalProjection h f‖^2 := by
  have hs := terminal_prediction_energy_hasSum h u hu f hf
  have hl := hs.summable.sum_le_tsum ({m} : Finset ℕ) (fun n hn => by positivity)
  simpa only [Finset.sum_singleton,hs.tsum_eq] using hl

end OperatorDerivativeRewrite.Foundation.GaussianTerminalPredictionSpectrum
