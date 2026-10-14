import Foundation.GaussianTerminalPredictionSpectrum

/-! A quantitative leading-rank remainder for arbitrary terminal L2 predictions. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianPredictionRankAsymptotic
open InfiniteGaussian GaussianConditionalGraph GaussianWickConditionalProjection
open GaussianSingleObservationPrediction GaussianTerminalPredictionSpectrum

theorem leading_rank_remainder {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) (hu : ‖u‖^2=1) (f : GaussianL2) (hf : f∈singleGenerated u)
    (m : ℕ) (hrank : ∀ n, n<m → coefficient u f n=0) :
    0≤‖conditionalProjection h f‖^2-(coefficient u f m)^2*(m.factorial : ℝ)*(‖sourceProjection h u‖^2)^m ∧
    ‖conditionalProjection h f‖^2-(coefficient u f m)^2*(m.factorial : ℝ)*(‖sourceProjection h u‖^2)^m
      ≤(‖sourceProjection h u‖^2)^(m+1)*‖f‖^2 := by
  let v := ‖sourceProjection h u‖^2
  let A := fun n => (coefficient u f n)^2*(n.factorial : ℝ)
  have hv0 : 0≤v := sq_nonneg _
  have hv1 : v≤1 := by
    rw [← hu]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      ((sourceSpan h).norm_starProjection_apply_le u)
  have hs := terminal_prediction_energy_hasSum h u hu f hf
  have hb := (hasSum_ite_eq m (A m*v^m)).add
    ((terminal_energy_hasSum u hu f hf).mul_left (v^(m+1)))
  have he : ‖conditionalProjection h f‖^2≤A m*v^m+v^(m+1)*‖f‖^2 := by
    apply hasSum_le _ hs hb
    intro n
    change A n*v^n≤(if n=m then A m*v^m else 0)+v^(m+1)*A n
    by_cases hn : n<m
    · have hz : A n=0 := by simp [A,hrank n hn]
      simp only [hz,zero_mul,mul_zero,add_zero]
      split_ifs <;> positivity
    · by_cases he : n=m
      · subst n
        simp only [ite_true]
        have hp : 0≤v^(m+1)*A m := by dsimp [A]; positivity
        linarith
      · rw [if_neg he,zero_add]
        have hmn : m+1≤n := by omega
        have hp := pow_le_pow_of_le_one hv0 hv1 hmn
        have hA : 0≤A n := by dsimp [A]; positivity
        nlinarith [mul_le_mul_of_nonneg_left hp hA]
  have hl := terminal_prediction_rank_lower h u hu f hf m
  constructor
  · linarith
  · change ‖conditionalProjection h f‖^2-A m*v^m≤v^(m+1)*‖f‖^2
    linarith

theorem normalized_rank_remainder {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) (hu : ‖u‖^2=1) (f : GaussianL2) (hf : f∈singleGenerated u)
    (m : ℕ) (hrank : ∀ n, n<m → coefficient u f n=0)
    (hv : 0<‖sourceProjection h u‖^2) :
    0≤‖conditionalProjection h f‖^2/(‖sourceProjection h u‖^2)^m-
      (coefficient u f m)^2*(m.factorial : ℝ) ∧
    ‖conditionalProjection h f‖^2/(‖sourceProjection h u‖^2)^m-
      (coefficient u f m)^2*(m.factorial : ℝ)≤‖sourceProjection h u‖^2*‖f‖^2 := by
  obtain ⟨hl,he⟩ := leading_rank_remainder h u hu f hf m hrank
  have hp : 0<(‖sourceProjection h u‖^2)^m := pow_pos hv m
  constructor
  · have h1 := (le_div_iff₀ hp).mpr (show
        (coefficient u f m)^2*(m.factorial : ℝ)*(‖sourceProjection h u‖^2)^m≤
          ‖conditionalProjection h f‖^2 by linarith)
    linarith
  · have h1 : ‖conditionalProjection h f‖^2≤
        ((coefficient u f m)^2*(m.factorial : ℝ)+‖sourceProjection h u‖^2*‖f‖^2)*
          (‖sourceProjection h u‖^2)^m := by
      rw [pow_succ (‖sourceProjection h u‖^2) m] at he
      nlinarith [he]
    have h2 := (div_le_iff₀ hp).mpr h1
    linarith

theorem leading_rank_limit {X I : Type*} (l : Filter X) (h : X → I → CoefficientSpace)
    (u : CoefficientSpace) (hu : ‖u‖^2=1) (f : GaussianL2) (hf : f∈singleGenerated u)
    (m : ℕ) (hrank : ∀ n, n<m → coefficient u f n=0)
    (hv0 : Tendsto (fun x => ‖sourceProjection (h x) u‖^2) l (𝓝 0))
    (hvpos : ∀ᶠ x in l, 0<‖sourceProjection (h x) u‖^2) :
    Tendsto (fun x => ‖conditionalProjection (h x) f‖^2/(‖sourceProjection (h x) u‖^2)^m)
      l (𝓝 ((coefficient u f m)^2*(m.factorial : ℝ))) := by
  have hb := hvpos.mono (fun x hx => normalized_rank_remainder (h x) u hu f hf m hrank hx)
  have ht := squeeze_zero' (hb.mono fun x hx => hx.1) (hb.mono fun x hx => hx.2)
    (by simpa only [zero_mul] using hv0.mul_const (‖f‖^2))
  convert ht.add_const ((coefficient u f m)^2*(m.factorial : ℝ)) using 1
  · funext x; ring
  · congr 1; ring
end OperatorDerivativeRewrite.Foundation.GaussianPredictionRankAsymptotic




