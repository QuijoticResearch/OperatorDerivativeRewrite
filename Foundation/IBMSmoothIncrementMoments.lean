import Foundation.IBMJointMollifierGaussian
import Foundation.IBMSourceMoments
import Mathlib.Analysis.Calculus.MeanValue

/-! Fourth-moment spatial bounds for the actual Gaussian convolution classes.
These estimates do not assert the existence of a continuous modification. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace OperatorDerivativeRewrite.Foundation.IBMSmoothIncrementMoments
open InfiniteGaussian GaussianHilbertProcess SeparableHilbertEmbedding
open FractionalSpectralKernel IBMContinuousScenery IBMJointMollifierGaussian
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

/-- Fourth powers in the subsequent identities are genuinely integrable. -/
theorem convolution_increment_fourth_integrable (ρ : ℝ → ℝ) (s t : ℝ) :
    Integrable (fun ω => (isonormal SpectralSpace (wholeLineDirection ρ t) ω -
      isonormal SpectralSpace (wholeLineDirection ρ s) ω)^4) gaussianProduct := by
  have h := ((isonormal_memLp (wholeLineDirection ρ t) 4 (by norm_num)).sub
    (isonormal_memLp (wholeLineDirection ρ s) 4 (by norm_num))).integrable_norm_pow'
  simpa only [Pi.sub_apply, Real.norm_eq_abs, (show Even 4 by decide).pow_abs] using h

/-- Exact fourth moment for two observations of the actual convolution, without
any spatial regularity hypothesis on the kernel. -/
theorem convolution_increment_fourth (ρ : ℝ → ℝ) (s t : ℝ) :
    (∫ ω, (isonormal SpectralSpace (wholeLineDirection ρ t) ω -
      isonormal SpectralSpace (wholeLineDirection ρ s) ω)^4 ∂gaussianProduct) =
      3 * ‖wholeLineScenery ρ t - wholeLineScenery ρ s‖^4 := by
  have he : (fun ω => (isonormal SpectralSpace (wholeLineDirection ρ t) ω -
      isonormal SpectralSpace (wholeLineDirection ρ s) ω)^4) =ᵐ[gaussianProduct]
      (fun ω => (firstChaosEmbedding
        (hilbertEmbedding SpectralSpace
          (wholeLineDirection ρ t - wholeLineDirection ρ s)) ω)^4) := by
    filter_upwards [isonormal_sub_ae (wholeLineDirection ρ t) (wholeLineDirection ρ s)] with ω hω
    exact congrArg (fun z : ℝ => z^4) hω.symm
  rw [integral_congr_ae he, IBMSourceMoments.firstChaos_fourth]
  rw [(hilbertEmbedding SpectralSpace).norm_map,
    wholeLineScenery_eq_sourceEmbedding ρ t, wholeLineScenery_eq_sourceEmbedding ρ s,
    ← (isonormalEmbedding SpectralSpace).map_sub,
    (isonormalEmbedding SpectralSpace).norm_map]
  ring

/-- A compact derivative bound gives a fourth-power increment estimate,
with its coefficient displayed explicitly. -/
theorem convolution_increment_fourth_le {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ)
    {a b C : ℝ} (_hC : 0 ≤ C)
    (hbound : ∀ r ∈ Set.Icc a b, ‖wholeLineScenery (deriv ρ) r‖ ≤ C)
    {s t : ℝ} (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) :
    (∫ ω, (isonormal SpectralSpace (wholeLineDirection ρ t) ω -
      isonormal SpectralSpace (wholeLineDirection ρ s) ω)^4 ∂gaussianProduct) ≤
      3 * C^4 * |t-s|^4 := by
  have hn : ‖wholeLineScenery ρ t - wholeLineScenery ρ s‖ ≤ C * |t-s| := by
    simpa only [Real.norm_eq_abs, wholeLineScenery] using
      (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun r _ => (wholeLineScenery_hasDerivAt hc hρ r).hasDerivWithinAt)
        hbound hs ht
  rw [convolution_increment_fourth]
  calc
    3 * ‖wholeLineScenery ρ t - wholeLineScenery ρ s‖^4 ≤
        3 * (C * |t-s|)^4 := by gcongr
    _ = 3 * C^4 * |t-s|^4 := by ring

/-- The required derivative bound exists on every compact interval for each
compactly supported C² kernel. The constant is independent of both points. -/
theorem convolution_compact_increment_bound {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      (∫ ω, (isonormal SpectralSpace (wholeLineDirection ρ t) ω -
        isonormal SpectralSpace (wholeLineDirection ρ s) ω)^4 ∂gaussianProduct) ≤
        3 * C^4 * |t-s|^4 := by
  have hd : ContDiff ℝ 1 (deriv ρ) := (contDiff_succ_iff_deriv.mp hρ).2.2
  have hcont : Continuous (wholeLineScenery (deriv ρ)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (wholeLineScenery_hasDerivAt hc.deriv hd x).continuousAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro s hs t ht
  exact convolution_increment_fourth_le hc (hρ.of_le (by norm_num))
    (le_max_right _ _) (fun r hr => (hM r hr).trans (le_max_left _ _)) hs ht

/-- Each of the concrete normalized mollifier fields U, V and W has fourth
increment moments of order |t-s|⁴, uniformly on every compact interval. -/
theorem gaussianTriple_compact_increment_bound (n : ℕ) (i : Fin 3) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      (∫ ω, (gaussianTriple n t i ω - gaussianTriple n s i ω)^4 ∂gaussianProduct) ≤
        3 * C^4 * |t-s|^4 := by
  have hc : HasCompactSupport (derivativeKernel n i) := by
    unfold derivativeKernel
    split_ifs
    · exact IBMMollifier.kernel_compactSupport n
    · exact (IBMMollifier.kernel_compactSupport n).deriv
    · exact (IBMMollifier.kernel_compactSupport n).deriv.deriv
  have hρ : ContDiff ℝ 2 (derivativeKernel n i) := by
    have h := IBMMollifier.kernel_smooth n
    have h' := (contDiff_infty_iff_deriv.mp h).2
    have h'' := (contDiff_infty_iff_deriv.mp h').2
    unfold derivativeKernel
    split_ifs
    · exact h.of_le (by norm_num)
    · exact h'.of_le (by norm_num)
    · exact h''.of_le (by norm_num)
  exact convolution_compact_increment_bound hc hρ a b

end OperatorDerivativeRewrite.Foundation.IBMSmoothIncrementMoments


