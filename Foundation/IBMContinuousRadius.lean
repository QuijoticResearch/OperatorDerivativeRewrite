import Foundation.IBMContinuousCovariance

/-! Quantitative source-first approximation by positive compact kernels. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace OperatorDerivativeRewrite.Foundation.IBMContinuousScenery
open InfiniteGaussian GaussianHilbertProcess FractionalSpectralKernel
open IBMFiniteScenerySmoothing
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

/-- A positive mass-one continuous kernel supported in a spatial radius `δ`
approximates the original Brownian Hilbert direction by at most `√δ`. -/
theorem kernelDirection_error_le (a b x δ : ℝ) {ρ : ℝ → ℝ}
    (hρ : Continuous ρ)
    (hmass : (∫ r in Set.Icc a b, ρ (x - r)) = 1)
    (hw : ∀ r ∈ Set.Icc a b, 0 ≤ ρ (x - r))
    (hδ : 0 ≤ δ) (hradius : ∀ r ∈ Set.Icc a b, |r - x| ≤ δ) :
    ‖kernelDirection a b x ρ - direction x‖ ≤ Real.sqrt δ := by
  have hc : Continuous (fun r : ℝ => ρ (x - r)) :=
    hρ.comp (continuous_const.sub continuous_id)
  have hconst : IntegrableOn (fun r : ℝ => ρ (x - r) • direction x)
      (Set.Icc a b) volume :=
    (hc.smul continuous_const).integrableOn_Icc
  have heq : kernelDirection a b x ρ - direction x =
      ∫ r in Set.Icc a b, ρ (x - r) • (direction r - direction x) := by
    have hbase : (∫ r in Set.Icc a b, ρ (x - r) • direction x) = direction x := by
      rw [integral_smul_const, hmass, one_smul]
    rw [kernelDirection]
    nth_rewrite 1 [← hbase]
    rw [← integral_sub (weightedDirection_integrableOn a b x hρ) hconst]
    congr 1
    funext r
    rw [smul_sub]
  have hmajor : IntegrableOn (fun r : ℝ => ρ (x - r) * Real.sqrt δ)
      (Set.Icc a b) volume :=
    (hc.mul continuous_const).integrableOn_Icc
  have hpoint (r : ℝ) (hr : r ∈ Set.Icc a b) :
      ‖direction r - direction x‖ ≤ Real.sqrt δ := by
    have hs := direction_increment_sq x r
    have hrad := hradius r hr
    have hroot := Real.sq_sqrt hδ
    have hn := norm_nonneg (direction r - direction x)
    have hsqr := Real.sqrt_nonneg δ
    nlinarith
  have hbound (r : ℝ) (hr : r ∈ Set.Icc a b) :
      ‖ρ (x - r) • (direction r - direction x)‖ ≤
        ρ (x - r) * Real.sqrt δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw r hr)]
    exact mul_le_mul_of_nonneg_left (hpoint r hr) (hw r hr)
  rw [heq]
  calc
    ‖∫ r in Set.Icc a b, ρ (x - r) • (direction r - direction x)‖ ≤
        ∫ r in Set.Icc a b, ρ (x - r) * Real.sqrt δ :=
      norm_integral_le_of_norm_le hmajor
        (ae_restrict_of_forall_mem measurableSet_Icc hbound)
    _ = Real.sqrt δ := by
      rw [integral_mul_const, hmass, one_mul]

/-- The same radius bound holds for the genuine Gaussian L² convolution. -/
theorem kernelScenery_error_sq_le (a b x δ : ℝ) {ρ : ℝ → ℝ}
    (hρ : Continuous ρ)
    (hmass : (∫ r in Set.Icc a b, ρ (x - r)) = 1)
    (hw : ∀ r ∈ Set.Icc a b, 0 ≤ ρ (x - r))
    (hδ : 0 ≤ δ) (hradius : ∀ r ∈ Set.Icc a b, |r - x| ≤ δ) :
    ‖kernelScenery a b x ρ - sourceScenery x‖ ^ 2 ≤ δ := by
  have hn := kernelDirection_error_le a b x δ hρ hmass hw hδ hradius
  have heq : ‖kernelScenery a b x ρ - sourceScenery x‖ =
      ‖kernelDirection a b x ρ - direction x‖ := by
    rw [kernelScenery_eq_embedding, sourceScenery,
      ← (isonormalEmbedding SpectralSpace).map_sub]
    exact (isonormalEmbedding SpectralSpace).norm_map _
  rw [heq]
  nlinarith [Real.sq_sqrt hδ,
    norm_nonneg (kernelDirection a b x ρ - direction x), Real.sqrt_nonneg δ]

/-- The continuous-kernel smoothing error has the exact Gaussian fourth moment. -/
theorem kernelScenery_error_fourth (a b x : ℝ) (ρ : ℝ → ℝ) :
    (∫ ω, (isonormal SpectralSpace (kernelDirection a b x ρ - direction x) ω)^4
      ∂gaussianProduct) =
      3 * (‖kernelDirection a b x ρ - direction x‖ ^ 2)^2 := by
  change (∫ ω, (firstChaosEmbedding
    (SeparableHilbertEmbedding.hilbertEmbedding SpectralSpace
      (kernelDirection a b x ρ - direction x)) ω)^4 ∂gaussianProduct) = _
  rw [IBMSourceMoments.firstChaos_fourth]
  rw [(SeparableHilbertEmbedding.hilbertEmbedding SpectralSpace).norm_map]

/-- A normalized positive continuous kernel of radius `δ` has fourth
Gaussian smoothing error at most `3δ²`. -/
theorem kernelScenery_error_fourth_le (a b x δ : ℝ) {ρ : ℝ → ℝ}
    (hρ : Continuous ρ)
    (hmass : (∫ r in Set.Icc a b, ρ (x - r)) = 1)
    (hw : ∀ r ∈ Set.Icc a b, 0 ≤ ρ (x - r))
    (hδ : 0 ≤ δ) (hradius : ∀ r ∈ Set.Icc a b, |r - x| ≤ δ) :
    (∫ ω, (isonormal SpectralSpace (kernelDirection a b x ρ - direction x) ω)^4
      ∂gaussianProduct) ≤ 3 * δ ^ 2 := by
  rw [kernelScenery_error_fourth]
  have hs : ‖kernelDirection a b x ρ - direction x‖ ^ 2 ≤ δ := by
    have h := kernelScenery_error_sq_le a b x δ hρ hmass hw hδ hradius
    simpa only [kernelScenery_eq_embedding, sourceScenery,
      ← (isonormalEmbedding SpectralSpace).map_sub,
      (isonormalEmbedding SpectralSpace).norm_map] using h
  nlinarith [sq_nonneg (‖kernelDirection a b x ρ - direction x‖ ^ 2 - δ)]

/-- Shrinking normalized positive continuous kernels converge to the
original source coordinate in Gaussian L², with no pathwise claim. -/
theorem kernelScenery_tendsto
    (a b δ : ℕ → ℝ) (ρ : ℕ → ℝ → ℝ) (x : ℝ)
    (hρ : ∀ n, Continuous (ρ n))
    (hmass : ∀ n, (∫ r in Set.Icc (a n) (b n), ρ n (x - r)) = 1)
    (hw : ∀ n r, r ∈ Set.Icc (a n) (b n) → 0 ≤ ρ n (x - r))
    (hδ : ∀ n, 0 ≤ δ n)
    (hradius : ∀ n r, r ∈ Set.Icc (a n) (b n) → |r - x| ≤ δ n)
    (hδlim : Filter.Tendsto δ Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => kernelScenery (a n) (b n) x (ρ n)) Filter.atTop
      (nhds (sourceScenery x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hroot : Filter.Tendsto (fun n => Real.sqrt (δ n)) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hδlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hroot
    (fun n => norm_nonneg _)
    (fun n => by
      have hn := kernelDirection_error_le (a n) (b n) x (δ n)
        (hρ n) (hmass n) (hw n) (hδ n) (hradius n)
      simpa only [kernelScenery_eq_embedding, sourceScenery,
        ← (isonormalEmbedding SpectralSpace).map_sub,
        (isonormalEmbedding SpectralSpace).norm_map] using hn)

end OperatorDerivativeRewrite.Foundation.IBMContinuousScenery
