import Foundation.GaussianLipschitzIntegrands
import Foundation.BochnerL2Approximation

/-! Actual bounded Brownian compositions and dominated limits of their drifts. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianBoundedApproximation
open InfiniteGaussian GaussianTimeProcess GaussianLipschitzIntegrands

variable {φ : ℝ → ℝ} {M : ℝ}

theorem bounded_memLp (hφ : Continuous φ) (hM : ∀ x, ‖φ x‖ ≤ M) (t : ℝ≥0) :
    MemLp (fun ω => φ (process t ω)) 2 gaussianProduct :=
  MemLp.of_bound (hφ.comp_stronglyMeasurable (process_stronglyMeasurable t)).aestronglyMeasurable
    M (Eventually.of_forall fun ω => hM _)

def boundedValue (hφ : Continuous φ) (hM : ∀ x, ‖φ x‖ ≤ M) (t : ℝ≥0) : GaussianL2 :=
  (bounded_memLp hφ hM t).toLp _

theorem boundedValue_coeFn (hφ : Continuous φ) (hM : ∀ x, ‖φ x‖ ≤ M) (t : ℝ≥0) :
    boundedValue hφ hM t =ᵐ[gaussianProduct] fun ω => φ (process t ω) := MemLp.coeFn_toLp _

theorem gaussian_norm_le {A : GaussianL2} {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ᵐ ω ∂gaussianProduct, ‖A ω‖ ≤ C) : ‖A‖ ≤ C := by
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hC hA

theorem boundedValue_norm_le (hφ : Continuous φ) (hM : ∀ x, ‖φ x‖ ≤ M) (t : ℝ≥0) :
    ‖boundedValue hφ hM t‖ ≤ M := by
  apply gaussian_norm_le ((norm_nonneg _).trans (hM 0))
  filter_upwards [boundedValue_coeFn hφ hM t] with ω hω
  rw [hω]
  exact hM _

theorem value_norm_le {K : ℝ≥0} (hφ : LipschitzWith K φ) (hM : ∀ x, ‖φ x‖ ≤ M)
    (t : ℝ≥0) : ‖valueL2 hφ t‖ ≤ M := by
  apply gaussian_norm_le ((norm_nonneg _).trans (hM 0))
  filter_upwards [valueL2_coeFn hφ t] with ω hω
  rw [hω]
  exact hM _

theorem values_tendsto (φn : ℕ → ℝ → ℝ) (Kn : ℕ → ℝ≥0)
    (hn : ∀ n, LipschitzWith (Kn n) (φn n)) (hφ : Continuous φ)
    (hM : ∀ x, ‖φ x‖ ≤ M) (hMn : ∀ n x, ‖φn n x‖ ≤ M)
    (ht : ∀ x, Tendsto (fun n => φn n x) atTop (𝓝 (φ x))) (t : ℝ≥0) :
    Tendsto (fun n => valueL2 (hn n) t) atTop (𝓝 (boundedValue hφ hM t)) := by
  apply BochnerL2Approximation.tendsto_of_dominated _ _ (M • gaussianOne)
  · intro n
    filter_upwards [valueL2_coeFn (hn n) t, Lp.coeFn_smul M gaussianOne, gaussianOne_coeFn]
      with ω hv hs ho
    simp only [hv, hs, Pi.smul_apply, ho, smul_eq_mul, mul_one]
    exact (hMn n _).trans (le_abs_self M)
  · filter_upwards [boundedValue_coeFn hφ hM t, Lp.coeFn_smul M gaussianOne, gaussianOne_coeFn]
      with ω hv hs ho
    simp only [hv, hs, Pi.smul_apply, ho, smul_eq_mul, mul_one]
    exact (hM _).trans (le_abs_self M)
  · filter_upwards [ae_all_iff.mpr (fun n => valueL2_coeFn (hn n) t), boundedValue_coeFn hφ hM t]
      with ω hn hg
    simpa only [hn, hg] using ht (process t ω)

theorem value_uniform_error {ψ : ℝ → ℝ} {K L : ℝ≥0} (hφ : LipschitzWith K φ)
    (hψ : LipschitzWith L ψ) {e : ℝ} (he : 0 ≤ e) (h : ∀ x, ‖φ x-ψ x‖ ≤ e) (t : ℝ≥0) :
    ‖valueL2 hφ t-valueL2 hψ t‖ ≤ e := by
  apply gaussian_norm_le he
  filter_upwards [Lp.coeFn_sub (valueL2 hφ t) (valueL2 hψ t), valueL2_coeFn hφ t,
    valueL2_coeFn hψ t] with ω hs h1 h2
  simpa only [hs, Pi.sub_apply, h1, h2] using h (process t ω)

/-- No continuity of the limiting curve is assumed: measurability and actual
integrability follow from its pointwise L2 limits and the common norm bound. -/
theorem drift_tendsto (v : ℕ → ℝ≥0 → GaussianL2) (hv : ∀ n, Continuous (v n))
    (w : ℝ≥0 → GaussianL2) (ht : ∀ t, Tendsto (fun n => v n t) atTop (𝓝 (w t)))
    (M : ℝ) (hM : ∀ n t, ‖v n t‖ ≤ M) (hw : ∀ t, ‖w t‖ ≤ M) (T : ℝ≥0) :
    IntervalIntegrable (fun t : ℝ => w t.toNNReal) volume 0 T ∧
    Tendsto (fun n => ∫ t in 0..(T:ℝ), v n t.toNNReal) atTop
      (𝓝 (∫ t in 0..(T:ℝ), w t.toNNReal)) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (T:ℝ))
  have hm : AEStronglyMeasurable (fun t : ℝ => w t.toNNReal) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => ((hv n).comp continuous_real_toNNReal).aestronglyMeasurable)
      (Eventually.of_forall fun t => ht t.toNNReal)
  have hi : Integrable (fun t : ℝ => w t.toNNReal) μ :=
    Integrable.mono' (integrable_const M) hm (Eventually.of_forall fun t => hw _)
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mpr hi, ?_⟩
  simp only [intervalIntegral.integral_of_le T.coe_nonneg]
  exact tendsto_integral_of_dominated_convergence (fun _ => M)
    (fun n => ((hv n).comp continuous_real_toNNReal).aestronglyMeasurable)
    (integrable_const M) (fun n => Eventually.of_forall fun t => hM n _)
    (Eventually.of_forall fun t => ht t.toNNReal)

open GaussianTimeProductL2 GaussianProductDerivative GaussianPredictableFull

theorem integrands_tendsto (φn : ℕ → ℝ → ℝ) (Kn : ℕ → ℝ≥0)
    (hn : ∀ n, LipschitzWith (Kn n) (φn n)) {K : ℝ≥0} (hφ : LipschitzWith K φ)
    (hM : ∀ x, ‖φ x‖ ≤ M) (hMn : ∀ n x, ‖φn n x‖ ≤ M)
    (ht : ∀ x, Tendsto (fun n => φn n x) atTop (𝓝 (φ x))) (T : ℝ≥0) :
    Tendsto (fun n => integrand (hn n) T) atTop (𝓝 (integrand hφ T)) := by
  have hc (t : ℝ≥0) : Tendsto (fun n => valueL2 (hn n) t) atTop (𝓝 (valueL2 hφ t)) := by
    have he : boundedValue hφ.continuous hM t = valueL2 hφ t := by
      apply Lp.ext
      exact (boundedValue_coeFn hφ.continuous hM t).trans (valueL2_coeFn hφ t).symm
    simpa only [he] using values_tendsto φn Kn hn hφ.continuous hM hMn ht t
  let b : Lp ℝ 2 volume :=
    (GaussianHermiteTimeKernel.continuous_interval_memLp (fun _ : ℝ => M) continuous_const T).toLp _
  have hb : b =ᵐ[volume] (Ioc 0 (T:ℝ)).indicator (fun _ => M) := MemLp.coeFn_toLp _
  have hh := BochnerL2Approximation.tendsto_of_dominated
    (fun n => scalarCurry (integrand (hn n) T : TimeProbabilityL2))
    (scalarCurry (integrand hφ T : TimeProbabilityL2)) b ?_ ?_ ?_
  · apply tendsto_subtype_rng.mpr
    simpa only [Function.comp_def, scalarCurry.symm_apply_apply] using
      scalarCurry.symm.continuous.continuousAt.tendsto.comp hh
  · intro n
    filter_upwards [integrand_slices (hn n) T, hb] with t hv hb
    rw [hv, hb]
    by_cases hm : t ∈ Ioc 0 (T:ℝ)
    · simp only [indicator_of_mem hm]
      exact (value_norm_le (hn n) (hMn n) _).trans (le_abs_self M)
    · simp [hm]
  · filter_upwards [integrand_slices hφ T, hb] with t hv hb
    rw [hv, hb]
    by_cases hm : t ∈ Ioc 0 (T:ℝ)
    · simp only [indicator_of_mem hm]
      exact (value_norm_le hφ hM _).trans (le_abs_self M)
    · simp [hm]
  · filter_upwards [ae_all_iff.mpr (fun n => integrand_slices (hn n) T), integrand_slices hφ T]
      with t hn hg
    simp only [hn, hg]
    by_cases hm : t ∈ Ioc 0 (T:ℝ)
    · simpa only [indicator_of_mem hm] using hc t.toNNReal
    · simpa only [indicator_of_notMem hm] using (tendsto_const_nhds (x := (0:GaussianL2)))

end OperatorDerivativeRewrite.Foundation.GaussianBoundedApproximation


