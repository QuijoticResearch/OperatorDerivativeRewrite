import Foundation.IBMOriginalBoundaryResidual

/-! Uniform smoothing of genuine scenery expectations and their actual clock
occupation integrals. This controls the entire clock L² space at once. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMAveragedBulkClock
open InfiniteGaussian GaussianLipschitzIntegrands GaussianDeterministicGraphCore
open IBMContinuousScenery IBMBoundaryAveragedCoefficient IBMConstructedSources IBMMollifier
variable {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ)

def baseAverage (r : ℝ) : ℝ := inner ℝ gaussianOne (composition hφ (sourceScenery r))

theorem baseAverage_literal (r : ℝ) :
    baseAverage hφ r = ∫ ω, φ (sourceScenery r ω) ∂gaussianProduct := by
  rw [baseAverage, gaussianOne_inner_eq_integral,
    integral_congr_ae (composition_coeFn hφ _)]

theorem baseAverage_continuous : Continuous (baseAverage hφ) :=
  (innerSL ℝ gaussianOne).continuous.comp ((composition_continuous hφ).comp sourceScenery_continuous)

theorem average_eq_pairing (n : ℕ) (r : ℝ) :
    sourceAverage hφ n r = inner ℝ gaussianOne (composition hφ (wholeLineScenery (kernel n) r)) := by
  rw [sourceAverage_eq_integral, gaussianOne_inner_eq_integral,
    integral_congr_ae (composition_coeFn hφ _)]

theorem average_error (n : ℕ) (r : ℝ) :
    ‖sourceAverage hφ n r - baseAverage hφ r‖ ≤ (K : ℝ) * Real.sqrt (bump n).rOut := by
  have ho : ‖gaussianOne‖ = 1 := by
    have he := gaussianOne_inner_self
    rw [real_inner_self_eq_norm_sq] at he
    nlinarith [norm_nonneg gaussianOne]
  rw [average_eq_pairing, baseAverage, ← inner_sub_right]
  exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans (by
    rw [ho, one_mul]
    exact (composition_norm_sub_le hφ _ _).trans
      (mul_le_mul_of_nonneg_left (concreteMollifier_uniform_norm_le n r) K.coe_nonneg))

theorem baseAverage_bound {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) (r : ℝ) :
    ‖baseAverage hφ r‖ ≤ M := by
  rw [baseAverage_literal]
  simpa using norm_integral_le_of_norm_le_const
    (μ := gaussianProduct) (Filter.Eventually.of_forall fun ω => hM (sourceScenery r ω))

def clockIntegral (f : ℝ → ℝ) (T : ℝ≥0) (ω : SampleSpace) : ℝ :=
  ∫ t in 0..(T : ℝ), f |clockPath ω t.toNNReal|

theorem clockIntegral_measurable {f : ℝ → ℝ} (hf : Continuous f) (T : ℝ≥0) :
    StronglyMeasurable (clockIntegral f T) := by
  have he : Measurable (fun z : ℝ × SampleSpace => |clockPath z.2 z.1.toNNReal|) :=
    continuous_abs.measurable.comp (continuous_eval.measurable.comp
      ((clockPath_measurable.comp measurable_snd).prodMk
        (continuous_real_toNNReal.measurable.comp measurable_fst)))
  have hm := hf.measurable.comp he
  change StronglyMeasurable (fun ω => ∫ t in 0..(T : ℝ), _)
  simp only [intervalIntegral.integral_of_le T.coe_nonneg]
  exact hm.stronglyMeasurable.integral_prod_left'

theorem clockIntegral_bound {f : ℝ → ℝ} {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M)
    (T : ℝ≥0) (ω : SampleSpace) : ‖clockIntegral f T ω‖ ≤ M*T := by
  have he := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (T : ℝ)) (fun t _ => hM |clockPath ω t.toNNReal|)
  simpa only [clockIntegral, sub_zero, abs_of_nonneg T.coe_nonneg] using he

theorem clockIntegral_memLp {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ x, ‖f x‖ ≤ M) (T : ℝ≥0) : MemLp (clockIntegral f T) 2 gaussianProduct :=
  MemLp.of_bound (clockIntegral_measurable hf T).aestronglyMeasurable (M*T)
    (Eventually.of_forall fun ω => clockIntegral_bound hM T ω)

def clockClass {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ x, ‖f x‖ ≤ M) (T : ℝ≥0) : GaussianL2 :=
  (clockIntegral_memLp hf hM T).toLp _

theorem clockClass_coeFn {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ x, ‖f x‖ ≤ M) (T : ℝ≥0) :
    clockClass hf hM T =ᵐ[gaussianProduct] clockIntegral f T :=
  (clockIntegral_memLp hf hM T).coeFn_toLp

theorem clockClass_distance {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {M N e : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (hN : ∀ x, ‖g x‖ ≤ N)
    (he : ∀ x, ‖f x - g x‖ ≤ e) (T : ℝ≥0) :
    ‖clockClass hf hM T - clockClass hg hN T‖ ≤ e*T := by
  have hn : 0 ≤ e := (norm_nonneg (f 0-g 0)).trans (he 0)
  have hp (ω : SampleSpace) :
      ‖clockIntegral f T ω-clockIntegral g T ω‖ ≤ e*T := by
    have hc : Continuous (fun t : ℝ => |clockPath ω t.toNNReal|) :=
      continuous_abs.comp ((clockPath ω).continuous.comp continuous_real_toNNReal)
    have hi₁ : IntervalIntegrable (fun t : ℝ => f |clockPath ω t.toNNReal|) volume 0 T :=
      (hf.comp hc).intervalIntegrable 0 T
    have hi₂ : IntervalIntegrable (fun t : ℝ => g |clockPath ω t.toNNReal|) volume 0 T :=
      (hg.comp hc).intervalIntegrable 0 T
    rw [clockIntegral, clockIntegral, ← intervalIntegral.integral_sub hi₁ hi₂]
    exact clockIntegral_bound he T ω
  have hb : ∀ᵐ ω ∂gaussianProduct,
      ‖(clockClass hf hM T - clockClass hg hN T) ω‖ ≤ e*T := by
    filter_upwards [Lp.coeFn_sub (clockClass hf hM T) (clockClass hg hN T),
      clockClass_coeFn hf hM T, clockClass_coeFn hg hN T] with ω hs hf hg
    simp only [hs, Pi.sub_apply, hf, hg]
    exact hp ω
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (mul_nonneg hn T.coe_nonneg) hb

theorem bulkClass_tendsto {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) (T : ℝ≥0) :
    Tendsto (fun n => clockClass (sourceAverage_continuous hφ n)
      (IBMBoundaryLayerRemainder.sourceAverage_bound hφ hM n) T) atTop
      (𝓝 (clockClass (baseAverage_continuous hφ) (baseAverage_bound hφ hM) T)) := by
  have he : Tendsto (fun n => ((K : ℝ)*Real.sqrt (bump n).rOut)*T) atTop (𝓝 0) := by
    have hr := Real.continuous_sqrt.continuousAt.tendsto.comp bump_outer_tendsto_zero
    simpa only [Function.comp_apply, Real.sqrt_zero, mul_zero, zero_mul] using
      (hr.const_mul (K : ℝ)).mul_const (T : ℝ)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _) (fun n =>
    clockClass_distance (sourceAverage_continuous hφ n) (baseAverage_continuous hφ)
      (IBMBoundaryLayerRemainder.sourceAverage_bound hφ hM n)
      (baseAverage_bound hφ hM) (average_error hφ n) T) he

end OperatorDerivativeRewrite.Foundation.IBMAveragedBulkClock
