import Foundation.IBMBoundaryWeightedClock
import Foundation.BrownianZeroOccupation

/-! The actual bounded, shrinking-layer remainder in the IBM boundary
coefficient decomposition. Its random L² limit is proved using the already
constructed Brownian clock, not an assumed spatial occupation density. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMBoundaryLayerRemainder
open InfiniteGaussian IBMConstructedSources IBMVarianceClockGeometry IBMMollifier
open IBMBoundaryAveragedCoefficient
variable {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ)

theorem sourceAverage_bound {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) (n : ℕ) (r : ℝ) :
    ‖sourceAverage hφ n r‖ ≤ M := by
  rw [sourceAverage_eq_integral]
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := gaussianProduct)
      (Eventually.of_forall fun ω => hM _)

def slopeFactor (n : ℕ) (r : ℝ) : ℝ := ((deriv (variance n) r)^2 - 1) / 4

theorem slopeFactor_continuous (n : ℕ) : Continuous (slopeFactor n) :=
  ((((variance_smooth n).continuous_deriv (by norm_num)).pow 2).sub continuous_const).div_const 4

theorem slopeFactor_bound (n : ℕ) (r : ℝ) : ‖slopeFactor n r‖ ≤ 1/4 := by
  have h := slope_bound n r
  rw [Real.norm_eq_abs] at h
  have hh := abs_le.mp h
  rw [slopeFactor, Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith [sq_nonneg (deriv (variance n) r)]

def residual (n : ℕ) (r : ℝ) : ℝ := slopeFactor n r * sourceAverage hφ n r

theorem residual_continuous (n : ℕ) : Continuous (residual hφ n) :=
  (slopeFactor_continuous n).mul (sourceAverage_continuous hφ n)

theorem residual_bound {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) (n : ℕ) (r : ℝ) :
    ‖residual hφ n r‖ ≤ M/4 := by
  rw [residual, norm_mul]
  calc
    _ ≤ (1/4 : ℝ) * M := mul_le_mul (slopeFactor_bound n r)
      (sourceAverage_bound hφ hM n r) (norm_nonneg _)
        (by norm_num)
    _ = _ := by ring

/-- At every nonzero point the actual slope is eventually exactly ±1. -/
theorem residual_eventually_zero (r : ℝ) (hr : r ≠ 0) :
    ∀ᶠ n in atTop, residual hφ n r = 0 := by
  filter_upwards [bump_outer_tendsto_zero.eventually (eventually_lt_nhds (abs_pos.mpr hr))]
    with n hn
  rcases lt_or_gt_of_ne hr with hneg | hpos
  · rw [abs_of_neg hneg] at hn
    unfold residual slopeFactor variance
    rw [IBMNegativeBulkVariance.concrete_negative_variance_deriv n r (by linarith)]
    norm_num
  · rw [abs_of_pos hpos] at hn
    unfold residual slopeFactor variance
    rw [IBMOffsetTranslation.concrete_wholeLineVariance_deriv n r hn]
    norm_num

def pathIntegral (n : ℕ) (T : ℝ≥0) (ω : SampleSpace) : ℝ :=
  ∫ t in 0..(T : ℝ), residual hφ n |clockPath ω t.toNNReal|

theorem integrand_continuous (n : ℕ) (ω : SampleSpace) :
    Continuous (fun t : ℝ => residual hφ n |clockPath ω t.toNNReal|) :=
  (residual_continuous hφ n).comp
    (continuous_abs.comp ((clockPath ω).continuous.comp continuous_real_toNNReal))

theorem pathIntegral_stronglyMeasurable (n : ℕ) (T : ℝ≥0) :
    StronglyMeasurable (pathIntegral hφ n T) := by
  have he : Measurable (fun z : ℝ × SampleSpace => |clockPath z.2 z.1.toNNReal|) :=
    continuous_abs.measurable.comp (continuous_eval.measurable.comp
      ((clockPath_measurable.comp measurable_snd).prodMk
        (continuous_real_toNNReal.measurable.comp measurable_fst)))
  have hm := (residual_continuous hφ n).measurable.comp he
  change StronglyMeasurable (fun ω => ∫ t in 0..(T : ℝ), _)
  simp only [intervalIntegral.integral_of_le T.coe_nonneg]
  exact hm.stronglyMeasurable.integral_prod_left'

theorem pathIntegral_bound {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M)
    (n : ℕ) (T : ℝ≥0) (ω : SampleSpace) : ‖pathIntegral hφ n T ω‖ ≤ (M/4) * T := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (T : ℝ)) (fun t _ => residual_bound hφ hM n |clockPath ω t.toNNReal|)
  simpa only [sub_zero, abs_of_nonneg T.coe_nonneg, pathIntegral] using h

/-- Actual time integrals vanish along almost every constructed Brownian
path; the nonzero-time event is already verified independently. -/
theorem pathIntegral_tendsto_ae {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) (T : ℝ≥0) :
    ∀ᵐ ω ∂gaussianProduct, Tendsto (fun n => pathIntegral hφ n T ω) atTop (𝓝 0) := by
  filter_upwards [BrownianZeroOccupation.zero_time_ae T] with ω hω
  have h := tendsto_integral_of_dominated_convergence (fun _ : ℝ => M/4)
    (μ := volume.restrict (Ioc 0 (T : ℝ)))
    (F := fun n t => residual hφ n |clockPath ω t.toNNReal|) (f := fun _ => (0 : ℝ))
    (fun n => (integrand_continuous hφ n ω).aestronglyMeasurable)
    (integrable_const _) (fun n => Eventually.of_forall fun t => residual_bound hφ hM n _)
    (hω.mono fun t ht => by
      have he : (fun n : ℕ => residual hφ n |clockPath ω t.toNNReal|) =ᶠ[atTop]
          (fun _ => (0 : ℝ)) := residual_eventually_zero hφ _ (abs_ne_zero.mpr ht)
      exact tendsto_const_nhds.congr' he.symm)
  simpa only [pathIntegral, intervalIntegral.integral_of_le T.coe_nonneg, integral_zero] using h

theorem pathIntegral_memLp {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) (n : ℕ) (T : ℝ≥0) :
    MemLp (pathIntegral hφ n T) 2 gaussianProduct :=
  MemLp.of_bound (pathIntegral_stronglyMeasurable hφ n T).aestronglyMeasurable
    ((M/4)*T) (Eventually.of_forall fun ω => pathIntegral_bound hφ hM n T ω)

def integralClass {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) (n : ℕ) (T : ℝ≥0) : GaussianL2 :=
  (pathIntegral_memLp hφ hM n T).toLp _

theorem integralClass_coeFn {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) (n : ℕ) (T : ℝ≥0) :
    integralClass hφ hM n T =ᵐ[gaussianProduct] pathIntegral hφ n T :=
  (pathIntegral_memLp hφ hM n T).coeFn_toLp

/-- Strong random L² convergence of the actual bounded layer remainder. -/
theorem integralClass_tendsto {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) (T : ℝ≥0) :
    Tendsto (fun n => integralClass hφ hM n T) atTop (𝓝 0) := by
  apply BochnerL2Approximation.tendsto_of_dominated _ _ (((M/4)*T : ℝ) • gaussianOne)
  · intro n
    filter_upwards [integralClass_coeFn hφ hM n T,
      Lp.coeFn_smul (((M/4)*T : ℝ)) gaussianOne, gaussianOne_coeFn]
      with ω hf hs ho
    simp only [hf, hs, Pi.smul_apply, smul_eq_mul, ho, mul_one, Real.norm_eq_abs]
    exact (pathIntegral_bound hφ hM n T ω).trans (le_abs_self _)
  · filter_upwards [Lp.coeFn_zero ℝ 2 gaussianProduct] with ω hz
    simp only [hz, Pi.zero_apply, norm_zero]
    exact norm_nonneg _
  · filter_upwards [pathIntegral_tendsto_ae hφ hM T,
      ae_all_iff.mpr (fun n => integralClass_coeFn hφ hM n T),
      Lp.coeFn_zero ℝ 2 gaussianProduct] with ω ht hn hz
    simpa only [hn, hz, Pi.zero_apply] using ht

end OperatorDerivativeRewrite.Foundation.IBMBoundaryLayerRemainder
