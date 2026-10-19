import Foundation.GaussianC2Ito
import Foundation.ReflectedC2Primitive
import Foundation.BrownianMassLimitIdentification
import Foundation.BrownianSignIntegral
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
open OperatorDerivativeRewrite.Foundation
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianPredictableFull
open ReflectedC2Primitive GaussianLipschitzIntegrands
namespace DraftReflectedScalarIto
variable (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (K0 K1 : ℝ≥0)
  (h0 : ∀ x, ‖deriv f x‖ ≤ (K0 : ℝ))
  (h1 : ∀ x, ‖deriv (deriv f) x‖ ≤ (K1 : ℝ))

include hf h0 in
theorem bound0 (x : ℝ) : ‖deriv (corrected f) x‖₊ ≤ 2*K0 := by
  exact_mod_cast corrected_deriv_bound (hf.differentiable (by norm_num)) h0 x

include hf h1 in
theorem bound1 (x : ℝ) : ‖deriv (deriv (corrected f)) x‖₊ ≤ K1 := by
  exact_mod_cast corrected_second_deriv_bound hf h1 x

def running (T : ℝ≥0) : fullPredictable :=
  integrand (GaussianC2Ito.derivativeLip (corrected f) (corrected_C2 hf) K1
    (bound1 f hf K1 h1)) T + deriv f 0 • BrownianSignIntegral.predictableField T

def drift (T : ℝ≥0) : GaussianL2 :=
  ∫ t in 0..(T : ℝ), GaussianC2Ito.curvatureValue (corrected f) (corrected_C2 hf) K1
    (bound1 f hf K1 h1) t.toNNReal

include K0 h0 in
theorem reflected_ito_ae (T : ℝ≥0) :
    (fun ω => f |IBMConstructedSources.clockPath ω T|-f 0) =ᵐ[gaussianProduct]
      fun ω => itoIntegral (running f hf K1 h1 T) ω+
        deriv f 0*BrownianMassContinuousLimit.limitPath ω T+
        (1/2 : ℝ)*(drift f hf K1 h1 T) ω := by
  let J := itoIntegral (integrand
    (GaussianC2Ito.derivativeLip (corrected f) (corrected_C2 hf) K1
      (bound1 f hf K1 h1)) T)
  have he : itoIntegral (running f hf K1 h1 T) =
      J+deriv f 0 • BrownianSignIntegral.terminal T := by
    simp only [running, map_add, map_smul]
    rfl
  have hc := GaussianC2Ito.c2_ito_ae (corrected f) (corrected_C2 hf) (2*K0) K1
    (bound0 f hf K0 h0) (bound1 f hf K1 h1) T
  filter_upwards [hc, BrownianMassLimitIdentification.tanaka_ae T,
    IBMConstructedSources.clockPath_coordinate_ae T,
    Lp.coeFn_add J (deriv f 0 • BrownianSignIntegral.terminal T),
    Lp.coeFn_smul (deriv f 0) (BrownianSignIntegral.terminal T)] with ω hc ht hw ha hs
  change corrected f (process T ω)-corrected f 0 = J ω+(1/2 : ℝ)*(drift f hf K1 h1 T) ω at hc
  rw [← hw] at hc
  simp only [corrected, abs_zero, zero_mul, sub_zero] at hc
  rw [he, ha]
  simp only [Pi.add_apply]
  rw [hs]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination hc + deriv f 0 * ht
end DraftReflectedScalarIto
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
open OperatorDerivativeRewrite.Foundation
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianLipschitzIntegrands
open GaussianContinuousIntegrands BrownianClockWeightedEnergy IBMConstructedSources
open GaussianProductDerivative
theorem lipschitz_joint {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) (T : ℝ≥0) :
    (integrand hφ T : TimeProbabilityL2) =ᵐ[timeProbability]
      (PredictableRealL2.horizon T).indicator (fun z => φ (sigma z)) := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (Lp.stronglyMeasurable _).measurable
    ((hφ.continuous.measurable.comp sigma_measurable).indicator
      (PredictableRealL2.horizon_measurable T)))).mpr
  filter_upwards [integrand_slices hφ T,
    scalarCurry_coeFn (integrand hφ T : TimeProbabilityL2)] with t ht hc
  by_cases hp : t ∈ Ioc 0 (T : ℝ)
  · rw [indicator_of_mem hp] at ht
    filter_upwards [hc, clockPath_coordinate_ae t.toNNReal,
      valueL2_coeFn hφ t.toNNReal] with ω hc hw hv
    rw [← hc, ht, hv]
    simp [PredictableRealL2.horizon, hp, sigma, hw]
  · rw [indicator_of_notMem hp] at ht
    filter_upwards [hc, Lp.coeFn_zero ℝ 2 gaussianProduct] with ω hc hz
    rw [← hc, ht, hz]
    simp [PredictableRealL2.horizon, hp]
namespace DraftReflectedScalarIto
theorem slope_sign (f : ℝ → ℝ) (x : ℝ) :
    ReflectedC2Primitive.slope f x = BrownianSignIntegral.signum x*(deriv f |x|-deriv f 0) := by
  rcases lt_trichotomy x 0 with hn | hz | hp
  · simp [ReflectedC2Primitive.slope, BrownianSignIntegral.signum, hn, not_lt_of_gt hn, abs_of_neg hn]
  · subst x
    simp [ReflectedC2Primitive.slope, BrownianSignIntegral.signum]
  · simp [ReflectedC2Primitive.slope, BrownianSignIntegral.signum, hp, not_lt_of_gt hp, abs_of_pos hp]

variable (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (K1 : ℝ≥0)
  (h1 : ∀ x, ‖deriv (deriv f) x‖ ≤ (K1 : ℝ))
theorem running_coeFn (T : ℝ≥0) :
    (running f hf K1 h1 T : TimeProbabilityL2) =ᵐ[timeProbability]
      (PredictableRealL2.horizon T).indicator
        (fun z => BrownianSignIntegral.signum (sigma z)*deriv f |sigma z|) := by
  let hφ := GaussianC2Ito.derivativeLip (corrected f) (corrected_C2 hf) K1 (bound1 f hf K1 h1)
  let U := integrand hφ T
  have hu : (running f hf K1 h1 T : TimeProbabilityL2) =
      (U : TimeProbabilityL2)+deriv f 0 • BrownianSignIntegral.field T := rfl
  filter_upwards [Lp.coeFn_add (U : TimeProbabilityL2)
      (deriv f 0 • BrownianSignIntegral.field T),
    Lp.coeFn_smul (deriv f 0) (BrownianSignIntegral.field T),
    lipschitz_joint hφ T, BrownianSignIntegral.field_coeFn T] with z ha hs hg hsign
  rw [hu, ha]
  simp only [Pi.add_apply]
  rw [hs, hg]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hsign]
  by_cases hz : z ∈ PredictableRealL2.horizon T
  · simp only [indicator_of_mem hz]
    rw [corrected_deriv (hf.differentiable (by norm_num)), slope_sign]
    ring
  · simp [hz]
end DraftReflectedScalarIto
