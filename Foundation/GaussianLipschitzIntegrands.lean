import Foundation.GaussianContinuousIntegrands
import Mathlib.Analysis.Calculus.MeanValue

/-! Actual Lipschitz functions of Brownian observations and their predictable
running fields. Spatial derivatives enter through Mathlib `deriv`, not freely
specified candidate fields. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianLipschitzIntegrands
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianProductDerivative
open GaussianContinuousIntegrands GaussianPredictableFull GaussianBrownianQuadraticVariation

variable {φ : ℝ → ℝ} {K : ℝ≥0}

theorem centered_lipschitz (hφ : LipschitzWith K φ) :
    LipschitzWith K (fun x => φ x - φ 0) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [Real.dist_eq, sub_sub_sub_cancel_right] using hφ.dist_le_mul x y

/-- Nemytskii composition with a Lipschitz scalar function, including its
nonzero constant part on the actual Gaussian probability space. -/
def composition (hφ : LipschitzWith K φ) (A : GaussianL2) : GaussianL2 :=
  (centered_lipschitz hφ).compLp (sub_self _) A + φ 0 • gaussianOne

theorem composition_coeFn (hφ : LipschitzWith K φ) (A : GaussianL2) :
    composition hφ A =ᵐ[gaussianProduct] fun ω => φ (A ω) := by
  filter_upwards [Lp.coeFn_add ((centered_lipschitz hφ).compLp (sub_self _) A)
      (φ 0 • gaussianOne),
    (centered_lipschitz hφ).coeFn_compLp (sub_self _) A,
    Lp.coeFn_smul (φ 0) gaussianOne, gaussianOne_coeFn] with ω hadd hc hs h1
  change (composition hφ A) ω = _
  rw [composition, hadd]
  simp only [Pi.add_apply]
  rw [hs, hc]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_def, h1, mul_one]
  ring

theorem composition_memLp (hφ : LipschitzWith K φ) (A : GaussianL2) :
    MemLp (fun ω => φ (A ω)) 2 gaussianProduct :=
  (Lp.memLp _).ae_eq (composition_coeFn hφ A)

theorem composition_norm_sub_le (hφ : LipschitzWith K φ) (A B : GaussianL2) :
    ‖composition hφ A - composition hφ B‖ ≤ K * ‖A - B‖ := by
  simp only [composition, add_sub_add_right_eq_sub]
  exact (centered_lipschitz hφ).norm_compLp_sub_le (sub_self _) A B

theorem composition_continuous (hφ : LipschitzWith K φ) : Continuous (composition hφ) :=
  (LipschitzWith.of_dist_le_mul (fun A B => by
    simpa only [dist_eq_norm] using composition_norm_sub_le hφ A B)).continuous

theorem wienerL2_continuous : Continuous wienerL2 := by
  have he : (fun t => (GaussianTimeSpaceHermite.brownianCore t 1 : GaussianL2)) = wienerL2 := by
    funext t
    apply Lp.ext
    filter_upwards [GaussianTimeSpaceHermite.brownianCore_coeFn t 1] with ω hω
    simpa only [GaussianTimeSpaceHermite.value_one, process] using hω
  rw [← he]
  exact GaussianHermiteIntegrand.brownianCore_continuous 1

def valueL2 (hφ : LipschitzWith K φ) (t : ℝ≥0) : GaussianL2 := composition hφ (wienerL2 t)

theorem valueL2_coeFn (hφ : LipschitzWith K φ) (t : ℝ≥0) :
    valueL2 hφ t =ᵐ[gaussianProduct] fun ω => φ (process t ω) := composition_coeFn hφ _

theorem valueL2_continuous (hφ : LipschitzWith K φ) : Continuous (valueL2 hφ) :=
  (composition_continuous hφ).comp wienerL2_continuous

theorem valueL2_past (hφ : LipschitzWith K φ) (t : ℝ≥0) :
    AEStronglyMeasurable[naturalFiltration t] (valueL2 hφ t) gaussianProduct := by
  have hm : StronglyMeasurable[naturalFiltration t] (fun ω => φ (process t ω)) :=
    hφ.continuous.comp_stronglyMeasurable (process_stronglyAdapted t)
  exact hm.aestronglyMeasurable.congr (valueL2_coeFn hφ t).symm

theorem valueL2_increment_bound (hφ : LipschitzWith K φ) (s t : ℝ≥0) (hst : s ≤ t) :
    ‖valueL2 hφ t - valueL2 hφ s‖ ^ 2 ≤ K ^ 2 * ((t : ℝ) - s) := by
  have h := composition_norm_sub_le hφ (wienerL2 t) (wienerL2 s)
  have hn : 0 ≤ (K : ℝ) * ‖wienerL2 t - wienerL2 s‖ := mul_nonneg K.coe_nonneg (norm_nonneg _)
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [valueL2, mul_pow, wienerL2_sub_norm_sq s t hst] using hs

/-- The existing predictable domain contains the actual running Lipschitz function. -/
def integrand (hφ : LipschitzWith K φ) (T : ℝ≥0) : fullPredictable :=
  predictableField (valueL2 hφ) (valueL2_continuous hφ) (valueL2_past hφ) T

theorem integrand_slices (hφ : LipschitzWith K φ) (T : ℝ≥0) :
    scalarCurry (integrand hφ T : TimeProbabilityL2) =ᵐ[volume]
      (Ioc 0 (T : ℝ)).indicator (fun t => valueL2 hφ t.toNNReal) :=
  runningField_slices (valueL2 hφ) (valueL2_continuous hφ) T

theorem integrand_integrable_sq (hφ : LipschitzWith K φ) (T : ℝ≥0) :
    Integrable (fun z => ((integrand hφ T : TimeProbabilityL2) z) ^ 2) timeProbability :=
  (Lp.memLp _).integrable_sq

/-- Actual adapted left sums converge to J of the running field. The companion
`stochastic_sum_coeFn` identifies these sums pointwise almost everywhere. -/
theorem stochastic_sum_tendsto (hφ : LipschitzWith K φ) (T : ℝ≥0) :
    Tendsto (fun N => itoIntegral (predictableStep (valueL2 hφ) (valueL2_past hφ) T N)) atTop
      (𝓝 (itoIntegral (integrand hφ T))) :=
  integral_step_tendsto _ (valueL2_continuous hφ) _ _

theorem stochastic_sum_coeFn (hφ : LipschitzWith K φ) (T : ℝ≥0) (N : ℕ) :
    itoIntegral (predictableStep (valueL2 hφ) (valueL2_past hφ) T N) =ᵐ[gaussianProduct]
      fun ω => ∑ i : Fin (N + 1), φ (process (uniformTime T N i.castSucc) ω) *
        (process (uniformTime T N i.succ) ω - process (uniformTime T N i.castSucc) ω) := by
  filter_upwards [integral_step_coeFn (valueL2 hφ) (valueL2_past hφ) T N,
    ae_all_iff.mpr (fun i : Fin (N + 1) => valueL2_coeFn hφ (uniformTime T N i.castSucc))]
      with ω hs hv
  rw [hs]
  simp only [hv]

theorem drift_sum_tendsto (hφ : LipschitzWith K φ) (T : ℝ≥0) :
    Tendsto (fun N => ∑ i : Fin (N + 1),
      ((uniformTime T N i.succ : ℝ) - uniformTime T N i.castSucc) •
        valueL2 hφ (uniformTime T N i.castSucc)) atTop
      (𝓝 (∫ t in 0..(T : ℝ), valueL2 hφ t.toNNReal)) :=
  GaussianContinuousIntegrands.drift_sum_tendsto _ (valueL2_continuous hφ) T

/-- An explicit actual-derivative criterion, with no prescribed derivative candidate. -/
theorem deriv_lipschitz (f : ℝ → ℝ) (hf : Differentiable ℝ (deriv f))
    (hbound : ∀ x, ‖deriv (deriv f) x‖₊ ≤ K) : LipschitzWith K (deriv f) :=
  lipschitzWith_of_nnnorm_deriv_le hf hbound

end OperatorDerivativeRewrite.Foundation.GaussianLipschitzIntegrands


