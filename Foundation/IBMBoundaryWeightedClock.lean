import Foundation.IBMBoundaryAveragedCoefficient
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-! Actual scenery-averaged boundary integrals and their strong random L²
limit. The coefficient is constructed from the original scenery law. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMBoundaryWeightedClock
open InfiniteGaussian IBMConstructedSources IBMMollifier IBMBoundaryClockLimit
open IBMBoundaryAveragedCoefficient
variable {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ)

def errorPath (n : ℕ) (T : ℝ≥0) (ω : SampleSpace) : ℝ :=
  ∫ t in 0..(T : ℝ), kernel n |clockPath ω t.toNNReal| *
    (sourceAverage hφ n |clockPath ω t.toNNReal| - φ 0)

theorem error_integrand_continuous (n : ℕ) (ω : SampleSpace) :
    Continuous (fun t : ℝ => kernel n |clockPath ω t.toNNReal| *
      (sourceAverage hφ n |clockPath ω t.toNNReal| - φ 0)) := by
  have hc := continuous_abs.comp ((clockPath ω).continuous.comp continuous_real_toNNReal)
  exact ((kernel_smooth n).continuous.comp hc).mul
    (((sourceAverage_continuous hφ n).comp hc).sub continuous_const)

theorem errorPath_stronglyMeasurable (n : ℕ) (T : ℝ≥0) :
    StronglyMeasurable (errorPath hφ n T) := by
  have he : Measurable (fun z : ℝ × SampleSpace => |clockPath z.2 z.1.toNNReal|) :=
    continuous_abs.measurable.comp (continuous_eval.measurable.comp
      ((clockPath_measurable.comp measurable_snd).prodMk
        (continuous_real_toNNReal.measurable.comp measurable_fst)))
  have hm : Measurable (fun z : ℝ × SampleSpace => kernel n |clockPath z.2 z.1.toNNReal| *
      (sourceAverage hφ n |clockPath z.2 z.1.toNNReal| - φ 0)) :=
    ((kernel_smooth n).continuous.measurable.comp he).mul
    (((sourceAverage_continuous hφ n).measurable.comp he).sub measurable_const)
  change StronglyMeasurable (fun ω => ∫ t in 0..(T : ℝ), _)
  simp only [intervalIntegral.integral_of_le T.coe_nonneg]
  exact hm.stronglyMeasurable.integral_prod_left'

theorem errorPath_bound (n : ℕ) (T : ℝ≥0) (ω : SampleSpace) :
    ‖errorPath hφ n T ω‖ ≤ layerError (K := K) n *
      (∫ t in 0..(T : ℝ), kernel n |clockPath ω t.toNNReal|) := by
  rw [errorPath, intervalIntegral.integral_of_le T.coe_nonneg,
    intervalIntegral.integral_of_le T.coe_nonneg, ← integral_const_mul]
  apply norm_integral_le_of_norm_le
  · have hc : Continuous (fun t : ℝ => layerError (K := K) n *
        kernel n |clockPath ω t.toNNReal|) := by
      exact continuous_const.mul ((kernel_smooth n).continuous.comp
        (continuous_abs.comp ((clockPath ω).continuous.comp continuous_real_toNNReal)))
    exact hc.integrableOn_Ioc
  · exact Eventually.of_forall fun t => weighted_error_bound hφ n _

theorem errorPath_memLp (n : ℕ) (T : ℝ≥0) : MemLp (errorPath hφ n T) 2 gaussianProduct := by
  apply (path_integral_memLp n T).of_le_mul
    (errorPath_stronglyMeasurable hφ n T).aestronglyMeasurable
  exact Eventually.of_forall fun ω => (errorPath_bound hφ n T ω).trans
    (mul_le_mul_of_nonneg_left (le_abs_self _) (layerError_nonneg (K := K) n))

def errorClass (n : ℕ) (T : ℝ≥0) : GaussianL2 :=
  (errorPath_memLp hφ n T).toLp (errorPath hφ n T)

theorem errorClass_coeFn (n : ℕ) (T : ℝ≥0) :
    errorClass hφ n T =ᵐ[gaussianProduct] errorPath hφ n T :=
  (errorPath_memLp hφ n T).coeFn_toLp

theorem errorClass_norm (n : ℕ) (T : ℝ≥0) :
    ‖errorClass hφ n T‖ ≤ layerError (K := K) n * ‖clockMass n T‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [errorClass_coeFn hφ n T, clockMass_coeFn n T] with ω he hm
  rw [he, hm]
  exact (errorPath_bound hφ n T ω).trans
    (mul_le_mul_of_nonneg_left (le_abs_self _) (layerError_nonneg (K := K) n))

theorem errorClass_tendsto (T : ℝ≥0) :
    Tendsto (fun n => errorClass hφ n T) atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => errorClass_norm hφ n T)
  simpa only [zero_mul] using
    (layerError_tendsto (K := K)).mul (clockMass_tendsto T).norm

def weightedPath (n : ℕ) (T : ℝ≥0) (ω : SampleSpace) : ℝ :=
  ∫ t in 0..(T : ℝ), kernel n |clockPath ω t.toNNReal| *
    sourceAverage hφ n |clockPath ω t.toNNReal|

theorem weightedPath_decomposition (n : ℕ) (T : ℝ≥0) (ω : SampleSpace) :
    weightedPath hφ n T ω = φ 0 *
      (∫ t in 0..(T : ℝ), kernel n |clockPath ω t.toNNReal|) + errorPath hφ n T ω := by
  have hc : Continuous (fun t : ℝ => kernel n |clockPath ω t.toNNReal|) :=
    (kernel_smooth n).continuous.comp
      (continuous_abs.comp ((clockPath ω).continuous.comp continuous_real_toNNReal))
  have he : (fun t : ℝ => kernel n |clockPath ω t.toNNReal| *
      sourceAverage hφ n |clockPath ω t.toNNReal|) =
      (fun t => φ 0 * kernel n |clockPath ω t.toNNReal|) +
        (fun t => kernel n |clockPath ω t.toNNReal| *
          (sourceAverage hφ n |clockPath ω t.toNNReal| - φ 0)) := by
    funext t
    simp only [Pi.add_apply]
    ring
  have hf : Continuous (fun t : ℝ => φ 0 * kernel n |clockPath ω t.toNNReal|) :=
    continuous_const.mul hc
  rw [weightedPath, he]
  change (∫ t in 0..(T : ℝ), φ 0 * kernel n |clockPath ω t.toNNReal| +
    kernel n |clockPath ω t.toNNReal| *
      (sourceAverage hφ n |clockPath ω t.toNNReal| - φ 0)) = _
  rw [intervalIntegral.integral_add (hf.intervalIntegrable 0 T)
    ((error_integrand_continuous hφ n ω).intervalIntegrable 0 T),
      intervalIntegral.integral_const_mul]
  rfl

def weightedClass (n : ℕ) (T : ℝ≥0) : GaussianL2 :=
  φ 0 • clockMass n T + errorClass hφ n T

theorem weightedClass_coeFn (n : ℕ) (T : ℝ≥0) :
    weightedClass hφ n T =ᵐ[gaussianProduct] weightedPath hφ n T := by
  filter_upwards [Lp.coeFn_add (φ 0 • clockMass n T) (errorClass hφ n T),
    Lp.coeFn_smul (φ 0) (clockMass n T), clockMass_coeFn n T,
    errorClass_coeFn hφ n T] with ω ha hs hm he
  rw [weightedClass, ha, Pi.add_apply, hs, Pi.smul_apply, smul_eq_mul, hm, he,
    weightedPath_decomposition]

/-- Strong L² convergence of the actual weighted random boundary integral. -/
theorem weightedClass_tendsto (T : ℝ≥0) :
    Tendsto (fun n => weightedClass hφ n T) atTop
      (𝓝 (φ 0 • BrownianTanakaResidual.mass T)) := by
  have h := ((clockMass_tendsto T).const_smul (φ 0)).add (errorClass_tendsto hφ T)
  simpa only [add_zero, weightedClass] using h

theorem weightedPath_memLp (n : ℕ) (T : ℝ≥0) :
    MemLp (weightedPath hφ n T) 2 gaussianProduct :=
  (Lp.memLp (weightedClass hφ n T)).ae_eq (weightedClass_coeFn hφ n T)

theorem weightedPath_tendsto (T : ℝ≥0) :
    Tendsto (fun n => (weightedPath_memLp hφ n T).toLp _) atTop
      (𝓝 (φ 0 • BrownianMassLimitIdentification.coordinateClass T)) := by
  have he (n : ℕ) : (weightedPath_memLp hφ n T).toLp _ = weightedClass hφ n T := by
    apply Lp.ext
    exact (weightedPath_memLp hφ n T).coeFn_toLp.trans (weightedClass_coeFn hφ n T).symm
  simpa only [he, BrownianMassLimitIdentification.coordinateClass_eq] using
    weightedClass_tendsto hφ T

/-- The coefficient domain includes every actual Schwartz test, with a
verified derivative-seminorm Lipschitz bound. -/
theorem schwartz_lipschitz (g : SchwartzMap ℝ ℝ) :
    LipschitzWith (Real.toNNReal (SchwartzMap.seminorm ℝ 0 1 g)) (g : ℝ → ℝ) := by
  apply lipschitzWith_of_nnnorm_deriv_le g.differentiable
  intro x
  change ‖deriv (g : ℝ → ℝ) x‖ ≤ (Real.toNNReal (SchwartzMap.seminorm ℝ 0 1 g) : ℝ)
  have h := SchwartzMap.le_seminorm' ℝ 0 1 g x
  simp only [pow_zero, one_mul, iteratedDeriv_one] at h
  exact h.trans (Real.le_coe_toNNReal _)

theorem schwartz_weighted_limit (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) :
    Tendsto (fun n => weightedClass (schwartz_lipschitz g) n T) atTop
      (𝓝 (g 0 • BrownianTanakaResidual.mass T)) :=
  weightedClass_tendsto (schwartz_lipschitz g) T

end OperatorDerivativeRewrite.Foundation.IBMBoundaryWeightedClock
