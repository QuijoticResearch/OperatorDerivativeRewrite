import Foundation.IBMVarianceClockGeometry
import Foundation.BrownianTanakaResidual
import Foundation.BrownianMassLimitIdentification
import Foundation.BochnerL2RepresentativeFubini

/-! Genuine shrinking-mollifier clock occupation and its L² Tanaka limit.
The smooth function is the actual IBM scenery variance. This verifies the
unweighted boundary term; general Schwartz coefficients require further work. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMBoundaryClockLimit
open InfiniteGaussian IBMVarianceClockGeometry IBMMollifier
open GaussianLipschitzIntegrands GaussianPredictableFull GaussianBoundedApproximation
open BrownianTanakaApproximation GaussianTimeProductL2 GaussianProductDerivative
open BrownianClockWeightedEnergy

theorem exists_curvature_bound (n : ℕ) :
    ∃ K : ℝ≥0, ∀ x, ‖deriv (deriv (variance n)) x‖₊ ≤ K := by
  obtain ⟨M, hM⟩ := (kernel_compactSupport n).isCompact.exists_bound_of_continuousOn
    (kernel_smooth n).continuous.continuousOn
  refine ⟨⟨2 * max M 0, by positivity⟩, ?_⟩
  intro x
  change ‖deriv (deriv (variance n)) x‖ ≤ 2 * max M 0
  rw [variance_second, norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  by_cases hx : kernel n x = 0
  · simp only [hx, norm_zero]; exact le_max_right _ _
  · exact (hM x (subset_tsupport _ hx)).trans (le_max_left _ _)

def curvatureBound (n : ℕ) : ℝ≥0 := (exists_curvature_bound n).choose

theorem curvature_bound (n : ℕ) (x : ℝ) :
    ‖deriv (deriv (variance n)) x‖₊ ≤ curvatureBound n :=
  (exists_curvature_bound n).choose_spec x

theorem first_bound (n : ℕ) (x : ℝ) : ‖deriv (variance n) x‖₊ ≤ (1 : ℝ≥0) :=
  show ‖deriv (variance n) x‖ ≤ (1 : ℝ) from slope_bound n x

theorem derivativeLip (n : ℕ) : LipschitzWith (curvatureBound n) (deriv (variance n)) :=
  GaussianC2Ito.derivativeLip (variance n) (variance_smooth n) (curvatureBound n)
    (curvature_bound n)

def field (n : ℕ) (T : ℝ≥0) : fullPredictable := integrand (derivativeLip n) T

theorem field_tendsto (T : ℝ≥0) :
    Tendsto (fun n => field n T) atTop (𝓝 (BrownianSignIntegral.predictableField T)) := by
  apply tendsto_subtype_rng.mpr
  apply BochnerL2Dominated.tendsto_of_ae_norm_bound
  · intro n
    filter_upwards [integrand_joint (derivativeLip n) T,
      BrownianSignIntegral.field_coeFn T] with z hn hs
    change ‖(field n T : TimeProbabilityL2) z‖ ≤ ‖BrownianSignIntegral.field T z‖
    change (field n T : TimeProbabilityL2) z = _ at hn
    rw [hn, hs]
    by_cases ht : z ∈ PredictableRealL2.horizon T
    · simpa only [indicator_of_mem ht] using slope_sign_bound n (sigma z)
    · simp [ht]
  · filter_upwards [ae_all_iff.mpr (fun n => integrand_joint (derivativeLip n) T),
      BrownianSignIntegral.field_coeFn T] with z hn hs
    change Tendsto (fun n => (field n T : TimeProbabilityL2) z) atTop
      (𝓝 (BrownianSignIntegral.field T z))
    change ∀ n, (field n T : TimeProbabilityL2) z =
      (PredictableRealL2.horizon T).indicator (fun z => deriv (variance n) (sigma z)) z at hn
    simp only [hn, hs]
    by_cases ht : z ∈ PredictableRealL2.horizon T
    · simpa only [indicator_of_mem ht] using slope_tendsto (sigma z)
    · simpa only [indicator_of_notMem ht] using (tendsto_const_nhds (x := (0 : ℝ)))

theorem terminal_tendsto (T : ℝ≥0) :
    Tendsto (fun n => valueL2 (variance_lipschitz n) T) atTop (𝓝 (absoluteValue T)) := by
  apply BochnerL2Approximation.tendsto_of_dominated _ _
    (absoluteValue T + (2 : ℝ) • gaussianOne)
  · intro n
    filter_upwards [valueL2_coeFn (variance_lipschitz n) T,
      Lp.coeFn_add (absoluteValue T) ((2 : ℝ) • gaussianOne),
      Lp.coeFn_smul (2 : ℝ) gaussianOne, gaussianOne_coeFn,
      absoluteValue_coeFn T, IBMConstructedSources.clockPath_coordinate_ae T]
      with ω hv ha hs ho hb hc
    simp only [hv, ha, Pi.add_apply, hs, Pi.smul_apply, smul_eq_mul, ho, mul_one, hb, hc]
    exact (variance_bound n _).trans (le_abs_self _)
  · filter_upwards [Lp.coeFn_add (absoluteValue T) ((2 : ℝ) • gaussianOne),
      Lp.coeFn_smul (2 : ℝ) gaussianOne, gaussianOne_coeFn,
      absoluteValue_coeFn T] with ω ha hs ho hb
    simp only [ha, Pi.add_apply, hs, Pi.smul_apply, smul_eq_mul, ho, mul_one, hb,
      Real.norm_eq_abs, abs_abs]
    exact le_trans (by linarith : |IBMConstructedSources.clockPath ω T| ≤
      |IBMConstructedSources.clockPath ω T| + 2) (le_abs_self _)
  · filter_upwards [ae_all_iff.mpr (fun n => valueL2_coeFn (variance_lipschitz n) T),
      absoluteValue_coeFn T, IBMConstructedSources.clockPath_coordinate_ae T]
      with ω hn hb hc
    simpa only [hn, hb, hc] using variance_tendsto (GaussianTimeProcess.process T ω)

def curvatureValue (n : ℕ) (t : ℝ≥0) : GaussianL2 :=
  GaussianC2Ito.curvatureValue (variance n) (variance_smooth n) (curvatureBound n)
    (curvature_bound n) t

def clockMass (n : ℕ) (T : ℝ≥0) : GaussianL2 :=
  (1/2 : ℝ) • ∫ t in 0..(T : ℝ), curvatureValue n t.toNNReal

/-- Exact actual stochastic identity at every mollifier scale. -/
theorem clockMass_identity (n : ℕ) (T : ℝ≥0) :
    clockMass n T = valueL2 (variance_lipschitz n) T -
      variance n 0 • gaussianOne - itoIntegral (field n T) := by
  have h := GaussianC2Ito.c2_ito (variance n) (variance_smooth n) 1 (curvatureBound n)
    (first_bound n) (curvature_bound n) T
  rw [GaussianSmoothIto.valueL2_zero] at h
  change valueL2 (variance_lipschitz n) T - variance n 0 • gaussianOne =
    itoIntegral (field n T) + clockMass n T at h
  linear_combination (norm := module) -h

/-- Strong random-variable L² convergence, not merely equality of means. -/
theorem clockMass_tendsto (T : ℝ≥0) :
    Tendsto (fun n => clockMass n T) atTop (𝓝 (BrownianTanakaResidual.mass T)) := by
  have hz := (variance_tendsto 0).smul_const gaussianOne
  simp only [abs_zero, zero_smul] at hz
  have hi := itoIntegral.continuous.tendsto (BrownianSignIntegral.predictableField T)
    |>.comp (field_tendsto T)
  have h := ((terminal_tendsto T).sub hz).sub hi
  simpa only [Function.comp_apply, sub_zero, ← clockMass_identity, BrownianTanakaResidual.mass,
    BrownianSignIntegral.terminal] using h

theorem kernel_abs (n : ℕ) (x : ℝ) : kernel n |x| = kernel n x := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx), IBMBoundaryCurvature.kernel_even]

theorem curvatureValue_coeFn (n : ℕ) (t : ℝ≥0) :
    curvatureValue n t =ᵐ[gaussianProduct] fun ω =>
      2 * kernel n |IBMConstructedSources.clockPath ω t| := by
  filter_upwards [GaussianC2Ito.curvatureValue_coeFn (variance n) (variance_smooth n)
    (curvatureBound n) (curvature_bound n) t,
    IBMConstructedSources.clockPath_coordinate_ae t] with ω hv hc
  change curvatureValue n t ω = _ at hv
  rw [hv, variance_second, hc, kernel_abs]

/-- The clock mass is the actual pathwise time integral of the original
IBM mollifier at the constructed reflected Brownian clock. -/
theorem clockMass_coeFn (n : ℕ) (T : ℝ≥0) :
    clockMass n T =ᵐ[gaussianProduct] fun ω =>
      ∫ s in 0..(T : ℝ), kernel n |IBMConstructedSources.clockPath ω s.toNNReal| := by
  have hc := (GaussianC2TimeWeighted.curvature_continuous (variance n) (variance_smooth n)
    (curvatureBound n) (curvature_bound n)).comp continuous_real_toNNReal
  change Continuous (fun t : ℝ => curvatureValue n t.toNNReal) at hc
  have hm : Measurable (fun z : ℝ × SampleSpace =>
      2 * kernel n |IBMConstructedSources.clockPath z.2 z.1.toNNReal|) := by
    have he : Measurable (fun z : ℝ × SampleSpace =>
        IBMConstructedSources.clockPath z.2 z.1.toNNReal) :=
      continuous_eval.measurable.comp
        ((IBMConstructedSources.clockPath_measurable.comp measurable_snd).prodMk
          (continuous_real_toNNReal.measurable.comp measurable_fst))
    exact measurable_const.mul ((kernel_smooth n).continuous.measurable.comp
      (continuous_abs.measurable.comp he))
  have h := BochnerL2RepresentativeFubini.integral_coeFn_ae
    (μ := volume.restrict (Ioc 0 (T : ℝ))) (ν := gaussianProduct)
    (fun t : ℝ => curvatureValue n t.toNNReal) ((hc.intervalIntegrable 0 T).1)
    (fun z : ℝ × SampleSpace =>
      2 * kernel n |IBMConstructedSources.clockPath z.2 z.1.toNNReal|)
    hm.stronglyMeasurable.aestronglyMeasurable
    (Eventually.of_forall fun t => curvatureValue_coeFn n t.toNNReal)
  change ((1/2 : ℝ) • ∫ t in 0..(T : ℝ), curvatureValue n t.toNNReal) =ᵐ[gaussianProduct] _
  simp only [intervalIntegral.integral_of_le T.coe_nonneg]
  filter_upwards [h, Lp.coeFn_smul (1/2 : ℝ)
    (∫ t in Ioc 0 (T : ℝ), curvatureValue n t.toNNReal)] with ω hf hs
  rw [hs, Pi.smul_apply, smul_eq_mul, hf, integral_const_mul]
  ring

theorem path_integral_memLp (n : ℕ) (T : ℝ≥0) :
    MemLp (fun ω => ∫ s in 0..(T : ℝ),
      kernel n |IBMConstructedSources.clockPath ω s.toNNReal|) 2 gaussianProduct :=
  (Lp.memLp (clockMass n T)).ae_eq (clockMass_coeFn n T)

/-- Actual random functionals converge in L² to the already constructed
continuous Brownian mass at each fixed horizon. -/
theorem path_integral_tendsto (T : ℝ≥0) :
    Tendsto (fun n => (path_integral_memLp n T).toLp _) atTop
      (𝓝 (BrownianMassLimitIdentification.coordinateClass T)) := by
  have he (n : ℕ) : (path_integral_memLp n T).toLp _ = clockMass n T := by
    apply Lp.ext
    exact (path_integral_memLp n T).coeFn_toLp.trans (clockMass_coeFn n T).symm
  simpa only [he, BrownianMassLimitIdentification.coordinateClass_eq] using clockMass_tendsto T

end OperatorDerivativeRewrite.Foundation.IBMBoundaryClockLimit
