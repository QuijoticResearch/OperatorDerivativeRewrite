import Foundation.GaussianHermiteFutureError
import Foundation.GaussianShiftedIntegrand
import Foundation.BochnerL2Dominated

/-! Actual predictable representation of past-weighted future Hermite variables.
The past coefficient is only square integrable and measurable, not bounded. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianWeightedHermite
open InfiniteGaussian GaussianTimeSpaceHermite GaussianTimeProcess GaussianTimeHilbert
open GaussianPredictableFull GaussianPredictableAdjoint GaussianTimeProductL2
open GaussianPastFutureProducts GaussianHermiteFutureError GaussianBrownianQuadraticVariation
open GaussianPredictableStep (pastCoefficient pastCoefficient_measurable_natural)

variable (s : ℝ≥0) (a : (Iic s → ℝ) → ℝ) (ha : Measurable a)
  (hA : MemLp (pastCoefficient process s a) 2 gaussianProduct)
include ha hA

theorem coefficient_memLp (r : ℝ≥0) (n : ℕ) :
    MemLp (fun ω => pastCoefficient process s a ω *
      value n (process (s + r) ω - process s ω) r) 2 gaussianProduct :=
  past_future_memLp s ha (value_functional_measurable n r) hA
    (GaussianShiftedHermite.incrementCore_memLp s r n 2 (by simp))

def coefficient (r : ℝ≥0) (n : ℕ) : GaussianL2 :=
  (coefficient_memLp s a ha hA r n).toLp _

theorem coefficient_coeFn (r : ℝ≥0) (n : ℕ) :
    coefficient s a ha hA r n =ᵐ[gaussianProduct] fun ω => pastCoefficient process s a ω *
      value n (process (s + r) ω - process s ω) r := MemLp.coeFn_toLp _

theorem coefficient_past (r : ℝ≥0) (n : ℕ) :
    AEStronglyMeasurable[naturalFiltration (s + r)] (coefficient s a ha hA r n) gaussianProduct := by
  have hG : Measurable[naturalFiltration (s + r)] (pastCoefficient process s a) :=
    (pastCoefficient_measurable_natural (fun t => (process_stronglyMeasurable t).measurable) s ha).mono
      (naturalFiltration.mono (by exact le_add_of_nonneg_right (by positivity))) le_rfl
  have hH : Measurable[naturalFiltration (s + r)]
      (fun ω => value n (process (s + r) ω - process s ω) r) := by
    letI : MeasurableSpace SampleSpace := naturalFiltration (s + r)
    exact (polynomial r n).continuous_eval.measurable.comp (Measurable.of_eval (fun _ : Unit =>
      (process_stronglyAdapted (s + r)).measurable.sub ((process_stronglyAdapted s).measurable.mono
        (naturalFiltration.mono (by exact le_add_of_nonneg_right (by positivity))) le_rfl)))
  exact (hG.mul hH).stronglyMeasurable.aestronglyMeasurable.congr (coefficient_coeFn s a ha hA r n).symm

def step (n : ℕ) (r u : ℝ≥0) : fullPredictable :=
  ⟨productTensor (intervalVector (s + r) (s + u)) (coefficient s a ha hA r n),
    past_step_mem_fullPredictable (s + r) (s + u) _ (coefficient_past s a ha hA r n)⟩

def stepSum (n : ℕ) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) : fullPredictable :=
  ∑ i : Fin m, step s a ha hA n (τ i.castSucc) (τ i.succ)

theorem stepSum_coe (n : ℕ) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) :
    (stepSum s a ha hA n τ : TimeProbabilityL2) =
      partitionL2 (fun i => s + τ i) (fun i => coefficient s a ha hA (τ i.castSucc) n) := by
  simp only [stepSum, Submodule.coe_sum, step, partitionL2, NNReal.coe_add]

theorem integral_stepSum_coeFn (n : ℕ) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) (hτ : Monotone τ) :
    itoIntegral (stepSum s a ha hA n τ) =ᵐ[gaussianProduct]
      fun ω => pastCoefficient process s a ω * futureValue s (sumFunctional n τ) ω := by
  rw [stepSum, map_sum]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin m =>
    itoIntegral (step s a ha hA n (τ i.castSucc) (τ i.succ))), ae_all_iff.mpr (fun i : Fin m =>
      itoIntegral_past_step (s + τ i.castSucc) (s + τ i.succ)
        (add_le_add le_rfl (hτ (Fin.castSucc_le_succ i)))
        (coefficient s a ha hA (τ i.castSucc) n) (coefficient_past s a ha hA (τ i.castSucc) n)),
    ae_all_iff.mpr (fun i : Fin m => coefficient_coeFn s a ha hA (τ i.castSucc) n)] with ω hs hi hc
  rw [hs]
  simp only [Finset.sum_apply, futureValue, sumFunctional, futureProcess, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h := hi i
  change itoIntegral (step s a ha hA n (τ i.castSucc) (τ i.succ)) ω = _ at h
  rw [h, hc i]
  ring

theorem error_coeFn (n : ℕ) (T : ℝ≥0) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0) (hτ : Monotone τ) :
    (coefficient s a ha hA T (n + 1) - (n + 1 : ℝ) • itoIntegral (stepSum s a ha hA n τ))
      =ᵐ[gaussianProduct] fun ω => pastCoefficient process s a ω *
        futureValue s (errorFunctional n T τ) ω := by
  filter_upwards [Lp.coeFn_sub (coefficient s a ha hA T (n + 1))
    ((n + 1 : ℝ) • itoIntegral (stepSum s a ha hA n τ)),
    Lp.coeFn_smul (n + 1 : ℝ) (itoIntegral (stepSum s a ha hA n τ)),
    coefficient_coeFn s a ha hA T (n + 1), integral_stepSum_coeFn s a ha hA n τ hτ] with ω hs hm hc hi
  simp only [hs, Pi.sub_apply, hm, Pi.smul_apply, smul_eq_mul, hc, hi,
    futureValue, errorFunctional, futureProcess]
  ring

theorem stochasticSum_error_sq (n : ℕ) (T : ℝ≥0) {m : ℕ} (τ : Fin (m + 1) → ℝ≥0)
    (hτ : Monotone τ) :
    ‖coefficient s a ha hA T (n + 1) - (n + 1 : ℝ) • itoIntegral (stepSum s a ha hA n τ)‖ ^ 2 =
      ∫ ω, (pastCoefficient process s a ω * futureValue s (errorFunctional n T τ) ω) ^ 2
        ∂gaussianProduct := by
  rw [BochnerL2Dominated.norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [error_coeFn s a ha hA n T τ hτ] with ω he
  rw [he, Real.norm_eq_abs, sq_abs]

theorem scaled_stochasticSum_tendsto (n : ℕ) (T : ℝ≥0) :
    Tendsto (fun N => (n + 1 : ℝ) • itoIntegral (stepSum s a ha hA n (uniformTime T N))) atTop
      (𝓝 (coefficient s a ha hA T (n + 1))) := by
  have ht := weighted_error_sq_tendsto s n T ha hA
  have hn : Tendsto (fun N => ‖coefficient s a ha hA T (n + 1) -
      (n + 1 : ℝ) • itoIntegral (stepSum s a ha hA n (uniformTime T N))‖ ^ 2) atTop (𝓝 0) := by
    simpa only [stochasticSum_error_sq s a ha hA n T _ (uniformTime_monotone T _)] using ht
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hh
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [norm_sub_rev] using hh

theorem stochasticSum_tendsto (n : ℕ) (T : ℝ≥0) :
    Tendsto (fun N => itoIntegral (stepSum s a ha hA n (uniformTime T N))) atTop
      (𝓝 ((n + 1 : ℝ)⁻¹ • coefficient s a ha hA T (n + 1))) := by
  have h := (scaled_stochasticSum_tendsto s a ha hA n T).const_smul (n + 1 : ℝ)⁻¹
  simpa only [smul_smul, inv_mul_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0), one_smul] using h

theorem weighted_hermite_mem_range (n : ℕ) (T : ℝ≥0) :
    (n + 1 : ℝ)⁻¹ • coefficient s a ha hA T (n + 1) ∈ itoIntegral.toLinearMap.range :=
  GaussianBrownianGeneratedSpace.integralRange_isClosed.mem_of_tendsto
    (stochasticSum_tendsto s a ha hA n T)
    (Eventually.of_forall fun N => ⟨stepSum s a ha hA n (uniformTime T N), rfl⟩)

def hermiteIntegrand (n : ℕ) (T : ℝ≥0) : fullPredictable :=
  predictableAdjoint ((n + 1 : ℝ)⁻¹ • coefficient s a ha hA T (n + 1))

theorem integral_hermiteIntegrand (n : ℕ) (T : ℝ≥0) :
    itoIntegral (hermiteIntegrand s a ha hA n T) =
      (n + 1 : ℝ)⁻¹ • coefficient s a ha hA T (n + 1) := by
  obtain ⟨u, hu⟩ := weighted_hermite_mem_range s a ha hA n T
  change itoIntegral u = _ at hu
  unfold hermiteIntegrand
  rw [← hu, predictableAdjoint_integral]

theorem hermite_representation (n : ℕ) (T : ℝ≥0) :
    coefficient s a ha hA T (n + 1) = (n + 1 : ℝ) • itoIntegral (hermiteIntegrand s a ha hA n T) := by
  rw [integral_hermiteIntegrand, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]

theorem stepSum_tendsto (n : ℕ) (T : ℝ≥0) :
    Tendsto (fun N => stepSum s a ha hA n (uniformTime T N)) atTop
      (𝓝 (hermiteIntegrand s a ha hA n T)) := by
  have h := predictableAdjoint.continuous.continuousAt.tendsto.comp (stochasticSum_tendsto s a ha hA n T)
  simpa only [Function.comp_def, predictableAdjoint_integral, hermiteIntegrand] using h

theorem coefficient_difference_norm_sq (r q : ℝ≥0) (n : ℕ) :
    ‖coefficient s a ha hA r n - coefficient s a ha hA q n‖ ^ 2 =
      (∫ ω, pastCoefficient process s a ω ^ 2 ∂gaussianProduct) *
        ‖(GaussianShiftedHermite.incrementCore s r n : GaussianL2) -
          GaussianShiftedHermite.incrementCore s q n‖ ^ 2 := by
  let b : (ℝ≥0 → ℝ) → ℝ := fun z => value n (z r) r - value n (z q) q
  have hb : Measurable b := (value_functional_measurable n r).sub (value_functional_measurable n q)
  have hB : MemLp (futureValue s b) 2 gaussianProduct :=
    (GaussianShiftedHermite.incrementCore_memLp s r n 2 (by simp)).sub
      (GaussianShiftedHermite.incrementCore_memLp s q n 2 (by simp))
  have he : (∫ ω, futureValue s b ω ^ 2 ∂gaussianProduct) =
      ‖(GaussianShiftedHermite.incrementCore s r n : GaussianL2) -
        GaussianShiftedHermite.incrementCore s q n‖ ^ 2 := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (GaussianShiftedHermite.incrementCore s r n : GaussianL2)
      (GaussianShiftedHermite.incrementCore s q n : GaussianL2),
      GaussianShiftedHermite.incrementCore_coeFn s r n,
      GaussianShiftedHermite.incrementCore_coeFn s q n] with ω hd hr hq
    simp only [hd, Pi.sub_apply, hr, hq, Real.norm_eq_abs, sq_abs, futureValue, futureProcess, b]
  rw [← he, ← past_future_sq_integral s ha hb hA hB, BochnerL2Dominated.norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (coefficient s a ha hA r n) (coefficient s a ha hA q n),
    coefficient_coeFn s a ha hA r n, coefficient_coeFn s a ha hA q n] with ω hd hr hq
  simp only [hd, Pi.sub_apply, hr, hq, Real.norm_eq_abs, sq_abs, futureValue, futureProcess, b]
  ring

theorem coefficient_continuous (n : ℕ) : Continuous (fun r : ℝ≥0 => coefficient s a ha hA r n) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  have hc : Continuous (fun r : ℝ≥0 => ‖coefficient s a ha hA r n - coefficient s a ha hA q n‖ ^ 2) := by
    simp_rw [coefficient_difference_norm_sq s a ha hA]
    exact continuous_const.mul (((GaussianShiftedIntegrand.incrementCore_continuous s n).sub
      continuous_const).norm.pow 2)
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp (hc.continuousAt (x := q)).tendsto
  simp only [Function.comp_def, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] at hs
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hs

end OperatorDerivativeRewrite.Foundation.GaussianWeightedHermite
