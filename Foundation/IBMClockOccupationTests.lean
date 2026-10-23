import Foundation.IBMClockPhysicalOccupation

/-! Actual spatial tests of the directional clock occupation kernels.
Continuous compactly supported tests are genuine spatial Lebesgue-L2 vectors. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Convolution
namespace OperatorDerivativeRewrite.Foundation.IBMClockOccupationTests
open InfiniteGaussian GaussianTimeHilbert IBMClockPhysicalOccupation
open IBMFirstSourceClockGraph IBMClockOverlapEnergy
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def testClass (φ : ℝ → ℝ) (hc : Continuous φ) (hs : HasCompactSupport φ) : TimeHilbert :=
  (hc.memLp_of_hasCompactSupport hs).toLp φ

theorem testClass_ae (φ : ℝ → ℝ) (hc : Continuous φ) (hs : HasCompactSupport φ) :
    testClass φ hc hs =ᵐ[volume] φ := MemLp.coeFn_toLp _

theorem convolution_swap (n : ℕ) (φ : ℝ → ℝ) (r : ℝ) :
    IBMMollifiedScenery.U (IBMMollifier.kernel n) φ r =
      ∫ x, IBMMollifier.kernel n (r-x) * φ x := by
  exact convolution_lsmul_swap

theorem convolution_bound (n : ℕ) (φ : ℝ → ℝ) {M : ℝ}
    (_hM : 0 ≤ M) (hb : ∀ x, ‖φ x‖ ≤ M) (r : ℝ) :
    ‖IBMMollifiedScenery.U (IBMMollifier.kernel n) φ r‖ ≤ M := by
  rw [convolution_swap]
  calc
    _ ≤ ∫ x, ‖IBMMollifier.kernel n (r-x) * φ x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, IBMMollifier.kernel n (r-x) * M := by
      apply integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
        ((IBMFoldedTransitionBound.shifted_integrable n r).mul_const M)
      exact ae_of_all _ fun x => by
        dsimp only
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (IBMMollifier.kernel_nonneg n _)]
        exact mul_le_mul_of_nonneg_left (hb x) (IBMMollifier.kernel_nonneg n _)
    _ = M := by rw [integral_mul_const, IBMFoldedTransitionBound.shifted_mass, one_mul]

theorem convolution_continuous (n : ℕ) (φ : ℝ → ℝ) (hc : Continuous φ) :
    Continuous (IBMMollifiedScenery.U (IBMMollifier.kernel n) φ) :=
  continuous_iff_continuousAt.mpr fun r =>
    (IBMMollifiedScenery.U_hasDerivAt _ _ (IBMMollifier.kernel_compactSupport n)
      ((IBMMollifier.kernel_smooth n).of_le (by simp)) hc r).continuousAt

theorem translated_test (n : ℕ) (φ : ℝ → ℝ) (hc : Continuous φ)
    (hs : HasCompactSupport φ) (r : ℝ) :
    inner ℝ (IBMPhysicalDerivativeKernel.translatedClass (IBMMollifier.kernel n)
        (IBMMollifier.kernel_smooth n).continuous (IBMMollifier.kernel_compactSupport n) r)
      (testClass φ hc hs) = IBMMollifiedScenery.U (IBMMollifier.kernel n) φ r := by
  rw [L2_inner_eq_integral, convolution_swap]
  apply integral_congr_ae
  filter_upwards [IBMPhysicalDerivativeKernel.translatedClass_coeFn (IBMMollifier.kernel n)
    (IBMMollifier.kernel_smooth n).continuous (IBMMollifier.kernel_compactSupport n) r,
    testClass_ae φ hc hs] with x hr hφ
  rw [hr, hφ, Real.inner_apply, mul_comm]

def occupationIntegrand (h : CoefficientSpace) (φ : ℝ → ℝ) (ζ : GaussianL2)
    (p : ℝ × SampleSpace) : ℝ :=
  inner ℝ h (IBMClockAverageCandidate.direction p.1) *
    BrownianSignIntegral.signum (IBMConstructedSources.clockPath p.2 p.1.toNNReal) *
      φ |IBMConstructedSources.clockPath p.2 p.1.toNNReal| * ζ p.2

theorem occupationIntegrand_measurable (h : CoefficientSpace) (φ : ℝ → ℝ)
    (hc : Continuous φ) (ζ : GaussianL2) : Measurable (occupationIntegrand h φ ζ) := by
  have hd : Measurable (fun t : ℝ => inner ℝ h (IBMClockAverageCandidate.direction t)) :=
    (continuous_const.inner IBMClockAverageCandidate.direction_continuous).measurable
  have hb := BrownianClockWeightedEnergy.sigma_measurable
  exact (((hd.comp measurable_fst).mul (BrownianSignIntegral.signum_measurable.comp hb)).mul
    (hc.measurable.comp (continuous_abs.measurable.comp hb))).mul
      ((Lp.stronglyMeasurable ζ).measurable.comp measurable_snd)

theorem occupationIntegrand_bound (h : CoefficientSpace) (φ : ℝ → ℝ)
    (ζ : GaussianL2) {M : ℝ} (_hM : 0 ≤ M) (hb : ∀ x, ‖φ x‖ ≤ M)
    (T : ℝ≥0) (p : ℝ × SampleSpace) (hp : p.1 ∈ Ioc 0 (T : ℝ)) :
    ‖occupationIntegrand h φ ζ p‖ ≤ (‖h‖ * Real.sqrt T * M) * ‖ζ p.2‖ := by
  have hd := IBMClockAverageCandidate.direction_norm_bound T.property hp
  have hi : ‖inner ℝ h (IBMClockAverageCandidate.direction p.1)‖ ≤ ‖h‖ * Real.sqrt T :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hd (norm_nonneg _))
  rw [occupationIntegrand, norm_mul, norm_mul, norm_mul]
  calc
    _ ≤ ((‖h‖ * Real.sqrt T) * 1 * M) * ‖ζ p.2‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul _ (hb _) (norm_nonneg _) (by positivity)
      exact mul_le_mul hi (BrownianSignIntegral.signum_bound _) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem occupationIntegrand_integrable (h : CoefficientSpace) (φ : ℝ → ℝ)
    (hc : Continuous φ) (ζ : GaussianL2) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, ‖φ x‖ ≤ M) (T : ℝ≥0) :
    Integrable (occupationIntegrand h φ ζ) ((window T).prod gaussianProduct) := by
  have hm := (integrable_const (‖h‖ * Real.sqrt T * M) :
    Integrable (fun _ : ℝ => ‖h‖ * Real.sqrt T * M) (window T)).mul_prod
      (((Lp.memLp ζ).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).norm)
  apply hm.mono' (occupationIntegrand_measurable h φ hc ζ).aestronglyMeasurable
  filter_upwards [(Measure.quasiMeasurePreserving_fst
    (μ := window T) (ν := gaussianProduct)).ae (ae_restrict_mem measurableSet_Ioc)] with p hp
  exact occupationIntegrand_bound h φ ζ hM hb T p hp

theorem convolution_integral_tendsto (h : CoefficientSpace) (φ : ℝ → ℝ)
    (hc : Continuous φ) (ζ : GaussianL2) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, ‖φ x‖ ≤ M) (T : ℝ≥0) :
    Tendsto (fun n => ∫ p, occupationIntegrand h
        (IBMMollifiedScenery.U (IBMMollifier.kernel n) φ) ζ p
        ∂(window T).prod gaussianProduct) atTop
      (𝓝 (∫ p, occupationIntegrand h φ ζ p ∂(window T).prod gaussianProduct)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun p : ℝ × SampleSpace => (‖h‖ * Real.sqrt T * M) * ‖ζ p.2‖)
  · intro n
    exact (occupationIntegrand_measurable h _
      (convolution_continuous n φ hc) ζ).aestronglyMeasurable
  · exact (integrable_const (‖h‖ * Real.sqrt T * M) :
      Integrable (fun _ : ℝ => ‖h‖ * Real.sqrt T * M) (window T)).mul_prod
        (((Lp.memLp ζ).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).norm)
  · intro n
    filter_upwards [(Measure.quasiMeasurePreserving_fst
      (μ := window T) (ν := gaussianProduct)).ae (ae_restrict_mem measurableSet_Ioc)] with p hp
    exact occupationIntegrand_bound h _ ζ hM (convolution_bound n φ hM hb) T p hp
  · exact ae_of_all _ fun p => by
      exact (tendsto_const_nhds.mul (IBMMollifier.convolution_tendsto φ hc
        |IBMConstructedSources.clockPath p.2 p.1.toNNReal|)).mul tendsto_const_nhds

theorem recovered_slice_pairing (n : ℕ) (t : ℝ≥0) (φ : ℝ → ℝ)
    (hc : Continuous φ) (hs : HasCompactSupport φ) (ζ : GaussianL2) :
    inner ℝ (recover (signedSource n t))
      (BochnerClosedOperator.tensor gaussianProduct ζ (testClass φ hc hs)) =
    ∫ Y, BrownianSignIntegral.signum (IBMConstructedSources.clockPath Y t) *
      IBMMollifiedScenery.U (IBMMollifier.kernel n) φ
        |IBMConstructedSources.clockPath Y t| * ζ Y ∂gaussianProduct := by
  rw [L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [recovered_signedSource_ae n t,
    BochnerClosedOperator.tensor_coeFn gaussianProduct ζ (testClass φ hc hs)] with Y hr ht
  rw [hr, ht, real_inner_smul_left, real_inner_smul_right, translated_test]
  ring

theorem direction_toNNReal (t : ℝ) :
    IBMClockAverageCandidate.direction (t.toNNReal : ℝ) = IBMClockAverageCandidate.direction t := by
  simp only [IBMClockAverageCandidate.direction, Real.toNNReal_coe]

theorem kernelApprox_pairing (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0)
    (φ : ℝ → ℝ) (hc : Continuous φ) (hs : HasCompactSupport φ) (ζ : GaussianL2)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, ‖φ x‖ ≤ M) :
    inner ℝ (kernelApprox h n T)
        (BochnerClosedOperator.tensor gaussianProduct ζ (testClass φ hc hs)) =
      ∫ p, occupationIntegrand h (IBMMollifiedScenery.U (IBMMollifier.kernel n) φ) ζ p
        ∂(window T).prod gaussianProduct := by
  rw [kernelApprox_integral, real_inner_comm,
    ← integral_inner (kernelApprox_integrable h n T),
    integral_prod _ (occupationIntegrand_integrable h _ (convolution_continuous n φ hc)
      ζ hM (convolution_bound n φ hM hb) T)]
  apply integral_congr_ae
  exact ae_of_all _ fun t => by
    dsimp only
    rw [real_inner_comm, real_inner_smul_left, recovered_slice_pairing, ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun Y => by
      simp only [occupationIntegrand, direction_toNNReal]
      ring

theorem actual_occupation_integrable (h : CoefficientSpace) (T : ℝ≥0)
    (φ : ℝ → ℝ) (hc : Continuous φ) (hs : HasCompactSupport φ) (ζ : GaussianL2) :
    Integrable (occupationIntegrand h φ ζ) ((window T).prod gaussianProduct) := by
  obtain ⟨M, hM⟩ := hc.norm.bddAbove_range_of_hasCompactSupport hs.norm
  exact occupationIntegrand_integrable h φ hc ζ
    ((norm_nonneg (φ 0)).trans (hM ⟨0, rfl⟩)) (fun x => hM ⟨x, rfl⟩) T

/-- Actual signed occupation identity for every continuous compactly supported
spatial test and every clock-L2 weight. No local-time density is assumed. -/
theorem kernel_occupation_pairing (h : CoefficientSpace) (T : ℝ≥0)
    (φ : ℝ → ℝ) (hc : Continuous φ) (hs : HasCompactSupport φ) (ζ : GaussianL2) :
    inner ℝ (kernel h T) (BochnerClosedOperator.tensor gaussianProduct ζ (testClass φ hc hs)) =
      ∫ p, occupationIntegrand h φ ζ p ∂(window T).prod gaussianProduct := by
  obtain ⟨M, hM⟩ := hc.norm.bddAbove_range_of_hasCompactSupport hs.norm
  have hM0 : 0 ≤ M := (norm_nonneg (φ 0)).trans (hM ⟨0, rfl⟩)
  have hb : ∀ x, ‖φ x‖ ≤ M := fun x => hM ⟨x, rfl⟩
  have hk := kernel_pairing_tendsto h T
    (BochnerClosedOperator.tensor gaussianProduct ζ (testClass φ hc hs))
  have hi := convolution_integral_tendsto h φ hc ζ hM0 hb T
  have he (n : ℕ) := kernelApprox_pairing h n T φ hc hs ζ hM0 hb
  simp_rw [he] at hk
  exact tendsto_nhds_unique hk hi

/-- The same identity against the actual samplewise signed time integral.
Fubini is justified for every clock-L2 weight, not postulated. -/
theorem kernel_actual_time_pairing (h : CoefficientSpace) (T : ℝ≥0)
    (φ : ℝ → ℝ) (hc : Continuous φ) (hs : HasCompactSupport φ) (ζ : GaussianL2) :
    inner ℝ (kernel h T) (BochnerClosedOperator.tensor gaussianProduct ζ (testClass φ hc hs)) =
      ∫ Y, (∫ t : ℝ, inner ℝ h (IBMClockAverageCandidate.direction t) *
        BrownianSignIntegral.signum (IBMConstructedSources.clockPath Y t.toNNReal) *
          φ |IBMConstructedSources.clockPath Y t.toNNReal| ∂window T) * ζ Y ∂gaussianProduct := by
  rw [kernel_occupation_pairing,
    integral_prod_symm _ (actual_occupation_integrable h T φ hc hs ζ)]
  apply integral_congr_ae
  exact ae_of_all _ fun Y => by
    simp only [occupationIntegrand, integral_mul_const]

end OperatorDerivativeRewrite.Foundation.IBMClockOccupationTests
