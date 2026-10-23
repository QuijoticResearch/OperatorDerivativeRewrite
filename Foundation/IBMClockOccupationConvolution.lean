import Foundation.IBMClockOccupationPath

/-! Jointly measurable spatial mollification of the actual clock occupation
kernel. Product-measure Fubini replaces an invalid uncountable intersection
of the fixed-test null sets. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockOccupationConvolution
open InfiniteGaussian GaussianTimeHilbert IBMClockPhysicalOccupation
open IBMClockOccupationTests IBMClockOccupationPath IBMClockOverlapEnergy
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem kernel_even (n : ℕ) (r : ℝ) : IBMMollifier.kernel n (-r) = IBMMollifier.kernel n r :=
  (IBMMollifier.bump n).normed_neg (μ := volume) r

theorem kernel_sub_swap (n : ℕ) (a b : ℝ) :
    IBMMollifier.kernel n (a-b) = IBMMollifier.kernel n (b-a) := by
  simpa only [neg_sub] using kernel_even n (b-a)

def profile (n : ℕ) (x : ℝ) (r : ℝ) : ℝ := IBMMollifier.kernel n (x-r)

theorem profile_continuous (n : ℕ) (x : ℝ) : Continuous (profile n x) :=
  (IBMMollifier.kernel_smooth n).continuous.comp (continuous_const.sub continuous_id)

theorem profile_compact (n : ℕ) (x : ℝ) : HasCompactSupport (profile n x) :=
  (IBMMollifier.kernel_compactSupport n).comp_homeomorph (Homeomorph.subLeft x)

def profileClass (n : ℕ) (x : ℝ) : TimeHilbert :=
  IBMPhysicalDerivativeKernel.translatedClass (IBMMollifier.kernel n)
    (IBMMollifier.kernel_smooth n).continuous (IBMMollifier.kernel_compactSupport n) x

theorem profileClass_test (n : ℕ) (x : ℝ) :
    profileClass n x = testClass (profile n x) (profile_continuous n x) (profile_compact n x) := by
  apply Lp.ext
  exact (IBMPhysicalDerivativeKernel.translatedClass_coeFn _ _ _ x).trans
    (testClass_ae _ _ _).symm

theorem profileClass_noise (n : ℕ) (x : ℝ) :
    IBMPhysicalNoiseRealization.physicalNoise (profileClass n x) =
      IBMClockAverageCandidate.sourceColumn n x := by
  rw [profileClass, ← IBMPhysicalDerivativeKernel.derivative_eq_translated
    ((IBMMollifier.kernel_smooth n).of_le (by simp)) (IBMMollifier.kernel_compactSupport n)]
  exact sourceColumn_physical n x

theorem profileClass_continuous (n : ℕ) : Continuous (profileClass n) := by
  apply IBMPhysicalNoiseRealization.physicalNoise.isometry.comp_continuous_iff.mp
  simpa only [Function.comp_def, profileClass_noise] using
    IBMClockAverageCandidate.sourceColumn_continuous n

def kernelConvolution (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0)
    (p : ℝ × SampleSpace) : ℝ := inner ℝ (kernel h T p.2) (profileClass n p.1)

theorem kernelConvolution_measurable (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0) :
    Measurable (kernelConvolution h n T) := by
  exact (((Lp.stronglyMeasurable (kernel h T)).comp_measurable measurable_snd).inner
    (𝕜 := ℝ) ((profileClass_continuous n).stronglyMeasurable.comp_measurable
      measurable_fst)).measurable

def occupationValue (h : CoefficientSpace) (n : ℕ)
    (p : ℝ × (ℝ × SampleSpace)) : ℝ :=
  inner ℝ h (IBMClockAverageCandidate.direction p.1) *
    BrownianSignIntegral.signum (IBMConstructedSources.clockPath p.2.2 p.1.toNNReal) *
      IBMMollifier.kernel n (|IBMConstructedSources.clockPath p.2.2 p.1.toNNReal| - p.2.1)

theorem occupationValue_measurable (h : CoefficientSpace) (n : ℕ) :
    Measurable (occupationValue h n) := by
  have hb : Measurable (fun p : ℝ × (ℝ × SampleSpace) =>
      IBMConstructedSources.clockPath p.2.2 p.1.toNNReal) :=
    BrownianClockWeightedEnergy.sigma_measurable.comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hd : Measurable (fun t : ℝ => inner ℝ h (IBMClockAverageCandidate.direction t)) :=
    (continuous_const.inner IBMClockAverageCandidate.direction_continuous).measurable
  exact ((hd.comp measurable_fst).mul (BrownianSignIntegral.signum_measurable.comp hb)).mul
    ((IBMMollifier.kernel_smooth n).continuous.measurable.comp
      ((continuous_abs.measurable.comp hb).sub (measurable_fst.comp measurable_snd)))

def occupationConvolution (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0)
    (p : ℝ × SampleSpace) : ℝ := ∫ t : ℝ, occupationValue h n (t,p) ∂window T

theorem occupationConvolution_measurable (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0) :
    Measurable (occupationConvolution h n T) :=
  ((occupationValue_measurable h n).stronglyMeasurable.integral_prod_left'
    (μ := window T)).measurable

theorem occupationValue_eq_test (h : CoefficientSpace) (n : ℕ) (x t : ℝ)
    (Y : SampleSpace) : occupationValue h n (t,(x,Y)) = value h (profile n x) (t,Y) := by
  simp only [occupationValue, value, profile]
  rw [kernel_sub_swap]

theorem occupationValue_integrable (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0)
    (p : ℝ × SampleSpace) : Integrable (fun t : ℝ => occupationValue h n (t,p)) (window T) := by
  obtain ⟨M, hM⟩ := (profile_continuous n p.1).norm.bddAbove_range_of_hasCompactSupport
    (profile_compact n p.1).norm
  have hi := value_time_integrable h (profile n p.1) (profile_continuous n p.1)
    ((norm_nonneg (profile n p.1 0)).trans (hM ⟨0, rfl⟩))
    (fun x => hM ⟨x, rfl⟩) T p.2
  exact hi.congr (ae_of_all _ fun t => (occupationValue_eq_test h n p.1 t p.2).symm)

theorem occupationConvolution_eq_path (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0)
    (x : ℝ) (Y : SampleSpace) :
    occupationConvolution h n T (x,Y) = pathIntegral h (profile n x) T Y := by
  unfold occupationConvolution pathIntegral
  exact integral_congr_ae (ae_of_all _ fun t => occupationValue_eq_test h n x t Y)

theorem convolution_slice_ae (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0) (x : ℝ) :
    (fun Y => kernelConvolution h n T (x,Y)) =ᵐ[gaussianProduct]
      fun Y => occupationConvolution h n T (x,Y) := by
  have he := kernel_path_ae h (profile n x) (profile_continuous n x) (profile_compact n x) T
  simpa only [kernelConvolution, profileClass_test, occupationConvolution_eq_path] using he

/-- Joint measurability permits product Fubini; no uncountable null-set
intersection is taken. The spatial measure is the full Lebesgue measure. -/
theorem convolution_product_ae (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0) :
    kernelConvolution h n T =ᵐ[volume.prod gaussianProduct] occupationConvolution h n T := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (kernelConvolution_measurable h n T) (occupationConvolution_measurable h n T))).mpr
  exact ae_of_all _ (convolution_slice_ae h n T)

theorem convolution_clock_ae (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0) :
    ∀ᵐ Y ∂gaussianProduct, (fun x : ℝ => kernelConvolution h n T (x,Y)) =ᵐ[volume]
      fun x => occupationConvolution h n T (x,Y) := by
  exact Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp
      (convolution_product_ae h n T))

theorem convolution_all_widths_ae (h : CoefficientSpace) (T : ℝ≥0) :
    ∀ᵐ Y ∂gaussianProduct, ∀ n,
      (fun x : ℝ => kernelConvolution h n T (x,Y)) =ᵐ[volume]
        fun x => occupationConvolution h n T (x,Y) :=
  ae_all_iff.mpr (fun n => convolution_clock_ae h n T)

theorem kernelConvolution_integral (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0)
    (p : ℝ × SampleSpace) :
    kernelConvolution h n T p = ∫ r : ℝ, kernel h T p.2 r * IBMMollifier.kernel n (p.1-r) := by
  rw [kernelConvolution, profileClass_test, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [testClass_ae (profile n p.1) _ _] with r hr
  rw [hr, Real.inner_apply]
  rfl

end OperatorDerivativeRewrite.Foundation.IBMClockOccupationConvolution
