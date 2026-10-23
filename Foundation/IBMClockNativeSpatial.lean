import Foundation.IBMClockNativeOccupation
import Foundation.BochnerL2MajorantRealization

/-! Actual scalar spatial representatives of the original finite-width clock
kernels, with a genuine compact spatial L2 majorant for each continuous clock
sample. This identifies the native kernels with spatial smoothing of the limit. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockNativeSpatial
open InfiniteGaussian GaussianTimeHilbert IBMClockPhysicalOccupation
open IBMClockOccupationConvolution IBMClockNativeOccupation IBMClockOverlapEnergy
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem clock_bound (T : ℝ≥0) (Y : SampleSpace) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Ioc 0 (T : ℝ),
      |IBMConstructedSources.clockPath Y t.toNNReal| ≤ R := by
  have hc : Continuous (fun t : ℝ => |IBMConstructedSources.clockPath Y t.toNNReal|) :=
    ((IBMConstructedSources.clockPath Y).continuous.comp continuous_real_toNNReal).abs
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hc.continuousOn
  refine ⟨|M| + 1, by positivity, fun t ht => ?_⟩
  have hb : |IBMConstructedSources.clockPath Y t.toNNReal| ≤ M :=
    hM (Set.mem_image_of_mem _ ⟨ht.1.le, ht.2⟩)
  exact hb.trans ((le_abs_self M).trans (by linarith))

theorem kernel_zero_of_far (n : ℕ) (r : ℝ) (hr : (IBMMollifier.bump n).rOut ≤ |r|) :
    IBMMollifier.kernel n r = 0 := by
  by_contra hne
  have hm : r ∈ Function.support (IBMMollifier.kernel n) := hne
  rw [IBMMollifier.kernel, (IBMMollifier.bump n).support_normed_eq] at hm
  exact (not_lt.mpr hr) (by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hm)

theorem fieldValue_spatial_ae (h : CoefficientSpace) (n : ℕ) (t : ℝ) (Y : SampleSpace) :
    fieldValue h n (t,Y) =ᵐ[volume] fun x => occupationValue h n (t,(x,Y)) := by
  let a := inner ℝ h (IBMClockAverageCandidate.direction t) *
    BrownianSignIntegral.signum (IBMConstructedSources.clockPath Y t.toNNReal)
  have hs := Lp.coeFn_smul a (profileClass n |IBMConstructedSources.clockPath Y t.toNNReal|)
  have hp := IBMPhysicalDerivativeKernel.translatedClass_coeFn (IBMMollifier.kernel n)
    (IBMMollifier.kernel_smooth n).continuous (IBMMollifier.kernel_compactSupport n)
      |IBMConstructedSources.clockPath Y t.toNNReal|
  filter_upwards [hs, hp] with x hs hp
  change fieldValue h n (t,Y) x = _ at hs
  change profileClass n |IBMConstructedSources.clockPath Y t.toNNReal| x = _ at hp
  rw [hs, Pi.smul_apply, hp]
  rfl

theorem scalar_stronglyMeasurable (h : CoefficientSpace) (n : ℕ) (Y : SampleSpace) :
    StronglyMeasurable (fun p : ℝ × ℝ => occupationValue h n (p.1,(p.2,Y))) :=
  (occupationValue_measurable h n).stronglyMeasurable.comp_measurable
    (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))

theorem spatial_majorant (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0) (Y : SampleSpace) :
    ∃ B : ℝ → ℝ, MemLp B 2 volume ∧
      ∀ᵐ p : ℝ × ℝ ∂(window T).prod volume,
        ‖occupationValue h n (p.1,(p.2,Y))‖ ≤ B p.2 := by
  obtain ⟨R, hR, hclock⟩ := clock_bound T Y
  obtain ⟨M, hM⟩ :=
    (IBMMollifier.kernel_smooth n).continuous.norm.bddAbove_range_of_hasCompactSupport
      (IBMMollifier.kernel_compactSupport n).norm
  have hM0 : 0 ≤ M := (norm_nonneg (IBMMollifier.kernel n 0)).trans (hM ⟨0, rfl⟩)
  let S := R + (IBMMollifier.bump n).rOut + 1
  let C := ‖h‖ * Real.sqrt T * M
  let B : ℝ → ℝ := (Icc (-S) S).indicator (fun _ => C)
  have hB : MemLp B 2 volume := memLp_indicator_const 2 measurableSet_Icc C
    (.inr (by simp [Real.volume_Icc]))
  refine ⟨B, hB, ?_⟩
  filter_upwards [(Measure.quasiMeasurePreserving_fst
    (μ := window T) (ν := (volume : Measure ℝ))).ae (ae_restrict_mem measurableSet_Ioc)] with p ht
  change ‖occupationValue h n (p.1,(p.2,Y))‖ ≤ (Icc (-S) S).indicator (fun _ => C) p.2
  by_cases hx : p.2 ∈ Icc (-S) S
  · rw [indicator_of_mem hx, occupationValue_eq_test]
    exact IBMClockOccupationPath.value_bound h (profile n p.2) hM0
      (fun r => hM ⟨p.2-r, rfl⟩) T (p.1,Y) ht
  · rw [indicator_of_notMem hx]
    have hfar : (IBMMollifier.bump n).rOut ≤
        abs (|IBMConstructedSources.clockPath Y p.1.toNNReal| - p.2) := by
      have hb := hclock p.1 ht
      simp only [mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx | hx
      · have ha := le_abs_self (|IBMConstructedSources.clockPath Y p.1.toNNReal| - p.2)
        dsimp only [S] at hx
        linarith [abs_nonneg (IBMConstructedSources.clockPath Y p.1.toNNReal)]
      · have ha := neg_le_abs (|IBMConstructedSources.clockPath Y p.1.toNNReal| - p.2)
        dsimp only [S] at hx
        linarith
    simp only [occupationValue, kernel_zero_of_far n _ hfar, mul_zero, norm_zero, le_refl]

/-- Every continuous clock sample has a genuine spatial L2 time-integral
representative; spatial Lebesgue volume is not treated as finite. -/
theorem pathField_spatial_ae (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0) (Y : SampleSpace) :
    pathField h n T Y =ᵐ[volume] fun x => occupationConvolution h n T (x,Y) := by
  obtain ⟨B, hB, hb⟩ := spatial_majorant h n T Y
  exact BochnerL2MajorantRealization.integral_coeFn_ae
    (fun t : ℝ => fieldValue h n (t,Y)) (fieldValue_integrable h n T Y)
    (fun p : ℝ × ℝ => occupationValue h n (p.1,(p.2,Y))) (scalar_stronglyMeasurable h n Y)
    (ae_of_all _ fun t => fieldValue_spatial_ae h n t Y) B hB hb

theorem kernelApprox_spatial_ae (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0) :
    ∀ᵐ Y ∂gaussianProduct, kernelApprox h n T Y =ᵐ[volume]
      fun x => occupationConvolution h n T (x,Y) := by
  filter_upwards [kernelApprox_pathField_ae h n T] with Y hY
  rw [hY]
  exact pathField_spatial_ae h n T Y

/-- The original stored native L2 kernel really is spatial mollification of
the recovered kernel, with the actual samplewise occupation representative. -/
theorem kernelApprox_convolution_ae (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0) :
    ∀ᵐ Y ∂gaussianProduct, kernelApprox h n T Y =ᵐ[volume]
      fun x => kernelConvolution h n T (x,Y) := by
  filter_upwards [kernelApprox_spatial_ae h n T, convolution_clock_ae h n T] with Y hn hc
  exact hn.trans hc.symm

theorem kernelApprox_all_widths_ae (h : CoefficientSpace) (T : ℝ≥0) :
    ∀ᵐ Y ∂gaussianProduct, ∀ n, kernelApprox h n T Y =ᵐ[volume]
      fun x => kernelConvolution h n T (x,Y) :=
  ae_all_iff.mpr (fun n => kernelApprox_convolution_ae h n T)

end OperatorDerivativeRewrite.Foundation.IBMClockNativeSpatial
