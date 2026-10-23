import Foundation.IBMClockOccupationConvolution
import Foundation.BochnerL2Fubini

/-! Genuine samplewise physical-Hilbert realization of the original native
finite-width clock kernels. Integrability and the L2 representative are proved. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockNativeOccupation
open InfiniteGaussian GaussianTimeHilbert IBMFirstSourceClockGraph
open IBMClockPhysicalOccupation IBMClockOccupationConvolution IBMClockOverlapEnergy
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem profileClass_bounded (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ‖profileClass n r‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := IBMClockAverageCandidate.sourceColumn_bounded n
  refine ⟨C, hC, fun r => ?_⟩
  rw [← IBMPhysicalNoiseRealization.physicalNoise.norm_map (profileClass n r), profileClass_noise]
  exact hb r

def fieldValue (h : CoefficientSpace) (n : ℕ) (p : ℝ × SampleSpace) : TimeHilbert :=
  (inner ℝ h (IBMClockAverageCandidate.direction p.1) *
    BrownianSignIntegral.signum (IBMConstructedSources.clockPath p.2 p.1.toNNReal)) •
      profileClass n |IBMConstructedSources.clockPath p.2 p.1.toNNReal|

theorem fieldValue_stronglyMeasurable (h : CoefficientSpace) (n : ℕ) :
    StronglyMeasurable (fieldValue h n) := by
  have hb := BrownianClockWeightedEnergy.sigma_measurable
  have hd : StronglyMeasurable (fun t : ℝ => inner ℝ h (IBMClockAverageCandidate.direction t)) :=
    (continuous_const.inner IBMClockAverageCandidate.direction_continuous).stronglyMeasurable
  exact ((hd.comp_measurable measurable_fst).mul
    (BrownianSignIntegral.signum_measurable.comp hb).stronglyMeasurable).smul
      ((profileClass_continuous n).stronglyMeasurable.comp_measurable
        (continuous_abs.measurable.comp hb))

theorem fieldValue_bound (h : CoefficientSpace) (n : ℕ) {C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ r, ‖profileClass n r‖ ≤ C) (T : ℝ≥0)
    (p : ℝ × SampleSpace) (hp : p.1 ∈ Ioc 0 (T : ℝ)) :
    ‖fieldValue h n p‖ ≤ ‖h‖ * Real.sqrt T * C := by
  have hd := IBMClockAverageCandidate.direction_norm_bound T.property hp
  have hi : ‖inner ℝ h (IBMClockAverageCandidate.direction p.1)‖ ≤ ‖h‖ * Real.sqrt T :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hd (norm_nonneg _))
  rw [fieldValue, norm_smul, norm_mul]
  calc
    _ ≤ ((‖h‖ * Real.sqrt T) * 1) * C :=
      mul_le_mul (mul_le_mul hi (BrownianSignIntegral.signum_bound _)
        (norm_nonneg _) (by positivity)) (hb _) (norm_nonneg _) (by positivity)
    _ = _ := by ring

def field (h : CoefficientSpace) (n : ℕ) (t : ℝ) : Lp TimeHilbert 2 gaussianProduct :=
  inner ℝ h (IBMClockAverageCandidate.direction t) • recover (signedSource n t.toNNReal)

theorem field_ae (h : CoefficientSpace) (n : ℕ) (t : ℝ) :
    field h n t =ᵐ[gaussianProduct] fun Y => fieldValue h n (t,Y) := by
  filter_upwards [Lp.coeFn_smul (inner ℝ h (IBMClockAverageCandidate.direction t))
      (recover (signedSource n t.toNNReal)), recovered_signedSource_ae n t.toNNReal]
      with Y hs hr
  change field h n t Y = _ at hs
  rw [hs, Pi.smul_apply, hr, smul_smul]
  rfl

theorem field_integrable (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0) :
    Integrable (field h n) (window T) := by
  change Integrable (fun t : ℝ => inner ℝ h (IBMClockAverageCandidate.direction t) •
    recover (signedSource n t.toNNReal)) (window T)
  simpa only [IBMClockOccupationTests.direction_toNNReal] using
    kernelApprox_integrable h n T

theorem fieldValue_integrable (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0) (Y : SampleSpace) :
    Integrable (fun t : ℝ => fieldValue h n (t,Y)) (window T) := by
  obtain ⟨C, hC, hb⟩ := profileClass_bounded n
  apply Integrable.of_bound
    (((fieldValue_stronglyMeasurable h n).comp_measurable
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable) (‖h‖ * Real.sqrt T * C)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact fieldValue_bound h n hC hb T (t,Y) ht

def pathField (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0) (Y : SampleSpace) : TimeHilbert :=
  ∫ t : ℝ, fieldValue h n (t,Y) ∂window T

theorem pathField_stronglyMeasurable (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0) :
    StronglyMeasurable (pathField h n T) :=
  (fieldValue_stronglyMeasurable h n).integral_prod_left' (μ := window T)

theorem pathField_bound (h : CoefficientSpace) (n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ r, ‖profileClass n r‖ ≤ C) (T : ℝ≥0) (Y : SampleSpace) :
    ‖pathField h n T Y‖ ≤ (T : ℝ) * (‖h‖ * Real.sqrt T * C) := by
  have ha : ∀ᵐ t ∂window T, ‖fieldValue h n (t,Y)‖ ≤ ‖h‖ * Real.sqrt T * C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact fieldValue_bound h n hC hb T (t,Y) ht
  have hi := norm_integral_le_of_norm_le_const ha
  simpa [pathField, window, Measure.real, Real.volume_Ioc,
    ENNReal.toReal_ofReal T.property, mul_comm] using hi

theorem pathField_memLp (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0) :
    MemLp (pathField h n T) 2 gaussianProduct := by
  obtain ⟨C, hC, hb⟩ := profileClass_bounded n
  exact MemLp.of_bound (pathField_stronglyMeasurable h n T).aestronglyMeasurable
    ((T : ℝ) * (‖h‖ * Real.sqrt T * C)) (ae_of_all _ (pathField_bound h n hC hb T))

theorem kernelApprox_pathField_ae (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0) :
    kernelApprox h n T =ᵐ[gaussianProduct] pathField h n T := by
  obtain ⟨C, hC, hb⟩ := profileClass_bounded n
  let W := (pathField_memLp h n T).toLp (pathField h n T)
  have hmem : ∀ᵐ p : ℝ × SampleSpace ∂(window T).prod gaussianProduct, p.1 ∈ Ioc 0 (T : ℝ) :=
    (Measure.quasiMeasurePreserving_fst (μ := window T) (ν := gaussianProduct)).ae
      (ae_restrict_mem measurableSet_Ioc)
  have hbound : ∀ᵐ p : ℝ × SampleSpace ∂(window T).prod gaussianProduct,
      ‖fieldValue h n p‖ ≤ ‖h‖ * Real.sqrt T * C :=
    hmem.mono (fun p hp => fieldValue_bound h n hC hb T p hp)
  have he : (∫ t, field h n t ∂window T) = W :=
    BochnerL2Fubini.integral_eq_of_slices (field h n) (field_integrable h n T)
      (fieldValue h n) (fieldValue_stronglyMeasurable h n).aestronglyMeasurable
      (ae_of_all _ (field_ae h n)) (fun _ => ‖h‖ * Real.sqrt T * C)
      (memLp_const _) hbound W (MemLp.coeFn_toLp _)
  have hk : kernelApprox h n T = ∫ t, field h n t ∂window T := by
    simpa only [field, IBMClockOccupationTests.direction_toNNReal] using kernelApprox_integral h n T
  rw [hk, he]
  exact MemLp.coeFn_toLp _

end OperatorDerivativeRewrite.Foundation.IBMClockNativeOccupation
