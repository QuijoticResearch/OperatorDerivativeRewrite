import Foundation.IBMNonlinearClockColumn
import Foundation.IBMSineSpatialDistribution
import Foundation.BochnerL2RepresentativeFubini

/-! The original Gaussian scenery mollifier fields are the actual convolutions
of the canonical continuous Brownian scenery, on one event for all spatial
coordinates. This connects native nonlinear columns to pathwise distributions. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology Convolution
namespace OperatorDerivativeRewrite.Foundation.IBMCanonicalMollifiedScenery
open InfiniteGaussian IBMContinuousScenery IBMMollifiedScenery
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

/-- Literal canonical convolution represents the original Gaussian-L2 convolution. -/
theorem wholeLine_path_ae (ρ : ℝ → ℝ) (hc : Continuous ρ) (hs : HasCompactSupport ρ)
    (x : ℝ) : wholeLineScenery ρ x =ᵐ[gaussianProduct] fun ω =>
      U ρ (IBMConstructedSources.sceneryPath ω) x := by
  let w : ℝ → ℝ := fun r => ρ (x-r)
  have hwc : Continuous w := hc.comp (continuous_const.sub continuous_id)
  have hws : HasCompactSupport w := hs.comp_homeomorph (Homeomorph.subLeft x)
  let μ : Measure ℝ := volume.restrict (tsupport w)
  letI : IsFiniteMeasure μ := ⟨by
    simpa only [μ, Measure.restrict_apply_univ] using hws.measure_lt_top⟩
  let v : ℝ → GaussianL2 := fun r => w r • sourceScenery r
  have hv : Integrable v μ :=
    ((hwc.smul sourceScenery_continuous).integrable_of_hasCompactSupport
      hws.smul_right).integrableOn
  let g : ℝ × SampleSpace → ℝ := fun p => w p.1 * IBMConstructedSources.sceneryPath p.2 p.1
  have hsc : Measurable (fun p : ℝ × SampleSpace =>
      IBMConstructedSources.sceneryPath p.2 p.1) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun ω => (IBMConstructedSources.sceneryPath ω).continuous)
      (fun r => (ContinuousMap.measurable_eval r).comp
        IBMConstructedSources.sceneryPath_measurable)
  have hg : StronglyMeasurable g :=
    ((hwc.measurable.comp measurable_fst).mul hsc).stronglyMeasurable
  have hrep : ∀ᵐ r ∂μ, v r =ᵐ[gaussianProduct] fun ω => g (r,ω) :=
    ae_of_all _ fun r => by
      filter_upwards [Lp.coeFn_smul (w r) (sourceScenery r),
        IBMConstructedSources.sceneryPath_coordinate_ae r] with ω hv hs
      rw [hv, Pi.smul_apply]
      change w r * sourceScenery r ω = w r * IBMConstructedSources.sceneryPath ω r
      rw [hs]
      rfl
  have he := BochnerL2RepresentativeFubini.integral_coeFn_ae v hv g
    hg.aestronglyMeasurable hrep
  have hvfull : (∫ r, v r ∂μ) = wholeLineScenery ρ x := by
    rw [wholeLineScenery_eq_integral]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun r hr => by simp [v, image_eq_zero_of_notMem_tsupport hr])
  rw [hvfull] at he
  filter_upwards [he] with ω hω
  rw [hω]
  change (∫ r in tsupport w, w r * IBMConstructedSources.sceneryPath ω r) = _
  rw [show U ρ (IBMConstructedSources.sceneryPath ω) x =
      ∫ r, ρ (x-r) * IBMConstructedSources.sceneryPath ω r from convolution_lsmul_swap]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun r hr => by simp [image_eq_zero_of_notMem_tsupport hr])

/-- Fixed-coordinate identity on the ORIGINAL source, not equality in law. -/
theorem field_path_coordinate_ae (n : ℕ) (i : Fin 3) (r : ℝ) :
    (fun ω => IBMDyadicExtension.field n i ω r) =ᵐ[gaussianProduct] fun ω =>
      U (IBMJointMollifierGaussian.derivativeKernel n i)
        (IBMConstructedSources.sceneryPath ω) r := by
  have hf := (IBMPointwiseEvaluation.field_memLp n i r).coeFn_toLp
  rw [IBMPointwiseEvaluation.field_toLp_eq] at hf
  exact hf.symm.trans (wholeLine_path_ae _
    (IBMDyadicExtension.derivativeKernel_regular n i).2.continuous
    (IBMDyadicExtension.derivativeKernel_regular n i).1 r)

/-- One source event for every original scale, derivative channel and real point.
Continuity and rational density replace an invalid uncountable AE intersection. -/
theorem fields_common_path_ae : ∀ᵐ ω ∂gaussianProduct, ∀ (n : ℕ) (i : Fin 3) (r : ℝ),
    IBMDyadicExtension.field n i ω r =
      U (IBMJointMollifierGaussian.derivativeKernel n i)
        (IBMConstructedSources.sceneryPath ω) r := by
  apply ae_all_iff.mpr
  intro n
  apply ae_all_iff.mpr
  intro i
  filter_upwards [ae_all_iff.mpr (fun q : ℚ => field_path_coordinate_ae n i q)] with ω hω
  have he : IBMDyadicExtension.field n i ω =
      U (IBMJointMollifierGaussian.derivativeKernel n i)
        (IBMConstructedSources.sceneryPath ω) := by
    apply Rat.denseRange_cast.equalizer (IBMDyadicExtension.field_continuous n i ω)
    · exact (IBMDyadicExtension.derivativeKernel_regular n i).1.continuous_convolution_left
        (ContinuousLinearMap.lsmul ℝ ℝ)
        (IBMDyadicExtension.derivativeKernel_regular n i).2.continuous
        (IBMConstructedSources.sceneryPath ω).continuous.locallyIntegrable
    · exact funext hω
  exact congrFun he

/-- Original nonlinear source columns equal canonical smooth cos(U)*V, on the
same event for every spatial point, not merely coordinatewise in law. -/
theorem nonlinear_common_path_ae : ∀ᵐ ω ∂gaussianProduct, ∀ (n : ℕ) (r : ℝ),
    IBMNonlinearClockColumn.value n r ω =
      Real.cos (U (IBMMollifier.kernel n) (IBMConstructedSources.sceneryPath ω) r) *
        V (IBMMollifier.kernel n) (IBMConstructedSources.sceneryPath ω) r := by
  filter_upwards [fields_common_path_ae] with ω hω
  intro n r
  have h0 := hω n 0 r
  have h1 := hω n 1 r
  simpa [IBMNonlinearClockColumn.value, IBMJointMollifierGaussian.derivativeKernel,
    V, U] using congrArg₂ (fun u v : ℝ => Real.cos u * v) h0 h1

open IBMSineSpatialDistribution

def originalIntegral (φ : ℝ → ℝ) (a b : ℝ) (n : ℕ) (ω : SampleSpace) : ℝ :=
  ∫ r in a..b, φ r * IBMNonlinearClockColumn.value n r ω

theorem originalIntegral_representation (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    {a b : ℝ} (hab : a ≤ b) (ha : φ a = 0) (hb : φ b = 0) (n : ℕ) :
    sourceClass φ hφ hab (some n) =ᵐ[gaussianProduct] originalIntegral φ a b n := by
  filter_upwards [sourceClass_actual_derivative φ hφ hab ha hb n,
    nonlinear_common_path_ae] with ω hω hn
  rw [hω, originalIntegral]
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  rw [hn n r]

theorem weighted_column_integrable (φ : ℝ → ℝ) (hc : Continuous φ)
    (a b : ℝ) (n : ℕ) :
    IntegrableOn (fun r => φ r • IBMNonlinearClockColumn.column n r) (Ioc a b) volume := by
  obtain ⟨C,hC,hb⟩ := IBMNonlinearClockColumn.column_bounded n
  have hi : Integrable (fun r => ‖φ r‖ * C) (volume.restrict (Ioc a b)) :=
    ((hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self).norm.mul_const C
  apply hi.mono'
    (hc.stronglyMeasurable.smul (IBMNonlinearClockColumn.column_stronglyMeasurable n)).aestronglyMeasurable
  exact ae_of_all _ fun r => by
    change ‖φ r • IBMNonlinearClockColumn.column n r‖ ≤ ‖φ r‖ * C
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hb r) (abs_nonneg _)

/-- Actual scalar representative of the genuine ORIGINAL Bochner source-column integral. -/
theorem original_bochner_ae (φ : ℝ → ℝ) (hc : Continuous φ)
    {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    (∫ r in a..b, φ r • IBMNonlinearClockColumn.column n r) =ᵐ[gaussianProduct]
      originalIntegral φ a b n := by
  have hg : StronglyMeasurable (fun p : ℝ × SampleSpace =>
      φ p.1 * IBMNonlinearClockColumn.value n p.1 p.2) :=
    ((hc.measurable.comp measurable_fst).mul
      (IBMNonlinearClockColumn.value_measurable n)).stronglyMeasurable
  have he := BochnerL2RepresentativeFubini.integral_coeFn_ae
    (fun r => φ r • IBMNonlinearClockColumn.column n r)
    (weighted_column_integrable φ hc a b n) _ hg.aestronglyMeasurable
    (ae_of_all _ fun r => by
      filter_upwards [Lp.coeFn_smul (φ r) (IBMNonlinearClockColumn.column n r),
        IBMNonlinearClockColumn.column_actual_ae n r] with ω hs hc
      rw [hs, Pi.smul_apply, hc]
      rfl)
  rw [intervalIntegral.integral_of_le hab]
  filter_upwards [he] with ω hω
  change _ = ∫ r in a..b, φ r * IBMNonlinearClockColumn.value n r ω
  rw [intervalIntegral.integral_of_le hab]
  exact hω

theorem original_bochner_eq (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    {a b : ℝ} (hab : a ≤ b) (ha : φ a = 0) (hb : φ b = 0) (n : ℕ) :
    (∫ r in a..b, φ r • IBMNonlinearClockColumn.column n r) = sourceClass φ hφ hab (some n) :=
  Lp.ext ((original_bochner_ae φ hφ.continuous hab n).trans
    (originalIntegral_representation φ hφ hab ha hb n).symm)

/-- Strong stochastic convergence of genuine ORIGINAL nonlinear-column Bochner integrals. -/
theorem original_bochner_tendsto (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    {a b : ℝ} (hab : a ≤ b) (ha : φ a = 0) (hb : φ b = 0) :
    Tendsto (fun n => ∫ r in a..b, φ r • IBMNonlinearClockColumn.column n r) atTop
      (𝓝 (sourceClass φ hφ hab none)) := by
  simpa only [original_bochner_eq φ hφ hab ha hb] using sourceClass_tendsto φ hφ hab

end OperatorDerivativeRewrite.Foundation.IBMCanonicalMollifiedScenery
