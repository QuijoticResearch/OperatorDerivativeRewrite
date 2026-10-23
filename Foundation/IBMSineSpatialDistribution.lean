import Foundation.IBMMollifier
import Foundation.IBMConstructedSources
import Foundation.IBMMollifiedMeasurability
import Foundation.FiniteMeasureL2Dominated
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Spatial distributional derivatives of sine of actual Brownian scenery.
This tests the nonlinear derivative against C1 functions vanishing at both
endpoints; it does not differentiate Brownian paths pointwise. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSineSpatialDistribution
open InfiniteGaussian IBMMollifiedScenery

def tested (φ : ℝ → ℝ) (a b : ℝ) (X : ℝ → ℝ) : ℝ :=
  -(∫ r in a..b, deriv φ r * Real.sin (X r))

theorem mollified_identity (φ X : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hX : Continuous X) (a b : ℝ) (ha : φ a = 0) (hb : φ b = 0) (n : ℕ) :
    (∫ r in a..b, φ r * (Real.cos (U (IBMMollifier.kernel n) X r) *
      V (IBMMollifier.kernel n) X r)) = tested φ a b (U (IBMMollifier.kernel n) X) := by
  have hU := U_hasDerivAt (IBMMollifier.kernel n) X (IBMMollifier.kernel_compactSupport n)
    ((IBMMollifier.kernel_smooth n).of_le (by norm_num)) hX
  have hcU : Continuous (U (IBMMollifier.kernel n) X) :=
    continuous_iff_continuousAt.mpr fun r => (hU r).continuousAt
  have hcV : Continuous (V (IBMMollifier.kernel n) X) :=
    continuous_iff_continuousAt.mpr fun r =>
      (V_hasDerivAt (IBMMollifier.kernel n) X (IBMMollifier.kernel_compactSupport n)
        ((IBMMollifier.kernel_smooth n).of_le (by norm_num)) hX r).continuousAt
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hφ.continuous.continuousOn (Real.continuous_sin.comp hcU).continuousOn
    (fun r _ => (hφ.differentiable (by norm_num) r).hasDerivAt)
    (fun r _ => (Real.hasDerivAt_sin _).comp r (hU r))
    ((hφ.continuous_deriv (by norm_num)).intervalIntegrable a b)
    (((Real.continuous_cos.comp hcU).mul hcV).intervalIntegrable a b)
  simpa [ha, hb, tested] using hi

theorem tested_bound (φ X : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (hX : Continuous X)
    {a b : ℝ} (hab : a ≤ b) :
    ‖tested φ a b X‖ ≤ ∫ r in a..b, ‖deriv φ r‖ := by
  rw [tested, norm_neg]
  apply (intervalIntegral.norm_integral_le_integral_norm hab).trans
  apply intervalIntegral.integral_mono_on hab
    (((hφ.continuous_deriv (by norm_num)).mul (Real.continuous_sin.comp hX)).norm.intervalIntegrable a b)
    (((hφ.continuous_deriv (by norm_num)).norm).intervalIntegrable a b)
  intro r _
  change ‖deriv φ r * Real.sin (X r)‖ ≤ ‖deriv φ r‖
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (norm_nonneg _)).trans_eq (mul_one _)

theorem tested_tendsto (φ X : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (hX : Continuous X)
    {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun n => tested φ a b (U (IBMMollifier.kernel n) X)) atTop
      (𝓝 (tested φ a b X)) := by
  unfold tested
  simp only [intervalIntegral.integral_of_le hab]
  apply Filter.Tendsto.neg
  apply tendsto_integral_of_dominated_convergence (fun r => ‖deriv φ r‖)
  · intro n
    exact (((hφ.continuous_deriv (by norm_num)).mul
      (Real.continuous_sin.comp (continuous_iff_continuousAt.mpr fun r =>
        (U_hasDerivAt (IBMMollifier.kernel n) X (IBMMollifier.kernel_compactSupport n)
          ((IBMMollifier.kernel_smooth n).of_le (by norm_num)) hX r).continuousAt))).aestronglyMeasurable)
  · exact ((hφ.continuous_deriv (by norm_num)).norm).integrableOn_Ioc
  · intro n
    exact ae_of_all _ fun r => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (norm_nonneg _)).trans_eq (mul_one _)
  · exact ae_of_all _ fun r => tendsto_const_nhds.mul
      (Real.continuous_sin.continuousAt.tendsto.comp (IBMMollifier.convolution_tendsto X hX r))

/-- The actual continuous Brownian scenery and its concrete smoothings. -/
def path (n : Option ℕ) (ω : SampleSpace) : ℝ → ℝ :=
  match n with
  | none => IBMConstructedSources.sceneryPath ω
  | some m => U (IBMMollifier.kernel m) (IBMConstructedSources.sceneryPath ω)

theorem path_continuous (n : Option ℕ) (ω : SampleSpace) : Continuous (path n ω) := by
  cases n with
  | none => exact (IBMConstructedSources.sceneryPath ω).continuous
  | some m => exact continuous_iff_continuousAt.mpr fun r =>
      (U_hasDerivAt (IBMMollifier.kernel m) _ (IBMMollifier.kernel_compactSupport m)
        ((IBMMollifier.kernel_smooth m).of_le (by norm_num))
        (IBMConstructedSources.sceneryPath ω).continuous r).continuousAt

theorem path_measurable (n : Option ℕ) :
    Measurable (fun p : ℝ × SampleSpace => path n p.2 p.1) := by
  have hm (r : ℝ) : Measurable (fun ω => IBMConstructedSources.sceneryPath ω r) :=
    (ContinuousMap.measurable_eval r).comp IBMConstructedSources.sceneryPath_measurable
  cases n with
  | none =>
      exact measurable_uncurry_of_continuous_of_measurable
        (fun ω => (IBMConstructedSources.sceneryPath ω).continuous) hm
  | some m =>
      exact IBMMollifiedMeasurability.U_joint_measurable (IBMMollifier.kernel m)
        (fun r ω => IBMConstructedSources.sceneryPath ω r)
        (IBMMollifier.kernel_compactSupport m)
        ((IBMMollifier.kernel_smooth m).of_le (by norm_num))
        (fun ω => (IBMConstructedSources.sceneryPath ω).continuous) hm

def sample (φ : ℝ → ℝ) (a b : ℝ) (n : Option ℕ) (ω : SampleSpace) : ℝ :=
  tested φ a b (path n ω)

theorem sample_measurable (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    {a b : ℝ} (hab : a ≤ b) (n : Option ℕ) : Measurable (sample φ a b n) := by
  have hi : StronglyMeasurable (fun p : SampleSpace × ℝ =>
      deriv φ p.2 * Real.sin (path n p.1 p.2)) :=
    (((hφ.continuous_deriv (by norm_num)).measurable.comp measurable_snd).mul
      (Real.continuous_sin.measurable.comp ((path_measurable n).comp measurable_swap))).stronglyMeasurable
  have hm := hi.integral_prod_right' (ν := volume.restrict (Ioc a b))
  change Measurable (fun ω => -(∫ r in a..b, deriv φ r * Real.sin (path n ω r)))
  convert hm.measurable.neg using 1
  funext ω
  rw [intervalIntegral.integral_of_le hab]
  rfl

theorem sample_memLp (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    {a b : ℝ} (hab : a ≤ b) (n : Option ℕ) :
    MemLp (sample φ a b n) 2 gaussianProduct :=
  MemLp.of_bound (sample_measurable φ hφ hab n).aestronglyMeasurable
    (∫ r in a..b, ‖deriv φ r‖)
    (ae_of_all _ fun ω => tested_bound φ _ hφ (path_continuous n ω) hab)

def sourceClass (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    {a b : ℝ} (hab : a ≤ b) (n : Option ℕ) : GaussianL2 :=
  (sample_memLp φ hφ hab n).toLp (sample φ a b n)

theorem sourceClass_ae (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    {a b : ℝ} (hab : a ≤ b) (n : Option ℕ) :
    sourceClass φ hφ hab n =ᵐ[gaussianProduct] sample φ a b n := MemLp.coeFn_toLp _

/-- Genuine strong source-L2 convergence of the tested nonlinear spatial derivative. -/
theorem sourceClass_tendsto (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun n => sourceClass φ hφ hab (some n)) atTop
      (𝓝 (sourceClass φ hφ hab none)) := by
  apply FiniteMeasureL2Dominated.toLp_tendsto_of_constant_bound
    (fun n => sample φ a b (some n)) (sample φ a b none)
    (fun n => sample_memLp φ hφ hab (some n)) (sample_memLp φ hφ hab none)
    (∫ r in a..b, ‖deriv φ r‖)
    (intervalIntegral.integral_nonneg hab (fun _ _ => norm_nonneg _))
  · exact fun n => ae_of_all _ fun ω => tested_bound φ _ hφ (path_continuous _ ω) hab
  · exact ae_of_all _ fun ω => tested_bound φ _ hφ (path_continuous _ ω) hab
  · exact ae_of_all _ fun ω => tested_tendsto φ _ hφ
      (IBMConstructedSources.sceneryPath ω).continuous hab

/-- Every finite stochastic approximant is an actual tested smooth spatial derivative. -/
theorem sourceClass_actual_derivative (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    {a b : ℝ} (hab : a ≤ b) (ha : φ a = 0) (hb : φ b = 0) (n : ℕ) :
    sourceClass φ hφ hab (some n) =ᵐ[gaussianProduct] fun ω =>
      ∫ r in a..b, φ r * (Real.cos (U (IBMMollifier.kernel n)
        (IBMConstructedSources.sceneryPath ω) r) *
          V (IBMMollifier.kernel n) (IBMConstructedSources.sceneryPath ω) r) := by
  filter_upwards [sourceClass_ae φ hφ hab (some n)] with ω hω
  exact hω.trans (mollified_identity φ _ hφ
    (IBMConstructedSources.sceneryPath ω).continuous a b ha hb n).symm

end OperatorDerivativeRewrite.Foundation.IBMSineSpatialDistribution
