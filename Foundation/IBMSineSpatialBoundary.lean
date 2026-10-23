import Foundation.IBMNonlinearSpatialOperator

/-! Smooth spatial tests with the necessary Brownian boundary terms. These
supply an actual strong convergence core for the local rough-test operators. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSineSpatialBoundary
open InfiniteGaussian IBMMollifiedScenery IBMSineSpatialDistribution
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
attribute [local irreducible] path IBMSineSpatialDistribution.tested

def tested (φ : ℝ → ℝ) (a b : ℝ) (X : ℝ → ℝ) : ℝ :=
  φ b * Real.sin (X b) - φ a * Real.sin (X a) + IBMSineSpatialDistribution.tested φ a b X

theorem mollified_identity (φ X : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hX : Continuous X) (a b : ℝ) (n : ℕ) :
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
  simpa only [tested, IBMSineSpatialDistribution.tested, sub_eq_add_neg, Function.comp_def] using hi

theorem tested_bound (φ X : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (hX : Continuous X)
    {a b : ℝ} (hab : a ≤ b) :
    ‖tested φ a b X‖ ≤ ‖φ b‖+‖φ a‖+(∫ r in a..b, ‖deriv φ r‖) := by
  have hb : ‖φ b * Real.sin (X b)‖ ≤ ‖φ b‖ := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (norm_nonneg _)).trans_eq (mul_one _)
  have ha : ‖φ a * Real.sin (X a)‖ ≤ ‖φ a‖ := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (norm_nonneg _)).trans_eq (mul_one _)
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add hb ha))
    (IBMSineSpatialDistribution.tested_bound φ X hφ hX hab))

theorem tested_tendsto (φ X : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (hX : Continuous X)
    {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun n => tested φ a b (U (IBMMollifier.kernel n) X)) atTop
      (𝓝 (tested φ a b X)) := by
  have hb := (tendsto_const_nhds (x := φ b)).mul
    (Real.continuous_sin.continuousAt.tendsto.comp (IBMMollifier.convolution_tendsto X hX b))
  have ha := (tendsto_const_nhds (x := φ a)).mul
    (Real.continuous_sin.continuousAt.tendsto.comp (IBMMollifier.convolution_tendsto X hX a))
  exact (hb.sub ha).add (IBMSineSpatialDistribution.tested_tendsto φ X hφ hX hab)

def sample (φ : ℝ → ℝ) (a b : ℝ) (n : Option ℕ) (ω : SampleSpace) : ℝ :=
  tested φ a b (path n ω)

theorem sample_measurable (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    {a b : ℝ} (hab : a ≤ b) (n : Option ℕ) : Measurable (sample φ a b n) := by
  have hp (r : ℝ) : Measurable (fun ω => path n ω r) :=
    (path_measurable n).comp (measurable_const.prodMk measurable_id)
  change Measurable (fun ω => φ b * Real.sin (path n ω b) -
    φ a * Real.sin (path n ω a) + IBMSineSpatialDistribution.sample φ a b n ω)
  exact (((Real.continuous_sin.measurable.comp (hp b)).const_mul _).sub
    ((Real.continuous_sin.measurable.comp (hp a)).const_mul _)).add
      (IBMSineSpatialDistribution.sample_measurable φ hφ hab n)

theorem sample_memLp (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    {a b : ℝ} (hab : a ≤ b) (n : Option ℕ) : MemLp (sample φ a b n) 2 gaussianProduct :=
  MemLp.of_bound (sample_measurable φ hφ hab n).aestronglyMeasurable
    (‖φ b‖+‖φ a‖+(∫ r in a..b, ‖deriv φ r‖))
    (ae_of_all _ fun ω => tested_bound φ _ hφ (path_continuous n ω) hab)

def boundaryClass (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    {a b : ℝ} (hab : a ≤ b) (n : Option ℕ) : GaussianL2 :=
  (sample_memLp φ hφ hab n).toLp (sample φ a b n)

theorem boundaryClass_ae (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    {a b : ℝ} (hab : a ≤ b) (n : Option ℕ) :
    boundaryClass φ hφ hab n =ᵐ[gaussianProduct] sample φ a b n := MemLp.coeFn_toLp _

theorem boundaryClass_tendsto (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun n => boundaryClass φ hφ hab (some n)) atTop
      (𝓝 (boundaryClass φ hφ hab none)) := by
  apply FiniteMeasureL2Dominated.toLp_tendsto_of_constant_bound
    (fun n => sample φ a b (some n)) (sample φ a b none)
    (fun n => sample_memLp φ hφ hab (some n)) (sample_memLp φ hφ hab none)
    (‖φ b‖+‖φ a‖+(∫ r in a..b, ‖deriv φ r‖))
    (add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
      (intervalIntegral.integral_nonneg hab (fun _ _ => norm_nonneg _)))
  · exact fun n => ae_of_all _ fun ω => tested_bound φ _ hφ (path_continuous _ ω) hab
  · exact ae_of_all _ fun ω => tested_bound φ _ hφ (path_continuous _ ω) hab
  · exact ae_of_all _ fun ω => by
      simpa only [sample, path] using tested_tendsto φ _ hφ
        (IBMConstructedSources.sceneryPath ω).continuous hab

theorem original_bochner_eq (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    (∫ r in a..b, φ r • IBMNonlinearClockColumn.column n r) = boundaryClass φ hφ hab (some n) := by
  apply Lp.ext
  filter_upwards [IBMCanonicalMollifiedScenery.original_bochner_ae φ hφ.continuous hab n,
    boundaryClass_ae φ hφ hab (some n),
    IBMCanonicalMollifiedScenery.nonlinear_common_path_ae] with ω ho hb hn
  rw [ho, hb]
  change (∫ r in a..b, φ r * IBMNonlinearClockColumn.value n r ω) = _
  rw [show sample φ a b (some n) ω =
      tested φ a b (U (IBMMollifier.kernel n) (IBMConstructedSources.sceneryPath ω)) from by simp only [sample, path],
    ← mollified_identity φ _ hφ (IBMConstructedSources.sceneryPath ω).continuous a b n]
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  rw [hn n r]

theorem original_bochner_tendsto (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun n => ∫ r in a..b, φ r • IBMNonlinearClockColumn.column n r) atTop
      (𝓝 (boundaryClass φ hφ hab none)) := by
  simpa only [original_bochner_eq φ hφ hab] using boundaryClass_tendsto φ hφ hab

/-- A genuine smooth convergence core, with NO endpoint vanishing assumption. -/
theorem operator_core_tendsto (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    {a b : ℝ} (hab : a ≤ b) (u : IBMNonlinearSpatialOperator.Space a b)
    (hu : u =ᵐ[volume.restrict (Ioc a b)] φ) :
    Tendsto (fun n => IBMNonlinearSpatialOperator.operator n hab u) atTop
      (𝓝 (boundaryClass φ hφ hab none)) := by
  have he (n : ℕ) : IBMNonlinearSpatialOperator.operator n hab u =
      ∫ r in a..b, φ r • IBMNonlinearClockColumn.column n r := by
    rw [IBMNonlinearSpatialOperator.operator_apply, intervalIntegral.integral_of_le hab]
    exact integral_congr_ae (hu.mono fun r hr => by dsimp only; rw [hr])
  simp_rw [he]
  exact original_bochner_tendsto φ hφ hab

end OperatorDerivativeRewrite.Foundation.IBMSineSpatialBoundary
