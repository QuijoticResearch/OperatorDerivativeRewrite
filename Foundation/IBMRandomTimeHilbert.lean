import Foundation.IBMUniformSmoothing
import Foundation.IBMSourceLaws
import Mathlib.MeasureTheory.Function.L2Space

/-! Evaluation of Gaussian L² scenery classes at an independent Brownian clock.
The values are Hilbert classes over the scenery source, not sample-path values. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
open Filter
open scoped Topology

namespace OperatorDerivativeRewrite.Foundation.IBMRandomTimeHilbert
open InfiniteGaussian IBMContinuousScenery IBMMollifier
open GaussianTimeProcess IBMSourceLaws FractionalSpectralKernel
open IBMFiniteScenerySmoothing FractionalSpectralGeometry

theorem mollifiedScenery_continuous (n : ℕ) :
    Continuous (wholeLineScenery (kernel n)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (wholeLineScenery_hasDerivAt (kernel_compactSupport n)
    ((kernel_smooth n).of_le (by norm_num)) x).continuousAt

def randomMollifiedClass (n : ℕ) (t : ℝ≥0) (ω : SampleSpace) : GaussianL2 :=
  wholeLineScenery (kernel n) |process t ω|

def randomSourceClass (t : ℝ≥0) (ω : SampleSpace) : GaussianL2 :=
  sourceScenery |process t ω|

theorem randomMollifiedClass_stronglyMeasurable (n : ℕ) (t : ℝ≥0) :
    StronglyMeasurable (randomMollifiedClass n t) := by
  exact (mollifiedScenery_continuous n).stronglyMeasurable.comp_measurable
    (continuous_abs.measurable.comp (process_stronglyMeasurable t).measurable)

theorem randomSourceClass_stronglyMeasurable (t : ℝ≥0) :
    StronglyMeasurable (randomSourceClass t) := by
  exact sourceScenery_continuous.stronglyMeasurable.comp_measurable
    (continuous_abs.measurable.comp (process_stronglyMeasurable t).measurable)

theorem randomMollifiedClass_error_le (n : ℕ) (t : ℝ≥0) (ω : SampleSpace) :
    ‖randomMollifiedClass n t ω - randomSourceClass t ω‖ ≤
      Real.sqrt (bump n).rOut :=
  concreteMollifier_uniform_norm_le n |process t ω|

theorem sourceScenery_norm_sq (x : ℝ) : ‖sourceScenery x‖ ^ 2 = |x| := by
  have hzero : sourceScenery 0 = 0 := by
    simp [sourceScenery, direction, normalized_zero]
  simpa [hzero] using sourceScenery_increment_sq 0 x

theorem randomSourceClass_norm_sq (t : ℝ≥0) (ω : SampleSpace) :
    ‖randomSourceClass t ω‖ ^ 2 = |process t ω| := by
  simpa [randomSourceClass] using sourceScenery_norm_sq |process t ω|

theorem randomMollifiedClass_norm_sq_le (n : ℕ) (t : ℝ≥0) (ω : SampleSpace) :
    ‖randomMollifiedClass n t ω‖ ^ 2 ≤
      2 * (bump n).rOut + 2 * |process t ω| := by
  have he := concreteMollifier_error_sq_le n |process t ω|
  change ‖randomMollifiedClass n t ω - randomSourceClass t ω‖ ^ 2 ≤
    (bump n).rOut at he
  have hs := randomSourceClass_norm_sq t ω
  have ht : ‖randomMollifiedClass n t ω‖ ≤
      ‖randomMollifiedClass n t ω - randomSourceClass t ω‖ +
        ‖randomSourceClass t ω‖ := by
    conv_lhs => rw [show randomMollifiedClass n t ω =
      (randomMollifiedClass n t ω - randomSourceClass t ω) +
        randomSourceClass t ω by abel]
    exact norm_add_le _ _
  have hsq : ‖randomMollifiedClass n t ω‖ ^ 2 ≤
      (‖randomMollifiedClass n t ω - randomSourceClass t ω‖ +
        ‖randomSourceClass t ω‖) ^ 2 := by
    nlinarith [mul_nonneg
      (show 0 ≤ ‖randomMollifiedClass n t ω - randomSourceClass t ω‖ +
          ‖randomSourceClass t ω‖ - ‖randomMollifiedClass n t ω‖ by linarith)
      (show 0 ≤ ‖randomMollifiedClass n t ω - randomSourceClass t ω‖ +
          ‖randomSourceClass t ω‖ + ‖randomMollifiedClass n t ω‖ by positivity)]
  nlinarith [sq_nonneg (‖randomMollifiedClass n t ω - randomSourceClass t ω‖ -
    ‖randomSourceClass t ω‖),
    norm_nonneg (randomMollifiedClass n t ω),
    norm_nonneg (randomMollifiedClass n t ω - randomSourceClass t ω),
    norm_nonneg (randomSourceClass t ω)]

theorem randomSourceClass_memLp (t : ℝ≥0) :
    MemLp (randomSourceClass t) 2 gaussianProduct := by
  apply (memLp_two_iff_integrable_sq_norm
    (randomSourceClass_stronglyMeasurable t).aestronglyMeasurable).2
  have hi : Integrable (fun ω => |process t ω|) gaussianProduct :=
    (process_memLp t 1 (by simp)).integrable (by norm_num) |>.abs
  convert hi using 1
  funext ω
  exact randomSourceClass_norm_sq t ω

theorem randomMollifiedClass_memLp (n : ℕ) (t : ℝ≥0) :
    MemLp (randomMollifiedClass n t) 2 gaussianProduct := by
  apply (memLp_two_iff_integrable_sq_norm
    (randomMollifiedClass_stronglyMeasurable n t).aestronglyMeasurable).2
  have hi : Integrable (fun ω => |process t ω|) gaussianProduct :=
    (process_memLp t 1 (by simp)).integrable (by norm_num) |>.abs
  have hmajor : Integrable (fun ω => 2 * (bump n).rOut + 2 * |process t ω|)
      gaussianProduct := (integrable_const _).add (hi.const_mul 2)
  refine Integrable.mono' hmajor ?_ ?_
  · exact (((randomMollifiedClass_stronglyMeasurable n t).norm.measurable).pow_const 2).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖randomMollifiedClass n t ω‖))] using
        randomMollifiedClass_norm_sq_le n t ω)

def randomMollifiedL2 (n : ℕ) (t : ℝ≥0) :
    Lp GaussianL2 2 gaussianProduct :=
  (randomMollifiedClass_memLp n t).toLp (randomMollifiedClass n t)

def randomSourceL2 (t : ℝ≥0) : Lp GaussianL2 2 gaussianProduct :=
  (randomSourceClass_memLp t).toLp (randomSourceClass t)

theorem randomMollifiedL2_error_le (n : ℕ) (t : ℝ≥0) :
    ‖randomMollifiedL2 n t - randomSourceL2 t‖ ≤
      Real.sqrt (bump n).rOut := by
  have hbound : ∀ᵐ ω ∂gaussianProduct,
      ‖(randomMollifiedL2 n t - randomSourceL2 t) ω‖ ≤
        Real.sqrt (bump n).rOut := by
    filter_upwards [(randomMollifiedClass_memLp n t).coeFn_toLp,
      (randomSourceClass_memLp t).coeFn_toLp,
      Lp.coeFn_sub (randomMollifiedL2 n t) (randomSourceL2 t)] with ω hU hS hsub
    rw [hsub]
    change ‖(randomMollifiedL2 n t) ω - (randomSourceL2 t) ω‖ ≤ _
    change (randomMollifiedL2 n t) ω = randomMollifiedClass n t ω at hU
    change (randomSourceL2 t) ω = randomSourceClass t ω at hS
    rw [hU, hS]
    exact randomMollifiedClass_error_le n t ω
  have h := Lp.norm_le_of_ae_bound (Real.sqrt_nonneg _) hbound
  have hprob : measureUnivNNReal gaussianProduct = 1 := by
    simp [measureUnivNNReal]
  simpa [hprob] using h

/-- Gaussian scenery smoothing commutes with evaluation at a measurable
independent clock in the iterated `L²(clock; L²(scenery))` sense. No pointwise
sample-path modification is inferred. -/
theorem randomMollifiedL2_tendsto (t : ℝ≥0) :
    Tendsto (fun n : ℕ => randomMollifiedL2 n t) atTop
      (𝓝 (randomSourceL2 t)) := by
  have hroot : Tendsto (fun n : ℕ => Real.sqrt (bump n).rOut)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp bump_outer_tendsto_zero
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _)
    (fun n => randomMollifiedL2_error_le n t) hroot

end OperatorDerivativeRewrite.Foundation.IBMRandomTimeHilbert
