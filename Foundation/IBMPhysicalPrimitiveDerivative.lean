import Foundation.IBMPhysicalPointKernelIto
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! The actual spatial Brownian indicator primitive is C1 in physical H^-1.
Its derivative is the genuine translated Dirac, proved by uniform convergence
of actual mollified derivatives, not by differentiating an L2 indicator. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalPrimitiveDerivative
open InfiniteGaussian IBMPhysicalWeakWiener IBMPhysicalNegativeEmbedding
open IBMPhysicalNoiseClock IBMPhysicalNoiseCalculus IBMPhysicalNoiseVectors
open IBMPhysicalDirac IBMPhysicalDerivativeKernel IBMContinuousScenery
local instance : NormedSpace ℝ Kernel := NormedSpace.restrictScalars ℝ ℂ _

def primitive (r : ℝ) : Kernel := embedding (vector r)

def native (n : ℕ) (r : ℝ) : Kernel :=
  embedding (convolutionKernel (IBMMollifier.kernel n) r)

theorem native_hasDerivAt (n : ℕ) (r : ℝ) :
    HasDerivAt (native n) (translated n r) r := by
  have h := (embedding.comp kernelPullback).hasFDerivAt.comp_hasDerivAt r
    (wholeLineScenery_hasDerivAt (IBMMollifier.kernel_compactSupport n)
      ((IBMMollifier.kernel_smooth n).of_le (by norm_num)) r)
  change HasDerivAt (fun s => (embedding.comp kernelPullback)
    (wholeLineScenery (IBMMollifier.kernel n) s))
    ((embedding.comp kernelPullback) (wholeLineScenery (deriv (IBMMollifier.kernel n)) r)) r at h
  have he : (fun s => (embedding.comp kernelPullback)
      (wholeLineScenery (IBMMollifier.kernel n) s)) = native n := by
    funext s
    rw [ContinuousLinearMap.comp_apply,
      kernelPullback_convolution (IBMMollifier.kernel_smooth n).continuous
        (IBMMollifier.kernel_compactSupport n)]
    rfl
  rw [he] at h
  simp only [ContinuousLinearMap.comp_apply,
    kernelPullback_convolution ((IBMMollifier.kernel_smooth n).continuous_deriv (by norm_num))
      (IBMMollifier.kernel_compactSupport n).deriv,
    derivative_eq_translated ((IBMMollifier.kernel_smooth n).of_le (by norm_num))
      (IBMMollifier.kernel_compactSupport n)] at h
  exact h

theorem translated_uniform : TendstoUniformly translated dirac atTop := by
  have hroot : Tendsto (fun n => Real.sqrt (IBMMollifier.bump n).rOut) atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp IBMMollifier.bump_outer_tendsto_zero
  have hzero : Tendsto (fun n => ‖physicalDerivative‖ * Real.sqrt (IBMMollifier.bump n).rOut)
      atTop (nhds 0) := by simpa only [mul_zero] using hroot.const_mul ‖physicalDerivative‖
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [hzero.eventually (eventually_lt_nhds hε)] with n hn r
  rw [dist_comm, dist_eq_norm]
  exact (IBMPhysicalRunningPrimitive.translated_error n r).trans_lt hn

theorem native_tendsto (r : ℝ) :
    Tendsto (fun n => native n r) atTop (nhds (primitive r)) := by
  simpa only [native, primitive, Function.comp_def] using
    embedding.continuous.tendsto _ |>.comp (mollifier_kernel_tendsto r)

theorem primitive_hasDerivAt (r : ℝ) : HasDerivAt primitive (dirac r) r :=
  hasDerivAt_of_tendstoUniformly translated_uniform
    (Eventually.of_forall fun n r => native_hasDerivAt n r) native_tendsto r

theorem primitive_deriv : deriv primitive = dirac :=
  funext fun r => (primitive_hasDerivAt r).deriv

theorem primitive_C1 : ContDiff ℝ 1 primitive := contDiff_one_iff_deriv.mpr
  ⟨fun r => (primitive_hasDerivAt r).differentiableAt, by
    rw [primitive_deriv]
    exact dirac_continuous⟩

theorem primitive_zero : primitive 0 = 0 := by simp only [primitive, vector_zero, map_zero]

theorem scalar_hasDerivAt (L : Tests) (r : ℝ) :
    HasDerivAt (fun s => L (primitive s)) (L (dirac r)) r :=
  L.hasFDerivAt.comp_hasDerivAt r (primitive_hasDerivAt r)

theorem scalar_C1 (L : Tests) : ContDiff ℝ 1 (fun s => L (primitive s)) :=
  L.contDiff.comp primitive_C1

/-- A physical norm estimate for the genuine first-order Taylor remainder.
The explicit square-root modulus is the input needed for clock path estimates. -/
theorem taylor_remainder_bound {r s : ℝ} (hrs : r ≤ s) :
    ‖primitive s - primitive r - (s-r) • dirac r‖ ≤
      (‖physicalDerivative‖ * Real.sqrt (s-r)) * (s-r) := by
  have hd (x : ℝ) : HasDerivAt (fun y => primitive y - (y-r) • dirac r)
      (dirac x - dirac r) x := by
    have h := (primitive_hasDerivAt x).sub
      (((hasDerivAt_id x).sub_const r).smul_const (dirac r))
    change HasDerivAt (fun y => primitive y - (y-r) • dirac r)
      (dirac x - (1 : ℝ) • dirac r) x at h
    convert h using 1
    module
  have hb (x : ℝ) (hx : x ∈ Set.Ico r s) :
      ‖dirac x - dirac r‖ ≤ ‖physicalDerivative‖ * Real.sqrt (s-r) := by
    apply (dirac_difference_bound x r).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.sqrt_le_sqrt
    rw [abs_of_nonpos (by linarith [hx.1])]
    linarith [hx.2]
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun x (_hx : x ∈ Set.Icc r s) => (hd x).hasDerivWithinAt) hb s
      (Set.right_mem_Icc.mpr hrs)
  have he : (primitive s - (s-r) • dirac r) -
      (primitive r - (r-r) • dirac r) = primitive s - primitive r - (s-r) • dirac r := by
    module
  rw [he] at h
  exact h

theorem dirac_interval_integral (r s : ℝ) :
    ∫ x in r..s, dirac x = primitive s - primitive r :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _hx => primitive_hasDerivAt x) (dirac_continuous.intervalIntegrable r s)

theorem origin_remainder_bound {s : ℝ} (hs : 0 ≤ s) :
    ‖primitive s - s • dirac 0‖ ≤ (‖physicalDerivative‖ * Real.sqrt s) * s := by
  simpa only [primitive_zero, sub_zero] using taylor_remainder_bound hs

end OperatorDerivativeRewrite.Foundation.IBMPhysicalPrimitiveDerivative
