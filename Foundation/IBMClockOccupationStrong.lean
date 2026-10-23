import Foundation.IBMClockNativeSpatial
import Foundation.PositiveMollifierL2Contraction

/-! Strong L2 convergence of the ORIGINAL native directional clock kernels.
Contraction of actual positive spatial mollification upgrades the previously
verified weak limit. This is not full coefficient-vector gradient convergence. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockOccupationStrong
open InfiniteGaussian GaussianTimeHilbert IBMClockPhysicalOccupation IBMClockNativeSpatial
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem spatial_norm_sq_le (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0) :
    ∀ᵐ Y ∂gaussianProduct, ‖kernelApprox h n T Y‖ ^ 2 ≤ ‖kernel h T Y‖ ^ 2 := by
  filter_upwards [kernelApprox_convolution_ae h n T] with Y hY
  apply PositiveMollifierL2Contraction.norm_sq_le n (kernel h T Y) (kernelApprox h n T Y)
  filter_upwards [hY] with x hx
  exact hx.trans (IBMClockOccupationConvolution.kernelConvolution_integral h n T (x,Y))

theorem kernel_norm_sq_le (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0) :
    ‖kernelApprox h n T‖ ^ 2 ≤ ‖kernel h T‖ ^ 2 := by
  rw [BochnerL2Dominated.norm_sq_integral, BochnerL2Dominated.norm_sq_integral]
  exact integral_mono_ae (Lp.memLp (kernelApprox h n T)).norm.integrable_sq
    (Lp.memLp (kernel h T)).norm.integrable_sq (spatial_norm_sq_le h n T)

attribute [local irreducible] kernel kernelApprox

theorem kernel_tendsto (h : CoefficientSpace) (T : ℝ≥0) :
    Tendsto (fun n => kernelApprox h n T) atTop (𝓝 (kernel h T)) := by
  have hp := kernel_pairing_tendsto h T (kernel h T)
  have ht : Tendsto (fun n => 2 * ‖kernel h T‖ ^ 2 -
      2 * inner ℝ (kernelApprox h n T) (kernel h T)) atTop (𝓝 (0 : ℝ)) := by
    have hl := (tendsto_const_nhds (x := 2 * ‖kernel h T‖ ^ 2)).sub (hp.const_mul 2)
    have he : 2 * ‖kernel h T‖ ^ 2 - 2 * inner ℝ (kernel h T) (kernel h T) = 0 := by
      rw [real_inner_self_eq_norm_sq]
      ring
    exact he ▸ hl
  have hb (n : ℕ) : ‖kernelApprox h n T - kernel h T‖ ^ 2 ≤
      2 * ‖kernel h T‖ ^ 2 - 2 * inner ℝ (kernelApprox h n T) (kernel h T) := by
    rw [norm_sub_sq_real]
    linarith [kernel_norm_sq_le h n T]
  have hs := squeeze_zero (fun n => sq_nonneg ‖kernelApprox h n T - kernel h T‖) hb ht
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  have hn : Tendsto (fun n => ‖kernelApprox h n T - kernel h T‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hr
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

theorem kernel_norm_tendsto (h : CoefficientSpace) (T : ℝ≥0) :
    Tendsto (fun n => ‖kernelApprox h n T‖) atTop (𝓝 ‖kernel h T‖) :=
  (kernel_tendsto h T).norm

/-- Strong convergence in the original source/clock scalar L2 after contracting
the clock coefficient with a FIXED Cameron--Martin direction. -/
theorem native_directional_tendsto (h : CoefficientSpace) (T : ℝ≥0) :
    Tendsto (fun n => directional h (IBMClockAverageGraph.averageGradient n T)) atTop
      (𝓝 (directional h (gradient T))) := by
  have ht := noiseLift.continuous.continuousAt.tendsto.comp (kernel_tendsto h T)
  simpa only [Function.comp_def, kernelApprox_realization, kernel_realization] using ht

theorem native_directional_norm_tendsto (h : CoefficientSpace) (T : ℝ≥0) :
    Tendsto (fun n => ‖directional h (IBMClockAverageGraph.averageGradient n T)‖) atTop
      (𝓝 ‖directional h (gradient T)‖) := (native_directional_tendsto h T).norm

end OperatorDerivativeRewrite.Foundation.IBMClockOccupationStrong
