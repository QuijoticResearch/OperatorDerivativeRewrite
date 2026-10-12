import Foundation.GaussianAmbientRepresentationObstruction
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The actual norm of the projected derivative of Brownian coordinates, and
the resulting integrated energy. This is not a quadratic-variation theorem. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianBrownianBracket
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProductL2 GaussianPredictableFull
open GaussianPredictableAdjoint GaussianTimeProcess
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe

theorem gaussianOne_past (s : ℝ≥0) :
    AEStronglyMeasurable[naturalFiltration s] gaussianOne gaussianProduct :=
  aestronglyMeasurable_const.congr gaussianOne_coeFn.symm

def deterministicInterval (t : ℝ≥0) : fullPredictable :=
  ⟨productTensor (timeVector t) gaussianOne,
    past_step_mem_fullPredictable 0 t gaussianOne (gaussianOne_past 0)⟩

theorem integral_deterministicInterval (t : ℝ≥0) :
    itoIntegral (deterministicInterval t) = wienerL2 t := by
  apply Lp.ext
  filter_upwards [itoIntegral_past_step 0 t (by positivity) gaussianOne (gaussianOne_past 0),
    gaussianOne_coeFn, process_zero_ae] with ω hi h1 h0
  change itoIntegral (deterministicInterval t) ω = _ at hi
  rw [hi, h1, h0, sub_zero, one_mul]
  rfl

/-- The projected derivative is the WHOLE interval indicator, not the scalar constant one. -/
theorem predictableAdjoint_wiener (t : ℝ≥0) :
    predictableAdjoint (wienerL2 t) = deterministicInterval t := by
  rw [← integral_deterministicInterval, predictableAdjoint_integral]

theorem predictableAdjoint_wiener_norm_sq (t : ℝ≥0) :
    ‖predictableAdjoint (wienerL2 t)‖ ^ 2 = (t : ℝ) := by
  rw [predictableAdjoint_wiener, ← itoIntegral.norm_map,
    integral_deterministicInterval]
  simpa only [wienerL2_zero, sub_zero, NNReal.coe_zero] using
    wienerL2_sub_norm_sq 0 t (by positivity)

/-- The manuscript's integral of whole derivative-Hilbert norms equals T^2/2 in this model. -/
theorem integrated_projected_energy (T : ℝ≥0) :
    (∫ s in (0 : ℝ)..(T : ℝ), ‖predictableAdjoint (wienerL2 s.toNNReal)‖ ^ 2) =
      (T : ℝ) ^ 2 / 2 := by
  have he : (∫ s in (0 : ℝ)..(T : ℝ),
      ‖predictableAdjoint (wienerL2 s.toNNReal)‖ ^ 2) = ∫ s in (0 : ℝ)..(T : ℝ), s := by
    apply intervalIntegral.integral_congr
    intro s hs
    change ‖predictableAdjoint (wienerL2 s.toNNReal)‖ ^ 2 = s
    rw [uIcc_of_le T.coe_nonneg] at hs
    rw [predictableAdjoint_wiener_norm_sq, Real.coe_toNNReal _ hs.1]
  rw [he, integral_id]
  ring

/-- At unit time the whole-norm integrated energy is 1/2, not the Brownian variance 1. -/
theorem integrated_projected_energy_one_ne_variance :
    (∫ s in (0 : ℝ)..1, ‖predictableAdjoint (wienerL2 s.toNNReal)‖ ^ 2) ≠
      ‖wienerL2 1‖ ^ 2 := by
  have he := integrated_projected_energy 1
  have hv := wienerL2_sub_norm_sq 0 1 (by norm_num)
  simp only [wienerL2_zero, sub_zero, NNReal.coe_zero, NNReal.coe_one] at he hv
  simp only [one_pow] at he hv
  rw [he, hv]
  norm_num

end OperatorDerivativeRewrite.Foundation.GaussianBrownianBracket
