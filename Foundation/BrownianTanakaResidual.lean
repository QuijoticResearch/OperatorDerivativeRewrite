import Foundation.BrownianTanakaApproximation
import Foundation.GaussianC2TimeWeighted
import Foundation.BrownianSignConditional
import Mathlib.MeasureTheory.Function.LpOrder

/-! A positive fixed-time Tanaka residual obtained as an actual L2 limit
of the smooth Ito curvature drifts. This is not yet a local-time path. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianTanakaResidual
open InfiniteGaussian GaussianTimeProcess GaussianPredictableFull GaussianLipschitzIntegrands
open SmoothAbsoluteApproximation BrownianTanakaApproximation RealSteklovApprox

local instance : IsOrderedModule ℝ GaussianL2 := IsOrderedModule.of_smul_nonneg (by
  intro a ha F hF
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [Lp.coeFn_smul a F, (Lp.coeFn_nonneg F).mpr hF] with ω hs hf
  simp only [hs, Pi.smul_apply, smul_eq_mul]
  exact mul_nonneg ha hf)

def curvatureConstant {e : ℝ} (he : 0 < e) : ℝ≥0 := ⟨e⁻¹, inv_nonneg.mpr he.le⟩

theorem first_bound {e : ℝ} (he : 0 < e) (x : ℝ) : ‖deriv (radius e) x‖₊ ≤ 1 := by
  rw [radius_deriv he]
  exact slope_bound he x

theorem second_bound {e : ℝ} (he : 0 < e) (x : ℝ) :
    ‖deriv (deriv (radius e)) x‖₊ ≤ curvatureConstant he := by
  rw [radius_second_deriv he]
  exact curvature_bound he x

def curvatureValue {e : ℝ} (he : 0 < e) (t : ℝ≥0) : GaussianL2 :=
  GaussianC2Ito.curvatureValue (radius e) (radius_smooth he 2)
    (curvatureConstant he) (second_bound he) t

theorem curvatureValue_nonneg {e : ℝ} (he : 0 < e) (t : ℝ≥0) :
    0 ≤ curvatureValue he t := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [GaussianC2Ito.curvatureValue_coeFn (radius e) (radius_smooth he 2)
    (curvatureConstant he) (second_bound he) t] with ω hv
  change curvatureValue he t ω = _ at hv
  rw [hv, radius_second_deriv he]
  exact curvature_nonneg he _

def approximateMass (n : ℕ) (T : ℝ≥0) : GaussianL2 :=
  (1 / 2 : ℝ) • ∫ t in 0..(T : ℝ), curvatureValue (width_pos n) t.toNNReal

theorem approximateMass_nonneg (n : ℕ) (T : ℝ≥0) : 0 ≤ approximateMass n T := by
  apply smul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [intervalIntegral.integral_of_le T.coe_nonneg]
  exact integral_nonneg (fun t => curvatureValue_nonneg (width_pos n) t.toNNReal)

theorem approximateMass_identity (n : ℕ) (T : ℝ≥0) :
    approximateMass n T = valueL2 (functionLip (width_pos n)) T -
      width n • gaussianOne - itoIntegral (approximateField n T) := by
  have h := GaussianC2Ito.c2_ito (radius (width n)) (radius_smooth (width_pos n) 2)
    1 (curvatureConstant (width_pos n)) (first_bound (width_pos n))
      (second_bound (width_pos n)) T
  have hd : integrand (GaussianC2Ito.derivativeLip (radius (width n))
      (radius_smooth (width_pos n) 2) (curvatureConstant (width_pos n))
      (second_bound (width_pos n))) T = approximateField n T := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [integrand_joint (GaussianC2Ito.derivativeLip (radius (width n))
      (radius_smooth (width_pos n) 2) (curvatureConstant (width_pos n))
      (second_bound (width_pos n))) T,
      integrand_joint (slopeLip (width_pos n)) T] with z ha hb
    change (approximateField n T : GaussianTimeProductL2.TimeProbabilityL2) z = _ at hb
    rw [ha, hb, radius_deriv (width_pos n)]
  rw [GaussianSmoothIto.valueL2_zero, hd] at h
  have hz : radius (width n) 0 = width n := by
    simp [radius, Real.sqrt_sq (width_pos n).le]
  rw [hz] at h
  change valueL2 (functionLip (width_pos n)) T - width n • gaussianOne =
    itoIntegral (approximateField n T) + approximateMass n T at h
  linear_combination (norm := module) -h

def mass (T : ℝ≥0) : GaussianL2 := absoluteValue T - BrownianSignIntegral.terminal T

theorem approximateMass_tendsto (T : ℝ≥0) :
    Tendsto (fun n => approximateMass n T) atTop (𝓝 (mass T)) := by
  have hz := (width_tendsto.mono_right nhdsWithin_le_nhds).smul_const gaussianOne
  simp only [zero_smul] at hz
  have h := ((BrownianTanakaApproximation.terminal_tendsto T).sub hz).sub (integral_tendsto T)
  simpa only [sub_zero, ← approximateMass_identity, mass] using h

theorem mass_nonneg (T : ℝ≥0) : 0 ≤ mass T :=
  ge_of_tendsto' (approximateMass_tendsto T) (fun n => approximateMass_nonneg n T)

theorem mass_ae_nonneg (T : ℝ≥0) : ∀ᵐ ω ∂gaussianProduct, 0 ≤ mass T ω :=
  (Lp.coeFn_nonneg _).mpr (mass_nonneg T)

theorem approximateMass_monotone (n : ℕ) : Monotone (approximateMass n) := by
  intro S T hST
  have hc := (GaussianC2TimeWeighted.curvature_continuous (radius (width n))
    (radius_smooth (width_pos n) 2) (curvatureConstant (width_pos n))
      (second_bound (width_pos n))).comp continuous_real_toNNReal
  change Continuous (fun t : ℝ => curvatureValue (width_pos n) t.toNNReal) at hc
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := (volume : Measure ℝ))
    (hc.intervalIntegrable 0 (S : ℝ)) (hc.intervalIntegrable (S : ℝ) (T : ℝ))
  have hp : 0 ≤ ∫ t in (S : ℝ)..(T : ℝ), curvatureValue (width_pos n) t.toNNReal := by
    rw [intervalIntegral.integral_of_le (show (S : ℝ) ≤ T from hST)]
    exact integral_nonneg (fun t => curvatureValue_nonneg (width_pos n) t.toNNReal)
  unfold approximateMass
  apply smul_le_smul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [← hi]
  exact le_add_of_nonneg_right hp

theorem mass_monotone : Monotone mass := by
  intro S T hST
  exact le_of_tendsto_of_tendsto' (approximateMass_tendsto S) (approximateMass_tendsto T)
    (fun n => approximateMass_monotone n hST)

theorem mass_zero : mass 0 = 0 := by
  have hn : BrownianSignIntegral.terminal 0 = 0 := by
    have h := BrownianSignIntegral.terminal_norm_sq 0
    norm_num at h
    exact h
  simp [mass, absoluteValue, GaussianSmoothIto.valueL2_zero, hn]

theorem signIntegral_continuous : Continuous BrownianSignIntegral.terminal := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hc : Continuous (fun s : ℝ≥0 =>
      ‖BrownianSignIntegral.terminal s - BrownianSignIntegral.terminal t‖ ^ 2) := by
    simp_rw [norm_sub_sq_real, BrownianSignIntegral.terminal_norm_sq,
      BrownianSignConditional.terminal_inner]
    fun_prop
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp (hc.continuousAt (x := t)).tendsto
  simp only [Function.comp_def, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] at h
  exact tendsto_iff_norm_sub_tendsto_zero.mpr h

theorem mass_continuous : Continuous mass :=
  (valueL2_continuous absLip).sub signIntegral_continuous

theorem tanaka_identity (T : ℝ≥0) :
    absoluteValue T = BrownianSignIntegral.terminal T + mass T := by
  unfold mass
  abel

end OperatorDerivativeRewrite.Foundation.BrownianTanakaResidual
