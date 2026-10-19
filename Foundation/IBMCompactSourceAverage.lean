import Foundation.IBMDilatedClockMassLimit
import Foundation.IBMCompactKernelSchwartz

/-! Literal scenery averages for arbitrary compact kernels and their uniform
shrinking-layer estimate, on the original Gaussian source space. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMCompactSourceAverage
open InfiniteGaussian IBMContinuousScenery GaussianLipschitzIntegrands GaussianDeterministicGraphCore
open IBMCompactVarianceGeometry IBMDilatedVarianceGeometry
set_option backward.isDefEq.respectTransparency false
variable {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ)

def centeredClass (ρ : ℝ → ℝ) (r : ℝ) : GaussianL2 :=
  (centered_lipschitz hφ).compLp (sub_self _) (wholeLineScenery ρ r)

def sourceAverage (ρ : ℝ → ℝ) (r : ℝ) : ℝ := φ 0+inner ℝ gaussianOne (centeredClass hφ ρ r)

theorem centeredClass_ae (ρ : ℝ → ℝ) (r : ℝ) :
    centeredClass hφ ρ r =ᵐ[gaussianProduct] fun ω => φ (wholeLineScenery ρ r ω)-φ 0 :=
  (centered_lipschitz hφ).coeFn_compLp (sub_self _) _

theorem sourceAverage_eq_integral (ρ : ℝ → ℝ) (r : ℝ) :
    sourceAverage hφ ρ r = ∫ ω, φ (wholeLineScenery ρ r ω) ∂gaussianProduct := by
  have hu := (composition_memLp hφ (wholeLineScenery ρ r)).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  rw [sourceAverage,gaussianOne_inner_eq_integral,integral_congr_ae (centeredClass_ae hφ ρ r),
    integral_sub hu (integrable_const (φ 0)),integral_const]
  simp

theorem sourceAverage_continuous {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ) :
    Continuous (sourceAverage hφ ρ) := by
  have hU : Continuous (wholeLineScenery ρ) := continuous_iff_continuousAt.mpr fun r =>
    (wholeLineScenery_hasDerivAt hc hρ r).continuousAt
  have hcen : Continuous (centeredClass hφ ρ) :=
    ((centered_lipschitz hφ).continuous_compLp (sub_self _)).comp hU
  exact continuous_const.add ((innerSL ℝ gaussianOne).continuous.comp hcen)

theorem sourceAverage_error (ρ : ℝ → ℝ) (r : ℝ) :
    ‖sourceAverage hφ ρ r-φ 0‖ ≤ (K : ℝ)*‖wholeLineScenery ρ r‖ := by
  have hn : ‖gaussianOne‖ = 1 := by
    have h := gaussianOne_inner_self
    rw [real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg gaussianOne]
  have h := norm_inner_le_norm (𝕜 := ℝ) gaussianOne (centeredClass hφ ρ r)
  simp only [sourceAverage,add_sub_cancel_left,hn,one_mul] at *
  exact h.trans ((centered_lipschitz hφ).norm_compLp_le (sub_self _) _)

theorem sourceAverage_bound {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) (ρ : ℝ → ℝ) (r : ℝ) :
    ‖sourceAverage hφ ρ r‖ ≤ M := by
  rw [sourceAverage_eq_integral]
  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
    (μ := gaussianProduct) (Filter.Eventually.of_forall fun ω => hM _)

theorem variance_zero_le {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    (hpos : ∀ z, 0 ≤ ρ z) (hmass : (∫ z, ρ z) = 1) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ z, ρ z ≠ 0 → |z| ≤ R) : wholeLineVariance ρ 0 ≤ R := by
  have hz : sourceScenery 0 = 0 := by
    apply norm_eq_zero.mp
    have hh := IBMRandomTimeHilbert.sourceScenery_norm_sq 0
    simp only [abs_zero] at hh
    nlinarith [norm_nonneg (sourceScenery 0)]
  have he : IBMDilatedMollifier.dilate ρ 1 = ρ := by
    funext x
    simp [IBMDilatedMollifier.dilate]
  have h := IBMDilatedMollifier.scenery_error hρ hpos hmass hR hs (by norm_num : (0 : ℝ) < 1) 0
  simpa only [he,hz,sub_zero,one_mul,wholeLineVariance] using h

theorem sourceAverage_layer_error {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ)
    (hpos : ∀ z, 0 ≤ ρ z) (hmass : (∫ z, ρ z) = 1) {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ z, ρ z ≠ 0 → |z| ≤ R) (r : ℝ) (hr : |r| ≤ R) :
    ‖sourceAverage hφ ρ r-φ 0‖ ≤ (K : ℝ)*Real.sqrt (2*R) := by
  have hd := (variance_lipschitz hc hρ hpos hmass).dist_le_mul r 0
  simp only [Real.dist_eq,sub_zero,NNReal.coe_one,one_mul] at hd
  have hv := variance_zero_le hρ.continuous hpos hmass hR hs
  have hu : ‖wholeLineScenery ρ r‖ ≤ Real.sqrt (2*R) := by
    have he : wholeLineVariance ρ r = ‖wholeLineScenery ρ r‖^2 := rfl
    nlinarith [he,Real.sq_sqrt (by positivity : 0 ≤ 2*R),Real.sqrt_nonneg (2*R),
      norm_nonneg (wholeLineScenery ρ r),le_abs_self (wholeLineVariance ρ r-wholeLineVariance ρ 0)]
  exact (sourceAverage_error hφ ρ r).trans (mul_le_mul_of_nonneg_left hu K.coe_nonneg)

end OperatorDerivativeRewrite.Foundation.IBMCompactSourceAverage
