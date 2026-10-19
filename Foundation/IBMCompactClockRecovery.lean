import Foundation.IBMCompactClockGraph
import Foundation.IBMDilatedEndpointLimit
import Foundation.IBMClockRegularizedSlope

/-! Canonical full-source regularized slopes for arbitrary compact kernels,
with a width-independent integrable time-zero energy bound. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMCompactClockRecovery
open InfiniteGaussian GaussianClockValueOperators GaussianDirectionalRecovery
open IBMCompactClockGraph IBMCompactKernelReflectedIto IBMNormalizedClockProfiles
set_option backward.isDefEq.respectTransparency false
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def recoveredSlope (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0) : Field :=
  (Real.sqrt (T : ℝ))⁻¹ • clockLift (directionalRecovery (unitDirection T))
    (endpointClass g a hc hρ T)

/-- The exact shifted channels of the ACTUAL signed slope, obtained from
the original closed clock derivative rather than a prescribed series. -/
theorem recoveredSlope_projection (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) {T : ℝ≥0} (hT : 0 < T) (k : ℕ) :
    clockLift (GaussianNumberSectors.projection k) (recoveredSlope g a hc hρ T) =
      (k+1 : ℝ)⁻¹ • clockLift (GaussianNumberSectors.projection k) (pointSlope g a hc hρ T) := by
  have hz : Real.sqrt (T : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (show 0 < (T : ℝ) from hT))
  apply eq_of_all_tests
  intro L
  change L.compLpL 2 gaussianProduct
    (clockLift (GaussianNumberSectors.projection k) ((Real.sqrt (T : ℝ))⁻¹ •
      clockLift (directionalRecovery (unitDirection T)) (endpointClass g a hc hρ T))) = _
  rw [map_smul,map_smul,clockLift_test,clockLift_test]
  rw [shifted_derivative_projection _ (unitDirection_norm hT) (tested_closed_graph g a hc hρ hT L) k]
  rw [map_smul,map_smul]
  rw [map_smul,clockLift_test]
  simp only [smul_smul]
  congr 1
  field_simp

theorem recoveredSlope_chaos_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) {T : ℝ≥0} (hT : 0 < T) :
    Tendsto (fun N => ∑ k ∈ Finset.range (N+1), (k+1 : ℝ)⁻¹ •
      clockLift (GaussianNumberSectors.projection k) (pointSlope g a hc hρ T)) atTop
      (𝓝 (recoveredSlope g a hc hρ T)) := by
  have hh := clock_truncation_tendsto (recoveredSlope g a hc hρ T)
  simpa only [clock_truncation_eq,recoveredSlope_projection g a hc hρ hT] using hh

theorem recoveredSlope_unique (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) {T : ℝ≥0} (hT : 0 < T) {q : Field}
    (hq : ∀ k, clockLift (GaussianNumberSectors.projection k) q =
      (k+1 : ℝ)⁻¹ • clockLift (GaussianNumberSectors.projection k) (pointSlope g a hc hρ T)) :
    q = recoveredSlope g a hc hρ T := by
  apply eq_of_clock_projections
  intro k
  rw [hq k,recoveredSlope_projection g a hc hρ hT k]

theorem recoveredSlope_uniform_energy (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ)
    (hpos : ∀ x, 0 ≤ ρ x) (hmass : (∫ x, ρ x) = 1) {T : ℝ≥0} (hT : 0 < T) :
    ‖recoveredSlope g a hc hρ T‖^2 ≤ slopeBound g^2*absoluteMoment/Real.sqrt (T : ℝ) := by
  have hp : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.mpr (show 0 < (T : ℝ) from hT)
  have hn : ‖clockLift (directionalRecovery (unitDirection T)) (endpointClass g a hc hρ T)‖ ≤
      ‖endpointClass g a hc hρ T‖ := by
    simpa only [unitDirection_norm hT,one_mul] using
      clockRecovery_norm_le (unitDirection T) (endpointClass g a hc hρ T)
  have hb := (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
    (endpoint_uniform_energy g a hc hρ hpos hmass hT)
  rw [recoveredSlope,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hp.le),mul_pow]
  apply (mul_le_mul_of_nonneg_left hb (sq_nonneg _)).trans_eq
  field_simp

/-- At every fixed time the limit is the SAME previously constructed unmollified
recovery, independent of the positive normalized profile. -/
theorem recoveredSlope_continuum_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ)
    (hpos : ∀ x, 0 ≤ ρ x) (hmass : (∫ x, ρ x) = 1) (T : ℝ≥0) :
    Tendsto (fun ε : {x : ℝ // 0 < x} => recoveredSlope g a
      (IBMDilatedMollifier.dilate_compact hc ε.property.ne')
      (IBMDilatedMollifier.dilate_contDiff hρ ε.val) T)
      (comap (fun ε : {x : ℝ // 0 < x} => ε.val) (𝓝 0))
      (𝓝 (IBMClockRegularizedSlope.recoveredSlopeLimit g a T)) :=
  tendsto_const_nhds.smul
    ((clockLift (directionalRecovery (unitDirection T))).continuous.tendsto _ |>.comp
      (IBMDilatedEndpointLimit.endpoint_continuum_tendsto g a hc hρ hpos hmass T))

end OperatorDerivativeRewrite.Foundation.IBMCompactClockRecovery
