import Foundation.IBMDilatedPredictableLimit
import Foundation.IBMCrossSectorDualClosure

/-! Genuine full cross-sector dual closure for the actual continuum family,
with uniform rectangular chaos tails and bounded-test convergence. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMDilatedDualClosure
open InfiniteGaussian GaussianClockValueOperators GaussianClockSourceSpectral IBMCommonClockDual
open IBMDilatedPredictableLimit IBMRegularizedStochasticIdentity
set_option backward.isDefEq.respectTransparency false
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def rawCorrectionAt (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) (T : ℝ≥0) (ε : {x : ℝ // 0 < x}) : Field :=
  IBMCompactKernelReflectedIto.wholeClass g a (IBMDilatedMollifier.dilate_compact hc ε.property.ne')
    (IBMDilatedMollifier.dilate_contDiff hρ ε.val) T

theorem uniform_joint_tail {ι : Type*} {l : Filter ι} {f : ι → Field} {c : Field}
    (hc : Tendsto f l (𝓝 c)) {η : ℝ} (hη : 0 < η) :
    ∃ M0 N0 : ℕ, ∀ᶠ i in l, ∀ M ≥ M0, ∀ N ≥ N0,
      ‖f i-jointTruncation M N (f i)‖ < η := by
  have hn := Metric.tendsto_nhds.mp hc (η/4) (by positivity)
  obtain ⟨M0,hM⟩ := Metric.tendsto_atTop.mp (sourceTruncation_tendsto c) (η/4) (by positivity)
  obtain ⟨N0,hN⟩ := Metric.tendsto_atTop.mp (clock_truncation_tendsto c) (η/4) (by positivity)
  refine ⟨M0,N0,hn.mono fun i hi M hMM N hNN => ?_⟩
  have h1 : ‖f i-c‖ < η/4 := by simpa only [dist_eq_norm] using hi
  have h2 : ‖c-sourceTruncation M c‖ < η/4 := by
    simpa only [dist_eq_norm,norm_sub_rev] using hM M hMM
  have h3 : ‖c-clockLift (GaussianNumberSectors.truncation N) c‖ < η/4 := by
    simpa only [dist_eq_norm,norm_sub_rev] using hN N hNN
  have hb := joint_tail_compare M N (f i) c
  linarith

/-- Uniform over ALL sufficiently small positive widths and independently
large source/clock cutoffs, for the original full correction. -/
theorem correction_uniform_rectangular_tail (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ)
    (hpos : ∀ x, 0 ≤ ρ x) (hmass : (∫ x, ρ x) = 1) (T : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    ∃ M0 N0 : ℕ, ∀ᶠ ε : {x : ℝ // 0 < x} in comap (fun ε => ε.val) (𝓝 0),
      ∀ M ≥ M0, ∀ N ≥ N0, dualNorm (rawCorrectionAt g a hc hρ T ε-
        ∑ m ∈ Finset.range (M+1), ∑ k ∈ Finset.range (N+1),
          block m k (rawCorrectionAt g a hc hρ T ε)) < η := by
  obtain ⟨M0,N0,ht⟩ := uniform_joint_tail (correction_continuum_tendsto g a hc hρ hpos hmass T) hη
  refine ⟨M0,N0,ht.mono fun ε hε M hM N hN => ?_⟩
  rw [← jointTruncation_eq_sum]
  change ‖smoothing (rawCorrectionAt g a hc hρ T ε-
    jointTruncation M N (rawCorrectionAt g a hc hρ T ε))‖ < η
  rw [map_sub]
  rw [show smoothing (jointTruncation M N (rawCorrectionAt g a hc hρ T ε)) =
    jointTruncation M N (smoothing (rawCorrectionAt g a hc hρ T ε)) from commonSmoothing_joint M N _]
  exact hε M hM N hN

/-- Uniform convergence on the whole unit ball of the dense regular test space,
using its verified pulled-back norm, not the ambient L2 norm of K psi. -/
theorem correction_dual_uniform (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ)
    (hpos : ∀ x, 0 ≤ ρ x) (hmass : (∫ x, ρ x) = 1) (T : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ ε : {x : ℝ // 0 < x} in comap (fun ε => ε.val) (𝓝 0),
      ∀ ψ : Field, ‖ψ‖ ≤ 1 →
        |inner ℝ (rawCorrectionAt g a hc hρ T ε) (smoothing ψ)-
          inner ℝ (correctionLimit g a T) ψ| < η := by
  have hn := Metric.tendsto_nhds.mp (correction_continuum_tendsto g a hc hρ hpos hmass T) η hη
  apply hn.mono
  intro ε hε ψ hψ
  have he : inner ℝ (rawCorrectionAt g a hc hρ T ε) (smoothing ψ)-
      inner ℝ (correctionLimit g a T) ψ =
      inner ℝ (correctionAt g a hc hρ T ε-correctionLimit g a T) ψ := by
    rw [← smoothing_pairing,inner_sub_left]
    rfl
  rw [he]
  have hb : |inner ℝ (correctionAt g a hc hρ T ε-correctionLimit g a T) ψ| ≤
      ‖correctionAt g a hc hρ T ε-correctionLimit g a T‖ := by
    have hh := norm_inner_le_norm (𝕜 := ℝ) (correctionAt g a hc hρ T ε-correctionLimit g a T) ψ
    rw [Real.norm_eq_abs] at hh
    exact hh.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hψ (norm_nonneg _))
  exact hb.trans_lt (by simpa only [dist_eq_norm] using hε)

theorem raw_clock_projection_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ)
    (hpos : ∀ x, 0 ≤ ρ x) (hmass : (∫ x, ρ x) = 1) (T : ℝ≥0) (k : ℕ) :
    Tendsto (fun ε => clockLift (GaussianNumberSectors.projection k) (rawCorrectionAt g a hc hρ T ε))
      (comap (fun ε : {x : ℝ // 0 < x} => ε.val) (𝓝 0))
      (𝓝 ((GaussianRegularizedSecondDerivative.weight k)⁻¹ •
        clockLift (GaussianNumberSectors.projection k) (correctionLimit g a T))) := by
  have hh := (((clockLift (GaussianNumberSectors.projection k)).continuous.tendsto _).comp
    (correction_continuum_tendsto g a hc hρ hpos hmass T)).const_smul
      (GaussianRegularizedSecondDerivative.weight k)⁻¹
  simpa only [Function.comp_def,correctionAt,IBMCompactPredictableSlices.correction,rawCorrectionAt,
    IBMCrossSectorDualClosure.smoothed_clock_projection,smul_smul,
    inv_mul_cancel₀ (ne_of_gt (GaussianRegularizedSecondDerivative.weight_pos k)),one_smul] using hh

theorem raw_block_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ)
    (hpos : ∀ x, 0 ≤ ρ x) (hmass : (∫ x, ρ x) = 1) (T : ℝ≥0) (m k : ℕ) :
    Tendsto (fun ε => block m k (rawCorrectionAt g a hc hρ T ε))
      (comap (fun ε : {x : ℝ // 0 < x} => ε.val) (𝓝 0))
      (𝓝 ((GaussianRegularizedSecondDerivative.weight k)⁻¹ • block m k (correctionLimit g a T))) := by
  have hh := (sourceLift (GaussianNumberSectors.projection m)).continuous.tendsto _ |>.comp
    (raw_clock_projection_tendsto g a hc hρ hpos hmass T k)
  simpa only [Function.comp_def,block,ContinuousLinearMap.comp_apply,map_smul] using hh

end OperatorDerivativeRewrite.Foundation.IBMDilatedDualClosure
