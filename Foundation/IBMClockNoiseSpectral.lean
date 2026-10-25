import Foundation.GaussianObservationCorrelation
import Foundation.IBMClockNoiseRegularity

/-! Full actual reflected-clock IBM noise energy in the ORIGINAL clock-number
sectors, and vanishing of every odd clock sector with all source randomness
retained. The noise coupling is the already constructed future-clock probe;
this does not identify an adapted physical driver or a fractional domain. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockNoiseSpectral
open GaussianObservationCorrelation
open InfiniteGaussian IBMClockLinearDivergence IBMPointClockDomainObstruction
open IBMClockNoiseRegularity GaussianClockValueOperators

theorem actual_clock_noise_series (T : ℝ≥0) (hT : 0 < T) (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    HasSum (fun n => 2*(1-(1-h)^n)*
      ‖clockLift (GaussianNumberSectors.projection n) (IBMRandomTimeHilbert.randomSourceL2 T)‖^2)
      (‖timeDirection T‖ * GaussianAbsoluteMoments.standardMoment 1 * rate h) := by
  let u := unitClock T
  let hu := unitClock_norm T hT
  let v := rotation u (futureClock T) (1-h)
  let hv := rotation_norm u (futureClock T) hu (futureClock_norm T) (futureClock_orthogonal T)
    (1-h) (abs_le.mpr ⟨by linarith,by linarith⟩)
  have hs := clock_sector_noise_hasSum u v hu hv
    (IBMClockWeakGraphObstruction.sectionClass ‖timeDirection T‖)
  change HasSum (fun n => 2*(1-(inner ℝ u v)^n)*
    ‖clockLift (GaussianNumberSectors.projection n) (field ‖timeDirection T‖ u hu)‖^2)
      (‖field ‖timeDirection T‖ u hu-field ‖timeDirection T‖ v hv‖^2) at hs
  have hr : inner ℝ u v = 1-h := rotation_inner _ _ hu (futureClock_orthogonal T) _
  rw [hr,actual_point_field T hT] at hs
  change HasSum _ (‖IBMRandomTimeHilbert.randomSourceL2 T-clockPerturbed T hT h h0 h1‖^2) at hs
  rw [actual_perturbation_exact] at hs
  exact hs

end OperatorDerivativeRewrite.Foundation.IBMClockNoiseSpectral

namespace OperatorDerivativeRewrite.Foundation.IBMClockNoiseSpectral
open GaussianObservationCorrelation
open InfiniteGaussian IBMClockNoiseRegularity GaussianClockValueOperators
open IBMClockBochnerConverse

theorem folded_source_sign_invariant (c : ℝ) (u : CoefficientSpace) (hu : ‖u‖ = 1) :
    field c u hu = field c (-u) (by simpa only [norm_neg] using hu) := by
  have hz : sensitivity u (-u) = 0 := by
    rw [sensitivity_exact,add_neg_cancel,sub_neg_eq_add,norm_zero,← two_smul ℝ u,norm_smul]
    norm_num
    left
    ring
  have he := field_diff_sq c u (-u) hu (by simpa only [norm_neg] using hu)
  rw [hz,mul_zero] at he
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp he))

theorem folded_odd_clock_sector (c : ℝ) (u : CoefficientSpace) (hu : ‖u‖ = 1)
    (n : ℕ) (hn : Odd n) :
    clockLift (GaussianNumberSectors.projection n) (field c u hu) = 0 := by
  have hs := clock_sector_noise_hasSum u (-u) hu (by simpa only [norm_neg] using hu)
    (IBMClockWeakGraphObstruction.sectionClass c)
  change HasSum (fun m => 2*(1-(inner ℝ u (-u))^m)*
    ‖clockLift (GaussianNumberSectors.projection m) (field c u hu)‖^2)
      (‖field c u hu-field c (-u) (by simpa only [norm_neg] using hu)‖^2) at hs
  have hz : ‖field c u hu-field c (-u) (by simpa only [norm_neg] using hu)‖^2 = 0 := by
    rw [folded_source_sign_invariant c u hu,sub_self,norm_zero,zero_pow (by norm_num : 2 ≠ 0)]
  simp only [inner_neg_right,real_inner_self_eq_norm_sq,hu,one_pow,hz] at hs
  have hw (m : ℕ) : 0 ≤ 2*(1-(-1:ℝ)^m)*
      ‖clockLift (GaussianNumberSectors.projection m) (field c u hu)‖^2 := by
    rcases Nat.even_or_odd m with hm|hm <;> rw [hm.neg_one_pow] <;> positivity
  have hb := hs.summable.le_tsum n (fun m _ => hw m)
  rw [hs.tsum_eq,hn.neg_one_pow] at hb
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (clockLift (GaussianNumberSectors.projection n) (field c u hu))]

theorem actual_odd_clock_sector (T : ℝ≥0) (hT : 0 < T) (n : ℕ) (hn : Odd n) :
    clockLift (GaussianNumberSectors.projection n) (IBMRandomTimeHilbert.randomSourceL2 T) = 0 := by
  rw [← actual_point_field T hT]
  exact folded_odd_clock_sector _ _ _ n hn

end OperatorDerivativeRewrite.Foundation.IBMClockNoiseSpectral

namespace OperatorDerivativeRewrite.Foundation.IBMClockNoiseSpectral
open GaussianObservationCorrelation
open InfiniteGaussian GaussianClockSourceSpectral

theorem actual_odd_clock_block (T : ℝ≥0) (hT : 0 < T) (m n : ℕ) (hn : Odd n) :
    block m n (IBMRandomTimeHilbert.randomSourceL2 T) = 0 := by
  rw [block,ContinuousLinearMap.comp_apply,actual_odd_clock_sector T hT n hn,map_zero]

end OperatorDerivativeRewrite.Foundation.IBMClockNoiseSpectral
