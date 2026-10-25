import Foundation.IBMFoldedClockAbsolute
import Foundation.IBMClockSectionEnergyObstruction
import Foundation.IBMPointClockDomainObstruction
import Foundation.BochnerL2Dominated
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
/-! Exact correlated-clock noise sensitivity for the actual reflected-clock IBM endpoint.
The endpoint's ordinary joint derivative obstruction is preserved. Correlation
energy has a sharp critical index 1/2; identification with a spectral fractional
domain or a physical correction topology is a separate, unproved bridge.
The auxiliary clock direction uses a future increment and is not causal. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockNoiseRegularity
open InfiniteGaussian GaussianAbsoluteMoments IBMContinuousScenery

def sensitivity (u v : CoefficientSpace) : ℝ :=
  ∫ ω, ‖sourceScenery |firstChaosEmbedding u ω| -
    sourceScenery |firstChaosEmbedding v ω|‖ ^ 2 ∂gaussianProduct

theorem folded_distance (x y : ℝ) :
    ‖sourceScenery |x| - sourceScenery |y|‖ ^ 2 =
      |x+y|+|x-y|-|x|-|y| := by
  rw [sourceScenery_increment_sq]
  have hm := IBMFoldedClockAbsolute.min_absolute_identity x y
  rcases le_total |x| |y| with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h),min_eq_left h] at *
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr h),min_eq_right h] at *
    linarith

private theorem first_absolute (u : CoefficientSpace) :
    (∫ ω, |firstChaosEmbedding u ω| ∂gaussianProduct) = ‖u‖ * standardMoment 1 := by
  simpa only [pow_one] using firstChaos_absolute_moment u 1

private theorem sum_absolute (u v : CoefficientSpace) :
    (∫ ω, |firstChaosEmbedding u ω + firstChaosEmbedding v ω| ∂gaussianProduct) =
      ‖u+v‖ * standardMoment 1 := by
  have he := Lp.coeFn_add (firstChaosEmbedding u) (firstChaosEmbedding v)
  rw [← map_add] at he
  have hi := integral_congr_ae (he.fun_comp abs)
  simp only [Function.comp_def,Pi.add_apply] at hi
  exact hi.symm.trans (first_absolute _)

private theorem sub_absolute (u v : CoefficientSpace) :
    (∫ ω, |firstChaosEmbedding u ω - firstChaosEmbedding v ω| ∂gaussianProduct) =
      ‖u-v‖ * standardMoment 1 := by
  have he := Lp.coeFn_sub (firstChaosEmbedding u) (firstChaosEmbedding v)
  rw [← map_sub] at he
  have hi := integral_congr_ae (he.fun_comp abs)
  simp only [Function.comp_def,Pi.sub_apply] at hi
  exact hi.symm.trans (first_absolute _)

theorem sensitivity_exact (u v : CoefficientSpace) :
    sensitivity u v = (‖u+v‖+‖u-v‖-‖u‖-‖v‖)*standardMoment 1 := by
  have hu := ((Lp.memLp (firstChaosEmbedding u)).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2))
  have hv := ((Lp.memLp (firstChaosEmbedding v)).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2))
  unfold sensitivity
  simp_rw [folded_distance]
  have h1 := integral_sub (((hu.add hv).abs.add (hu.sub hv).abs).sub hu.abs) hv.abs
  have h2 := integral_sub ((hu.add hv).abs.add (hu.sub hv).abs) hu.abs
  have h3 := integral_add (hu.add hv).abs (hu.sub hv).abs
  simp only [Pi.add_apply,Pi.sub_apply] at h1 h2 h3
  rw [h1,h2,h3,sum_absolute,sub_absolute,first_absolute,first_absolute]
  ring

theorem unit_sensitivity (u v : CoefficientSpace) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    sensitivity u v = standardMoment 1 *
      (Real.sqrt (2+2*inner ℝ u v)+Real.sqrt (2-2*inner ℝ u v)-2) := by
  have hp : ‖u+v‖^2 = 2+2*inner ℝ u v := by rw [norm_add_sq_real,hu,hv]; ring
  have hm : ‖u-v‖^2 = 2-2*inner ℝ u v := by rw [norm_sub_sq_real,hu,hv]; ring
  have hp' : ‖u+v‖ = Real.sqrt (2+2*inner ℝ u v) := by
    rw [← hp,Real.sqrt_sq (norm_nonneg _)]
  have hm' : ‖u-v‖ = Real.sqrt (2-2*inner ℝ u v) := by
    rw [← hm,Real.sqrt_sq (norm_nonneg _)]
  rw [sensitivity_exact,hp',hm',hu,hv]
  ring

private theorem radical_bounds (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    Real.sqrt (2-2*ρ)/4 ≤ Real.sqrt (2+2*ρ)+Real.sqrt (2-2*ρ)-2 ∧
      Real.sqrt (2+2*ρ)+Real.sqrt (2-2*ρ)-2 ≤ Real.sqrt (2-2*ρ) := by
  have ha := Real.sqrt_nonneg (2-2*ρ)
  have hb := Real.sqrt_nonneg (2+2*ρ)
  have ha2 := Real.sq_sqrt (show 0 ≤ 2-2*ρ by linarith)
  have hb2 := Real.sq_sqrt (show 0 ≤ 2+2*ρ by linarith)
  have ha' : Real.sqrt (2-2*ρ) ≤ 3/2 := by nlinarith
  have hb' : Real.sqrt (2+2*ρ) ≤ 2 := by nlinarith
  constructor
  · by_contra hn
    have hneg : Real.sqrt (2+2*ρ) < 2-(3/4)*Real.sqrt (2-2*ρ) := by linarith
    have hr : 0 ≤ 2-(3/4)*Real.sqrt (2-2*ρ) := by linarith
    have hsq := mul_self_lt_mul_self hb hneg
    nlinarith [mul_nonneg ha (show 0 ≤ 3-(25/16)*Real.sqrt (2-2*ρ) by linarith)]
  · linarith

theorem unit_sensitivity_bounds (u v : CoefficientSpace) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hρ0 : 0 ≤ inner ℝ u v) (hρ1 : inner ℝ u v ≤ 1) :
    standardMoment 1 * Real.sqrt (2-2*inner ℝ u v)/4 ≤ sensitivity u v ∧
      sensitivity u v ≤ standardMoment 1 * Real.sqrt (2-2*inner ℝ u v) := by
  rw [unit_sensitivity u v hu hv]
  have h := radical_bounds (inner ℝ u v) hρ0 hρ1
  have hc := standardMoment_nonnegative 1
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h.1 hc]
  · exact mul_le_mul_of_nonneg_left h.2 hc

def rotation (u v : CoefficientSpace) (ρ : ℝ) : CoefficientSpace :=
  ρ • u + Real.sqrt (1-ρ^2) • v

theorem rotation_inner (u v : CoefficientSpace) (hu : ‖u‖ = 1)
    (huv : inner ℝ u v = 0) (ρ : ℝ) : inner ℝ u (rotation u v ρ) = ρ := by
  simp only [rotation,inner_add_right,real_inner_smul_right,huv,mul_zero,add_zero,
    real_inner_self_eq_norm_sq,hu,one_pow,mul_one]

theorem rotation_norm (u v : CoefficientSpace) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = 0) (ρ : ℝ) (hρ : |ρ| ≤ 1) : ‖rotation u v ρ‖ = 1 := by
  have hs : 0 ≤ 1-ρ^2 := by nlinarith [sq_abs ρ,abs_nonneg ρ]
  have hn : ‖rotation u v ρ‖^2 = 1 := by
    simp only [rotation,norm_add_sq_real,norm_smul,Real.norm_eq_abs,hu,hv,mul_one,
      sq_abs,real_inner_smul_left,real_inner_smul_right,huv,mul_zero,
      Real.sq_sqrt hs]
    ring
  nlinarith [norm_nonneg (rotation u v ρ)]

def field (c : ℝ) (u : CoefficientSpace) (hu : ‖u‖ = 1) :
    Lp GaussianL2 2 gaussianProduct :=
  IBMClockBochnerConverse.fieldPullback u hu (IBMClockWeakGraphObstruction.sectionClass c)

theorem field_ae (c : ℝ) (u : CoefficientSpace) (hu : ‖u‖ = 1) :
    field c u hu =ᵐ[gaussianProduct]
      fun ω => sourceScenery |c*firstChaosEmbedding u ω| := by
  have hmp := IBMClockObservationGraph.observation_measurePreserving u hu
  exact (IBMClockBochnerConverse.fieldPullback_ae u hu _).trans
    (hmp.quasiMeasurePreserving.ae_eq_comp (IBMClockWeakGraphObstruction.sectionClass_ae c))

theorem folded_scaled_distance (c x y : ℝ) :
    ‖sourceScenery |c*x|-sourceScenery |c*y|‖^2 =
      |c| *‖sourceScenery |x|-sourceScenery |y|‖^2 := by
  rw [folded_distance,folded_distance,← mul_add,← mul_sub]
  simp only [abs_mul]
  ring

theorem field_diff_sq (c : ℝ) (u v : CoefficientSpace) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖field c u hu-field c v hv‖^2 = |c| *sensitivity u v := by
  rw [BochnerL2Dominated.norm_sq_integral,sensitivity,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (field c u hu) (field c v hv),field_ae c u hu,field_ae c v hv]
    with ω hs hu hv
  rw [hs]
  simp only [Pi.sub_apply,hu,hv]
  exact folded_scaled_distance c _ _

theorem actual_point_field (T : ℝ≥0) (hT : 0 < T) :
    field ‖IBMClockLinearDivergence.timeDirection T‖
      (IBMPointClockDomainObstruction.unitClock T)
      (IBMPointClockDomainObstruction.unitClock_norm T hT) =
        IBMRandomTimeHilbert.randomSourceL2 T :=
  IBMPointClockDomainObstruction.point_pullback T hT

theorem rotation_field_bounds (c : ℝ) (u v : CoefficientSpace)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    let hrot := rotation_norm u v hu hv huv ρ (abs_le.mpr ⟨by linarith,hρ1⟩)
    |c| * standardMoment 1 * Real.sqrt (2-2*ρ)/4 ≤
        ‖field c u hu-field c (rotation u v ρ) hrot‖^2 ∧
      ‖field c u hu-field c (rotation u v ρ) hrot‖^2 ≤
        |c| * standardMoment 1 * Real.sqrt (2-2*ρ) := by
  dsimp only
  rw [field_diff_sq]
  have hrot := rotation_norm u v hu hv huv ρ (abs_le.mpr ⟨by linarith,hρ1⟩)
  have h := unit_sensitivity_bounds u (rotation u v ρ) hu hrot
    (by rw [rotation_inner u v hu huv];exact hρ0)
    (by rw [rotation_inner u v hu huv];exact hρ1)
  rw [rotation_inner u v hu huv] at h
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h.1 (abs_nonneg c)]
  · nlinarith [mul_le_mul_of_nonneg_left h.2 (abs_nonneg c)]

theorem rotation_field_fourth_bounds (c : ℝ) (u v : CoefficientSpace)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    let hrot := rotation_norm u v hu hv huv ρ (abs_le.mpr ⟨by linarith,hρ1⟩)
    c^2*(standardMoment 1)^2*(1-ρ)/8 ≤
        ‖field c u hu-field c (rotation u v ρ) hrot‖^4 ∧
      ‖field c u hu-field c (rotation u v ρ) hrot‖^4 ≤
        2*c^2*(standardMoment 1)^2*(1-ρ) := by
  dsimp only
  have h := rotation_field_bounds c u v hu hv huv ρ hρ0 hρ1
  dsimp only at h
  have hc := standardMoment_nonnegative 1
  have hr := Real.sqrt_nonneg (2-2*ρ)
  have hr2 := Real.sq_sqrt (show 0 ≤ 2-2*ρ by linarith)
  have hp : 0 ≤ |c| * standardMoment 1 * Real.sqrt (2-2*ρ)/4 := by positivity
  have hq : 0 ≤ |c| * standardMoment 1 * Real.sqrt (2-2*ρ) := by positivity
  have hl := pow_le_pow_left₀ hp h.1 2
  have hu' := pow_le_pow_left₀ (sq_nonneg _) h.2 2
  have he : (|c| * standardMoment 1 * Real.sqrt (2-2*ρ))^2 =
      2*c^2*(standardMoment 1)^2*(1-ρ) := by
    rw [mul_pow,mul_pow,sq_abs,hr2]
    ring
  rw [div_pow,he] at hl
  rw [he] at hu'
  simp only [← pow_mul] at hl hu'
  constructor
  · nlinarith only [hl]
  · exact hu'

end OperatorDerivativeRewrite.Foundation.IBMClockNoiseRegularity


namespace OperatorDerivativeRewrite.Foundation.IBMClockNoiseRegularity

def rate (h : ℝ) : ℝ := Real.sqrt (4-2*h)+Real.sqrt (2*h)-2

theorem rate_bounds (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    Real.sqrt (2*h)/4 ≤ rate h ∧ rate h ≤ Real.sqrt (2*h) := by
  have hb := radical_bounds (1-h) (by linarith) (by linarith)
  rw [show 2+2*(1-h) = 4-2*h by ring,show 2-2*(1-h) = 2*h by ring] at hb
  exact hb

def weightedRate (a h : ℝ) : ℝ := rate h / h^(1+a)

private theorem weighted_power (a h : ℝ) (hh : 0 < h) :
    Real.sqrt (2*h) / h^(1+a) = Real.sqrt 2 * h^(-a-1/2) := by
  calc
    _ = Real.sqrt 2 * (h^(1/2 : ℝ)/h^(1+a)) := by
      simp only [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_eq_rpow]
      ring
    _ = Real.sqrt 2 * h^((1/2 : ℝ)-(1+a)) := by rw [Real.rpow_sub hh]
    _ = _ := by congr 2; ring

private theorem weighted_bounds (a h : ℝ) (hh0 : 0 < h) (hh1 : h ≤ 1) :
    Real.sqrt 2 * h^(-a-1/2)/4 ≤ weightedRate a h ∧
      weightedRate a h ≤ Real.sqrt 2 * h^(-a-1/2) := by
  have hb := rate_bounds h hh0.le hh1
  have hp : 0 < h^(1+a) := Real.rpow_pos_of_pos hh0 _
  unfold weightedRate
  constructor
  · rw [← weighted_power a h hh0]
    convert div_le_div_of_nonneg_right hb.1 hp.le using 1; ring
  · rw [← weighted_power a h hh0]
    exact div_le_div_of_nonneg_right hb.2 hp.le

private theorem weighted_measurable (a : ℝ) : Measurable (weightedRate a) := by
  unfold weightedRate rate
  fun_prop

private theorem weighted_nonneg (a h : ℝ) (hh0 : 0 < h) (hh1 : h ≤ 1) :
    0 ≤ weightedRate a h :=
  (by positivity : 0 ≤ Real.sqrt 2 * h^(-a-1/2)/4).trans (weighted_bounds a h hh0 hh1).1

theorem weighted_integrable_iff (a : ℝ) :
    IntegrableOn (weightedRate a) (Ioo 0 1) volume ↔ a < 1/2 := by
  have hpow := intervalIntegral.integrableOn_Ioo_rpow_iff (s := -a-1/2)
    (by norm_num : (0:ℝ) < 1)
  have hm : AEStronglyMeasurable (fun h : ℝ => h^(-a-1/2))
      (volume.restrict (Ioo 0 1)) := by fun_prop
  constructor
  · intro hi
    have hl : IntegrableOn (fun h : ℝ => Real.sqrt 2/4 * h^(-a-1/2)) (Ioo 0 1) volume := by
      apply hi.mono' (hm.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
      have hb := (weighted_bounds a h hh.1 hh.2.le).1
      rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hh.1.le _))]
      nlinarith only [hb]
    have hr : IntegrableOn (fun h : ℝ => h^(-a-1/2)) (Ioo 0 1) volume :=
      (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr
        (by positivity : Real.sqrt 2/4 ≠ 0)) _).mp hl
    have := hpow.mp hr
    linarith
  · intro ha
    have hp : IntegrableOn (fun h : ℝ => h^(-a-1/2)) (Ioo 0 1) volume :=
      hpow.mpr (by linarith)
    apply (hp.const_mul (Real.sqrt 2)).mono' (weighted_measurable a).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    rw [Real.norm_of_nonneg (weighted_nonneg a h hh.1 hh.2.le)]
    exact (weighted_bounds a h hh.1 hh.2.le).2

end OperatorDerivativeRewrite.Foundation.IBMClockNoiseRegularity

namespace OperatorDerivativeRewrite.Foundation.IBMClockNoiseRegularity
open InfiniteGaussian GaussianAbsoluteMoments IBMClockLinearDivergence
open IBMPointClockDomainObstruction
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable

theorem time_direction_inner (s t : ℝ≥0) :
    inner ℝ (timeDirection s) (timeDirection t) = min (s : ℝ) t :=
    ((SeparableHilbertEmbedding.hilbertEmbedding GaussianTimeHilbert.TimeHilbert).inner_map_map _ _)
    |>.trans (GaussianTimeHilbert.timeVector_inner s t)

def futureClock (T : ℝ≥0) : CoefficientSpace := timeDirection (T+1)-timeDirection T

theorem futureClock_norm (T : ℝ≥0) : ‖futureClock T‖ = 1 := by
  have hn : ‖futureClock T‖^2 = 1 := by
    rw [futureClock,norm_sub_sq_real,timeDirection_norm_sq,timeDirection_norm_sq,
      time_direction_inner,min_eq_right (show (T:ℝ) ≤ (T+1:ℝ≥0) by simp)]
    push_cast
    ring
  nlinarith [norm_nonneg (futureClock T)]

theorem futureClock_orthogonal (T : ℝ≥0) : inner ℝ (unitClock T) (futureClock T) = 0 := by
  rw [unitClock,real_inner_smul_left,futureClock,inner_sub_right,time_direction_inner,
    time_direction_inner,min_eq_left (show (T:ℝ) ≤ (T+1:ℝ≥0) by simp),min_self,
    sub_self,mul_zero]

def clockPerturbed (T : ℝ≥0) (hT : 0 < T) (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    Lp GaussianL2 2 gaussianProduct :=
  field ‖timeDirection T‖ (rotation (unitClock T) (futureClock T) (1-h))
    (rotation_norm _ _ (unitClock_norm T hT) (futureClock_norm T) (futureClock_orthogonal T)
      (1-h) (abs_le.mpr ⟨by linarith,by linarith⟩))

theorem actual_perturbation_exact (T : ℝ≥0) (hT : 0 < T) (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    ‖IBMRandomTimeHilbert.randomSourceL2 T-clockPerturbed T hT h h0 h1‖^2 =
      ‖timeDirection T‖ * standardMoment 1 * rate h := by
  rw [← actual_point_field T hT,clockPerturbed,field_diff_sq,
    unit_sensitivity _ _ (unitClock_norm T hT)
      (rotation_norm _ _ (unitClock_norm T hT) (futureClock_norm T) (futureClock_orthogonal T)
        (1-h) (abs_le.mpr ⟨by linarith,by linarith⟩)),
    rotation_inner _ _ (unitClock_norm T hT) (futureClock_orthogonal T),
    abs_of_nonneg (norm_nonneg _)]
  rw [show 2+2*(1-h)=4-2*h by ring,show 2-2*(1-h)=2*h by ring]
  unfold rate
  ring

theorem actual_weighted_integrable_iff (T : ℝ≥0) (hT : 0 < T) (a : ℝ) :
    IntegrableOn (fun h => ‖timeDirection T‖ * standardMoment 1 * weightedRate a h)
      (Ioo 0 1) volume ↔ a < 1/2 := by
  have hc : ‖timeDirection T‖ * standardMoment 1 ≠ 0 :=
    (mul_pos (timeDirection_norm_pos T hT)
      IBMPhysicalL2Obstruction.first_absolute_moment_pos).ne'
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc) (weightedRate a)).trans
    (weighted_integrable_iff a)

end OperatorDerivativeRewrite.Foundation.IBMClockNoiseRegularity

namespace OperatorDerivativeRewrite.Foundation.IBMClockNoiseRegularity
open InfiniteGaussian IBMClockLinearDivergence

def endpointCurve (T : ℝ≥0) (hT : 0 < T) (h : ℝ) : Lp GaussianL2 2 gaussianProduct := by
  classical
  exact if hm : h ∈ Icc (0:ℝ) 1 then clockPerturbed T hT h hm.1 hm.2
    else IBMRandomTimeHilbert.randomSourceL2 T

def endpointWeightedEnergy (T : ℝ≥0) (hT : 0 < T) (a h : ℝ) : ℝ :=
  ‖IBMRandomTimeHilbert.randomSourceL2 T-endpointCurve T hT h‖^2 / h^(1+a)

theorem endpoint_weighted_eq (T : ℝ≥0) (hT : 0 < T) (a : ℝ) :
    EqOn (endpointWeightedEnergy T hT a)
      (fun h => ‖timeDirection T‖ * GaussianAbsoluteMoments.standardMoment 1 * weightedRate a h)
      (Ioo 0 1) := by
  intro h hh
  unfold endpointWeightedEnergy endpointCurve
  rw [dite_eq_left ⟨hh.1.le,hh.2.le⟩,actual_perturbation_exact]
  unfold weightedRate
  ring

theorem endpoint_energy_integrable_iff (T : ℝ≥0) (hT : 0 < T) (a : ℝ) :
    IntegrableOn (endpointWeightedEnergy T hT a) (Ioo 0 1) volume ↔ a < 1/2 :=
  (integrableOn_congr_fun (endpoint_weighted_eq T hT a) measurableSet_Ioo).trans
    (actual_weighted_integrable_iff T hT a)

end OperatorDerivativeRewrite.Foundation.IBMClockNoiseRegularity

namespace OperatorDerivativeRewrite.Foundation.IBMClockNoiseRegularity
open InfiniteGaussian IBMTimeAveragedObservable

theorem joint_endpoint_energy_integrable_iff (T : ℝ≥0) (hT : 0 < T) (a : ℝ) :
    IntegrableOn (fun h =>
      ‖(intrinsicCurve T : JointL2)-jointRealization (endpointCurve T hT h)‖^2 / h^(1+a))
      (Ioo 0 1) volume ↔ a < 1/2 := by
  change IntegrableOn (fun h =>
    ‖jointRealization (IBMRandomTimeHilbert.randomSourceL2 T)-
      jointRealization (endpointCurve T hT h)‖^2 / h^(1+a)) (Ioo 0 1) volume ↔ _
  simp only [← map_sub,jointRealization.norm_map]
  exact endpoint_energy_integrable_iff T hT a

end OperatorDerivativeRewrite.Foundation.IBMClockNoiseRegularity

namespace OperatorDerivativeRewrite.Foundation.IBMClockNoiseRegularity
open InfiniteGaussian IBMTimeAveragedObservable IBMConstructedSources

theorem field_actual_ae (c : ℝ) (u : CoefficientSpace) (hu : ‖u‖ = 1) :
    jointRealization (field c u hu) =ᵐ[IBMSourceLaws.jointMeasure]
      fun p => sceneryPath p.1 |c*firstChaosEmbedding u p.2| := by
  apply jointRealization_ae_of_sections _ _
  · have hm : Measurable (fun p : IBMSourceLaws.JointSample => firstChaosEmbedding u p.2) :=
      (Lp.stronglyMeasurable (firstChaosEmbedding u)).measurable.comp measurable_snd
    exact continuous_eval.measurable.comp
      ((sceneryPath_measurable.comp measurable_fst).prodMk (continuous_abs.measurable.comp (hm.const_mul c)))
  · filter_upwards [field_ae c u hu] with Y hY
    rw [hY]
    exact (sceneryPath_coordinate_ae |c*firstChaosEmbedding u Y|).symm

end OperatorDerivativeRewrite.Foundation.IBMClockNoiseRegularity
