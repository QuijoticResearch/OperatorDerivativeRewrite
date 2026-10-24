import Foundation.IBMActualIncrementMoments
import Foundation.IBMRawInitialPast
import Foundation.IBMClockOverlapEnergy

/-! Ordinary physical-time L2 cannot support a bounded integral normalized on
actual IBM deterministic steps. This does not exclude other integrand norms,
unbounded closed operators, or the verified Simpson/native constructions. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalL2Obstruction
open InfiniteGaussian IBMTimeAveragedObservable IBMRandomTimeHilbert
open IBMDeterministicRangeObstruction GaussianAbsoluteMoments IBMClockOverlapEnergy
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem observed_norm_sq (t : ℝ≥0) :
    ‖observed t‖^2 = Real.sqrt t * standardMoment 1 := by
  have he : ‖observed t‖^2 = ∫ ω, |GaussianTimeProcess.process t ω| ∂gaussianProduct := by
    change ‖jointRealization (randomSourceL2 t)‖^2 = _
    rw [jointRealization.norm_map, ← real_inner_self_eq_norm_sq, L2_inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [(randomSourceClass_memLp t).coeFn_toLp] with ω hω
    change randomSourceL2 t ω = randomSourceClass t ω at hω
    rw [hω, real_inner_self_eq_norm_sq, randomSourceClass_norm_sq]
  rw [he]
  have hm := IBMActualIncrementMoments.clock_absolute_moment 0 t 1
  have hc : (fun ω => |IBMConstructedSources.clockPath ω t -
      IBMConstructedSources.clockPath ω 0|^1) =ᵐ[gaussianProduct]
      (fun ω => |GaussianTimeProcess.process t ω|) := by
    filter_upwards [IBMConstructedSources.clockPath_coordinate_ae t,
      IBMConstructedSources.clockPath_coordinate_ae 0,
      GaussianTimeProcess.process_zero_ae] with ω ht hz hp
    simp only [ht,hz,hp,sub_zero,pow_one]
  simp only [NNReal.coe_zero,sub_zero,pow_one] at hm
  have hab : |(t:ℝ)| = (t:ℝ) := abs_of_nonneg t.property
  simp only [pow_one] at hc
  have hh := (integral_congr_ae hc).symm.trans hm
  simpa only [hab] using hh

theorem first_absolute_moment_pos : 0 < standardMoment 1 := by
  have hn : 0 < ‖observed 1‖^2 := sq_pos_of_pos (norm_pos_iff.mpr observed_one_ne_zero)
  simpa only [observed_norm_sq,NNReal.coe_one,Real.sqrt_one,one_mul] using hn

/-- No finite squared-energy constant works, even on arbitrarily short
deterministic initial intervals of any fixed positive horizon. -/
theorem short_step_energy_unbounded {T : ℝ≥0} (hT : 0 < T)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ t : ℝ≥0, 0 < t ∧ t ≤ T ∧ C * (t : ℝ) < ‖observed t‖^2 := by
  let c := standardMoment 1
  have hc : 0 < c := first_absolute_moment_pos
  let r := min (Real.sqrt T) (c/(C+1)) / 2
  have hs : 0 < Real.sqrt (T:ℝ) := Real.sqrt_pos.2 hT
  have hd : 0 < c/(C+1) := div_pos hc (by positivity)
  have hr : 0 < r := div_pos (lt_min hs hd) (by norm_num)
  have hrs : r ≤ Real.sqrt T := by
    have hm := min_le_left (Real.sqrt T) (c/(C+1))
    dsimp [r]
    linarith [lt_min hs hd]
  have hrd : r < c/(C+1) := by
    have hm := min_le_right (Real.sqrt T) (c/(C+1))
    dsimp [r]
    linarith [lt_min hs hd]
  have hcr : C*r < c := by
    have hh := (lt_div_iff₀ (show 0 < C+1 by positivity)).mp hrd
    nlinarith
  let t : ℝ≥0 := (r^2).toNNReal
  have ht : (t:ℝ) = r^2 := by simp only [t,Real.coe_toNNReal',max_eq_left (sq_nonneg r)]
  have htle : t ≤ T := by
    change (t:ℝ) ≤ (T:ℝ)
    rw [ht]
    have hh : r^2 ≤ (Real.sqrt (T:ℝ))^2 := pow_le_pow_left₀ hr.le hrs 2
    exact hh.trans_eq (Real.sq_sqrt T.property)
  refine ⟨t,?_,htle,?_⟩
  · change (0:ℝ) < (t:ℝ)
    rw [ht]
    exact sq_pos_of_pos hr
  · have hn := observed_norm_sq t
    rw [hn,ht]
    change C*r^2 < Real.sqrt (r^2)*c
    rw [Real.sqrt_sq (le_of_lt hr)]
    nlinarith [mul_lt_mul_of_pos_right hcr hr]

abbrev PhysicalL2 (T : ℝ≥0) := Lp ℝ 2 (window T)

def step (T t : ℝ≥0) : PhysicalL2 T :=
  indicatorConstLp 2 measurableSet_Ioc (measure_ne_top (window T) (Ioc 0 (t:ℝ))) (1:ℝ)

theorem step_actual (T t : ℝ≥0) :
    step T t =ᵐ[window T] (Ioc 0 (t:ℝ)).indicator (fun _ => (1:ℝ)) :=
  indicatorConstLp_coeFn

theorem step_norm_sq {T t : ℝ≥0} (ht : t ≤ T) : ‖step T t‖^2 = (t:ℝ) := by
  have hs : Ioc (0:ℝ) t ∩ Ioc 0 (T:ℝ) = Ioc 0 (t:ℝ) :=
    inter_eq_left.mpr (Ioc_subset_Ioc_right ht)
  have hm : (window T).real (Ioc 0 (t:ℝ)) = t := by
    simp only [window,measureReal_def,Measure.restrict_apply measurableSet_Ioc,hs,
      Real.volume_Ioc,sub_zero]
    exact ENNReal.toReal_ofReal t.property
  unfold step
  rw [norm_indicatorConstLp (by norm_num) (by norm_num),hm]
  norm_num only [norm_one,ENNReal.toReal_ofNat,one_mul]
  rw [← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt t.property

/-- No bounded linear map from ordinary deterministic physical-time L2 can
agree with actual IBM integration even on initial-interval indicator steps. -/
theorem no_bounded_step_integral {T : ℝ≥0} (hT : 0 < T)
    (J : PhysicalL2 T →L[ℝ] JointL2) :
    ¬ (∀ t : ℝ≥0, t ≤ T → J (step T t) = observed t) := by
  intro hJ
  obtain ⟨t,ht,hbound,hbad⟩ := short_step_energy_unbounded hT (‖J‖^2) (sq_nonneg _)
  have hn := J.le_opNorm (step T t)
  rw [hJ t hbound] at hn
  have hsq := pow_le_pow_left₀ (norm_nonneg (observed t)) hn 2
  rw [mul_pow,step_norm_sq hbound] at hsq
  exact (not_lt_of_ge hsq) hbad

/-- The obstruction uses literal actual increments, not just a choice of
abstract terminal classes. Deterministic inputs already rule out a bounded
ordinary physical-time L2 extension with the usual step normalization. -/
theorem no_actual_step_integral {T : ℝ≥0} (hT : 0 < T)
    (J : PhysicalL2 T →L[ℝ] JointL2) :
    ¬ (∀ t : ℝ≥0, t ≤ T → J (step T t) =ᵐ[IBMSourceLaws.jointMeasure]
      (fun p => IBMConstructedSources.ibmValue t p -
        IBMConstructedSources.ibmValue 0 p)) := by
  intro hJ
  apply no_bounded_step_integral hT J
  intro t ht
  apply Lp.ext
  filter_upwards [hJ t ht,observed_ae t,IBMRawInitialPast.ibm_zero_ae] with p hj ho hz
  rw [hz,sub_zero] at hj
  exact hj.trans ho.symm

end OperatorDerivativeRewrite.Foundation.IBMPhysicalL2Obstruction
