import Foundation.BrownianStickyOccupation
import Foundation.BrownianStoppedFourier
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! An actual measurable continuous two-point process with compensating clocks on independent sources. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.StickyPairPaths
open InfiniteGaussian IBMConstructedSources BrownianMassRandomTimeChange
attribute [local irreducible] IBMConstructedSources.clockPath

abbrev Sample := SampleSpace × SampleSpace

def sourceMeasure : Measure Sample := gaussianProduct.prod gaussianProduct

instance source_probability : IsProbabilityMeasure sourceMeasure := by
  unfold sourceMeasure
  infer_instance

def centerClock (κ : ℝ≥0) (w : SampleSpace) (t : ℝ≥0) : ℝ≥0 := 2*t-inverse κ w t

theorem center_clock_real (κ : ℝ≥0) (w : SampleSpace) (t : ℝ≥0) :
    (centerClock κ w t : ℝ)=2*(t:ℝ)-(inverse κ w t : ℝ) := by
  have h : inverse κ w t ≤ 2*t := (inverse_le κ w t).trans (by
    calc t = 1*t := (one_mul t).symm
         _ ≤ 2*t := mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
  rw [centerClock,NNReal.coe_sub h]
  norm_num

theorem center_clock_bounds (κ : ℝ≥0) (w : SampleSpace) (t : ℝ≥0) :
    t ≤ centerClock κ w t ∧ centerClock κ w t ≤ 2*t := by
  have h := inverse_le κ w t
  have hR : (inverse κ w t : ℝ) ≤ t := by exact_mod_cast h
  have hn := NNReal.coe_nonneg (inverse κ w t)
  constructor
  · apply NNReal.coe_le_coe.mp
    rw [center_clock_real]
    linarith
  · apply NNReal.coe_le_coe.mp
    rw [center_clock_real]
    push_cast
    linarith

theorem center_clock_continuous (κ : ℝ≥0) (w : SampleSpace) : Continuous (centerClock κ w) :=
  (continuous_const.mul continuous_id).sub (inverse_continuous κ w)

theorem center_clock_monotone (κ : ℝ≥0) (w : SampleSpace) : Monotone (centerClock κ w) := by
  intro s t hst
  have hi := inverse_increment κ w s t hst
  have hR : (s:ℝ) ≤ t := by exact_mod_cast hst
  apply NNReal.coe_le_coe.mp
  rw [center_clock_real,center_clock_real]
  linarith

theorem center_clock_measurable (κ t : ℝ≥0) : Measurable (fun w => centerClock κ w t) :=
  measurable_const.sub (inverse_coordinate_measurable κ t)

theorem center_clock_zero (κ : ℝ≥0) (w : SampleSpace) : centerClock κ w 0=0 := by
  simp [centerClock,inverse_zero]

theorem clock_balance (κ : ℝ≥0) (w : SampleSpace) (t : ℝ≥0) :
    centerClock κ w t+inverse κ w t=2*t := by
  apply NNReal.coe_injective
  push_cast
  rw [center_clock_real]
  ring

def centeredPath (w : SampleSpace) : C(ℝ≥0,ℝ) :=
  ⟨fun t => clockPath w t-clockPath w 0,(clockPath w).continuous.sub continuous_const⟩

theorem centered_zero (w : SampleSpace) : centeredPath w 0=0 := sub_self _

theorem centered_measurable : Measurable centeredPath := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact ((ContinuousMap.measurable_eval t).comp clockPath_measurable).sub
    ((ContinuousMap.measurable_eval 0).comp clockPath_measurable)

def separationPath (κ : ℝ≥0) (w : Sample) : C(ℝ≥0,ℝ) :=
  (centeredPath w.1).comp (inversePath κ w.1)

def centerPath (κ : ℝ≥0) (w : Sample) : C(ℝ≥0,ℝ) :=
  (centeredPath w.2).comp ⟨centerClock κ w.1,center_clock_continuous κ w.1⟩

def leftPath (κ : ℝ≥0) (w : Sample) : C(ℝ≥0,ℝ) :=
  ⟨fun t => (centerPath κ w t+separationPath κ w t)/Real.sqrt 2,
    ((centerPath κ w).continuous.add (separationPath κ w).continuous).div_const _⟩

def rightPath (κ : ℝ≥0) (w : Sample) : C(ℝ≥0,ℝ) :=
  ⟨fun t => (centerPath κ w t-separationPath κ w t)/Real.sqrt 2,
    ((centerPath κ w).continuous.sub (separationPath κ w).continuous).div_const _⟩

def pairPath (κ : ℝ≥0) (w : Sample) : C(ℝ≥0,ℝ × ℝ) := (leftPath κ w).prodMk (rightPath κ w)

theorem separation_measurable (κ : ℝ≥0) : Measurable (separationPath κ) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact continuous_eval.measurable.comp
    ((centered_measurable.comp measurable_fst).prodMk ((inverse_coordinate_measurable κ t).comp measurable_fst))

theorem center_measurable (κ : ℝ≥0) : Measurable (centerPath κ) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact continuous_eval.measurable.comp
    ((centered_measurable.comp measurable_snd).prodMk ((center_clock_measurable κ t).comp measurable_fst))

theorem left_measurable (κ : ℝ≥0) : Measurable (leftPath κ) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact (((ContinuousMap.measurable_eval t).comp (center_measurable κ)).add
    ((ContinuousMap.measurable_eval t).comp (separation_measurable κ))).div_const _

theorem right_measurable (κ : ℝ≥0) : Measurable (rightPath κ) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact (((ContinuousMap.measurable_eval t).comp (center_measurable κ)).sub
    ((ContinuousMap.measurable_eval t).comp (separation_measurable κ))).div_const _

theorem pair_measurable (κ : ℝ≥0) : Measurable (pairPath κ) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact ((ContinuousMap.measurable_eval t).comp (left_measurable κ)).prodMk
    ((ContinuousMap.measurable_eval t).comp (right_measurable κ))

theorem pair_zero (κ : ℝ≥0) (w : Sample) : pairPath κ w 0=(0,0) := by
  simp [pairPath,leftPath,rightPath,centerPath,separationPath,center_clock_zero,
    inversePath,inverse_zero,centered_zero]

def pathLaw (κ : ℝ≥0) : Measure C(ℝ≥0,ℝ × ℝ) := sourceMeasure.map (pairPath κ)

instance pathLaw_probability (κ : ℝ≥0) : IsProbabilityMeasure (pathLaw κ) := by
  unfold pathLaw
  infer_instance

theorem pair_hasLaw (κ : ℝ≥0) : HasLaw (pairPath κ) (pathLaw κ) sourceMeasure :=
  ⟨(pair_measurable κ).aemeasurable,rfl⟩

theorem difference (κ : ℝ≥0) (w : Sample) (t : ℝ≥0) :
    leftPath κ w t-rightPath κ w t=Real.sqrt 2*separationPath κ w t := by
  have hn : Real.sqrt (2:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hs : (2:ℝ)/Real.sqrt 2=Real.sqrt 2 := by
    apply (div_eq_iff hn).2
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  calc
    leftPath κ w t-rightPath κ w t=(2/Real.sqrt 2)*separationPath κ w t := by
      dsimp [leftPath,rightPath]
      ring
    _ = _ := by rw [hs]

theorem coincidence (κ : ℝ≥0) (w : Sample) (t : ℝ≥0) :
    leftPath κ w t=rightPath κ w t ↔ separationPath κ w t=0 := by
  rw [← sub_eq_zero,difference,mul_eq_zero]
  simp [ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))]

end OperatorDerivativeRewrite.Foundation.StickyPairPaths
