import Foundation.IBMPredictableBoundedSeries
import Foundation.IBMPastCoreDensity

/-! Actual stochastic outputs are IBM observable and orthogonal to the initial germ. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMPredictableIntegralObservable
open IBMTimeAveragedObservable IBMIntrinsicRightGerm IBMRightGermFiltration
open IBMPredictableRectangles IBMPredictableFiniteIntegral IBMPredictableLpDictionary
open IBMFullPredictableIntegral IBMNaturalFiltrationObstruction
set_option backward.isDefEq.respectTransparency false
local instance : MeasurableSpace Space := naturalFiltration.predictable

def jointOne : JointL2 := Lp.const 2 IBMSourceLaws.jointMeasure (1 : ℝ)

theorem jointOne_ae : jointOne =ᵐ[IBMSourceLaws.jointMeasure] (fun _ => (1 : ℝ)) :=
  Lp.coeFn_const 2 IBMSourceLaws.jointMeasure (1 : ℝ)

theorem jointOne_mem_past (s : ℝ≥0) : jointOne ∈ past s := by
  apply mem_lpMeas_iff_aestronglyMeasurable.mpr
  exact aestronglyMeasurable_const.congr jointOne_ae.symm

theorem rightPast_le_intrinsic (t : ℝ≥0) : rightPast t ≤ IntrinsicSpace :=
  (rightPast_le_past (lt_add_of_pos_right t (by norm_num : (0 : ℝ≥0) < 1))).trans
    (IBMPastCoreDensity.past_le_intrinsic (t+1))

theorem finite_mem_intrinsic (F : JointL2) (l : Index →₀ ℝ) :
    integralLinear F l ∈ IntrinsicSpace := by
  change (∑ d ∈ l.support, l d • basisIntegral F d) ∈ IntrinsicSpace
  exact IntrinsicSpace.sum_mem fun d _ => IntrinsicSpace.smul_mem _
    (rightPast_le_intrinsic (right d)
      (IBMGermPredictableStep.stepClass_mem_rightPast F (ordered d) (event_measurable d |> fun h =>
        IBMWeightedTerminalEnergy.eventCoefficient (left d) (event d) h)))

theorem finite_orthogonal_initial (F : JointL2) (l : Index →₀ ℝ) (g : JointL2)
    (hg : g ∈ rightPast 0) : inner ℝ g (integralLinear F l) = 0 := by
  change inner ℝ g (∑ d ∈ l.support, l d • basisIntegral F d) = 0
  rw [inner_sum]
  apply Finset.sum_eq_zero
  intro d _
  rw [real_inner_smul_right]
  have he := IBMGermPredictableStep.past_inner_step_zero F (ordered d)
    (IBMWeightedTerminalEnergy.eventCoefficient (left d) (event d) (event_measurable d)) g
    (rightPast_mono (zero_le : 0 ≤ left d) hg)
  change l d * inner ℝ g (basisIntegral F d) = 0
  rw [show inner ℝ g (basisIntegral F d) = 0 from he, mul_zero]

theorem integral_mem_intrinsic (F : JointL2) (H : PredictableL2 F) :
    integral F H ∈ IntrinsicSpace := by
  obtain ⟨a, _, ha⟩ := exists_actual_approximation F H
  apply (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).mem_of_tendsto ha
  exact Eventually.of_forall fun n => finite_mem_intrinsic F (a n)

theorem integral_orthogonal_initial (F : JointL2) (H : PredictableL2 F) (g : JointL2)
    (hg : g ∈ rightPast 0) : inner ℝ g (integral F H) = 0 := by
  obtain ⟨a, _, ha⟩ := exists_actual_approximation F H
  have ht := (innerSL ℝ g).continuous.continuousAt.tendsto.comp ha
  change Tendsto (fun n => inner ℝ g (integralLinear F (a n))) atTop
    (𝓝 (inner ℝ g (integral F H))) at ht
  have he n := finite_orthogonal_initial F (a n) g hg
  exact tendsto_nhds_unique ht (by simpa only [he] using tendsto_const_nhds (x := (0 : ℝ)))

theorem integral_centered (F : JointL2) (H : PredictableL2 F) :
    inner ℝ jointOne (integral F H) = 0 :=
  integral_orthogonal_initial F H jointOne (past_le_rightPast 0 (jointOne_mem_past 0))

end OperatorDerivativeRewrite.Foundation.IBMPredictableIntegralObservable
