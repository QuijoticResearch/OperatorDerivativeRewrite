import Foundation.IBMMixedPredictableEnergy
import Foundation.IBMTerminalSelfRepresentation

/-! Concrete signed covariance and cancellation for the ACTUAL IBM1 channel. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMActualMixedEnergyObstruction
open IBMTimeAveragedObservable IBMObservedTerminalMartingale IBMDeterministicRangeObstruction
open IBMPredictableRectangles IBMPredictableFiniteIntegral IBMPredictableRingContent
open IBMPredictableCovarianceMeasure IBMMixedPredictableEnergy

def unitCell : Set Space := rect 0 1 univ

theorem unitCell_ring : unitCell ∈ elementaryRing :=
  subset_supClosure (rect_mem 0 1 univ MeasurableSet.univ)

theorem ring_neg (F : JointL2) (E : Set Space) : ringIntegral (-F) E = -ringIntegral F E :=
  (ringOperator_eq E _).symm.trans (((ringOperator E).map_neg F).trans
    (congrArg Neg.neg (ringOperator_eq E F)))

theorem covariance_neg_diagonal (F : JointL2) {E : Set Space} (hE : E ∈ elementaryRing) :
    covariance F (-F) E = -‖ringIntegral F E‖^2 := by
  rw [covariance_ring F (-F) hE, ring_neg, inner_neg_right, real_inner_self_eq_norm_sq]

theorem observed_unit_cell : ringIntegral (observed 1) unitCell = observed 1 := by
  rw [unitCell, ringIntegral_rect _ 0 1 univ (by norm_num) MeasurableSet.univ,
    IBMGermPredictableStep.stepClass, IBMTerminalSelfRepresentation.weighted_unit]
  rw [terminal_class _ (observed_mem_past 1) le_rfl,
    IBMObservedInitialGerm.initial_channel_zero, sub_zero]

theorem actual_negative_covariance : covariance (observed 1) (-observed 1) unitCell < 0 := by
  rw [covariance_neg_diagonal _ unitCell_ring, observed_unit_cell]
  exact neg_lt_zero.mpr (sq_pos_of_pos (norm_pos_iff.mpr observed_one_ne_zero))

def unitPresentation : Index →₀ ℝ := Finsupp.single (IBMTerminalSelfRepresentation.unitIndex 1) 1

theorem unitPresentation_ring (F : JointL2) : integralLinear F unitPresentation = ringIntegral F unitCell := by
  simp only [unitPresentation, integralLinear, Finsupp.linearCombination_single, one_smul]
  exact (ringIntegral_rect F 0 1 univ (by norm_num) MeasurableSet.univ).symm

theorem actual_two_channel_cancellation :
    integralLinear (observed 1) unitPresentation + integralLinear (-observed 1) unitPresentation = 0 ∧
    0 < ‖IBMPredictableLpDictionary.dictionary (observed 1) unitPresentation‖^2 +
      ‖IBMPredictableLpDictionary.dictionary (-observed 1) unitPresentation‖^2 := by
  have hn : 0 < ‖observed 1‖^2 := sq_pos_of_pos (norm_pos_iff.mpr observed_one_ne_zero)
  have hp : integralLinear (observed 1) unitPresentation = observed 1 :=
    (unitPresentation_ring _).trans observed_unit_cell
  have hm : integralLinear (-observed 1) unitPresentation = -observed 1 :=
    (unitPresentation_ring _).trans ((ring_neg _ _).trans (congrArg Neg.neg observed_unit_cell))
  constructor
  · rw [hp, hm, add_neg_cancel]
  · rw [← IBMPredictableLpDictionary.dictionary_norm, ← IBMPredictableLpDictionary.dictionary_norm,
      hp, hm, norm_neg]
    linarith

end OperatorDerivativeRewrite.Foundation.IBMActualMixedEnergyObstruction
