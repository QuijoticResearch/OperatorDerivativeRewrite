import Foundation.IBMFullPredictableIntegral
import Foundation.MultiplierCore
import Mathlib.MeasureTheory.VectorMeasure.Operations

/-! Genuine signed predictable covariance measures for the ACTUAL IBM channels. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMPredictableCovarianceMeasure
open IBMTimeAveragedObservable IBMIntrinsicRightGerm IBMObservedTerminalMartingale
open IBMIntrinsicMartingaleStep (Coefficient)
open IBMWeightedTerminalEnergy IBMGermPredictableStep IBMPredictableRectangles
open IBMPredictableFiniteIntegral IBMPredictableRingContent IBMJointPredictableEnergyMeasure
local instance : MeasurableSpace Space := IBMNaturalFiltrationObstruction.naturalFiltration.predictable
local instance (F : JointL2) : IsFiniteMeasure (predictableMeasure F) := finite_measure F
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem coefficient_memLp {s : ℝ≥0} (a : Coefficient s) :
    MemLp a.function ∞ IBMSourceLaws.jointMeasure :=
  MemLp.of_bound ((a.adapted.mono (IBMNaturalFiltrationObstruction.naturalFiltration.le s)).aestronglyMeasurable)
    a.bound a.bounded

theorem weightedTerminal_multiplier (F : JointL2) (s : ℝ≥0) (a : Coefficient s) :
    weightedTerminal F s a = boundedMultiplier a.function (coefficient_memLp a) F := by
  apply Lp.ext
  exact (weightedTerminal_ae F s a).trans
    ((boundedMultiplier_coeFn a.function (coefficient_memLp a) F).trans
      (Eventually.of_forall fun _ => smul_eq_mul _ _)).symm

def stepOperator (s t : ℝ≥0) (a : Coefficient s) : JointL2 →L[ℝ] JointL2 :=
  ((rightPast t).starProjection - (rightPast s).starProjection).comp
    (boundedMultiplier a.function (coefficient_memLp a))

theorem stepOperator_eq (F : JointL2) (s t : ℝ≥0) (a : Coefficient s) :
    stepOperator s t a F = stepClass F s t a := by
  change (rightPast t).starProjection (boundedMultiplier _ _ F) -
    (rightPast s).starProjection (boundedMultiplier _ _ F) = _
  rw [← weightedTerminal_multiplier]
  rfl

def finiteOperator (l : Index →₀ ℝ) : JointL2 →L[ℝ] JointL2 :=
  Finsupp.linearCombination ℝ
    (fun d => stepOperator (left d) (right d) (eventCoefficient (left d) (event d) (event_measurable d))) l

theorem finiteOperator_eq (F : JointL2) (l : Index →₀ ℝ) :
    finiteOperator l F = integralLinear F l := by
  simp only [finiteOperator, integralLinear, Finsupp.linearCombination_apply, Finsupp.sum,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, stepOperator_eq, basisIntegral]

def ringOperator (E : Set Space) : JointL2 →L[ℝ] JointL2 :=
  finiteOperator (Classical.choose (indicatorClass E).property)

theorem ringOperator_eq (E : Set Space) (F : JointL2) :
    ringOperator E F = ringIntegral F E := by
  let l := Classical.choose (indicatorClass E).property
  have hl : processLinear l = (indicatorClass E : Space → ℝ) :=
    Classical.choose_spec (indicatorClass E).property
  have hh : (⟨processLinear l, ⟨l, rfl⟩⟩ : processSpace) = indicatorClass E := Subtype.ext hl
  change finiteOperator l F = integral F (indicatorClass E)
  exact (finiteOperator_eq F l).trans ((integral_process F l).symm.trans (congrArg (integral F) hh))

theorem ring_terminal_add (F G : JointL2) (E : Set Space) :
    ringIntegral (F+G) E = ringIntegral F E + ringIntegral G E :=
  (ringOperator_eq E _).symm.trans (((ringOperator E).map_add F G).trans
    (congrArg₂ (fun x y : JointL2 => x+y) (ringOperator_eq E F) (ringOperator_eq E G)))

theorem ring_terminal_sub (F G : JointL2) (E : Set Space) :
    ringIntegral (F-G) E = ringIntegral F E - ringIntegral G E :=
  (ringOperator_eq E _).symm.trans (((ringOperator E).map_sub F G).trans
    (congrArg₂ (fun x y : JointL2 => x-y) (ringOperator_eq E F) (ringOperator_eq E G)))

def covariance (F G : JointL2) : SignedMeasure Space :=
  (1/4 : ℝ) • ((predictableMeasure (F+G)).toSignedMeasure -
    (predictableMeasure (F-G)).toSignedMeasure)

theorem covariance_apply (F G : JointL2) {E : Set Space} (hE : MeasurableSet E) :
    covariance F G E = (1/4 : ℝ) *
      ((predictableMeasure (F+G) E).toReal - (predictableMeasure (F-G) E).toReal) := by
  simp only [covariance, smul_apply, sub_apply, Measure.toSignedMeasure_apply_measurable hE,
    smul_eq_mul, measureReal_def]

theorem covariance_ring (F G : JointL2) {E : Set Space} (hE : E ∈ elementaryRing) :
    covariance F G E = inner ℝ (ringIntegral F E) (ringIntegral G E) := by
  rw [covariance_apply F G (elementary_predictable hE),
    predictableMeasure_generator _ (Or.inl hE), predictableMeasure_generator _ (Or.inl hE),
    content_energy _ hE, content_energy _ hE,
    ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_ofReal (sq_nonneg _),
    ring_terminal_add, ring_terminal_sub, norm_add_sq_real, norm_sub_sq_real]
  ring

theorem covariance_ring_bound (F G : JointL2) {E : Set Space} (hE : E ∈ elementaryRing) :
    |covariance F G E| ≤ ‖ringIntegral F E‖ * ‖ringIntegral G E‖ := by
  rw [covariance_ring F G hE]
  exact abs_real_inner_le_norm _ _

end OperatorDerivativeRewrite.Foundation.IBMPredictableCovarianceMeasure
