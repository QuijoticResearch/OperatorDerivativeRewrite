import Foundation.IBMFullPredictableIntegral

/-! Lifting actual raw-past coefficients and their null sets to predictable energy. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMPredictableCoefficientLift
open IBMPredictableRectangles IBMPredictableLpDictionary IBMTimeAveragedObservable
open IBMJointPredictableEnergyMeasure IBMNaturalFiltrationObstruction
open IBMIntrinsicMartingaleStep (Coefficient)
set_option backward.isDefEq.respectTransparency false
local instance : MeasurableSpace Space := naturalFiltration.predictable
local instance (F : JointL2) : IsFiniteMeasure (predictableMeasure F) := finite_measure F

def lift (s t : ℝ≥0) (f : IBMSourceLaws.JointSample → ℝ) : Space → ℝ :=
  fun p => (Ioc s t).indicator (fun _ => f p.2) p.1

theorem coefficient_stronglyMeasurable (s t : ℝ≥0) (a : Coefficient s) :
    StronglyMeasurable (lift s t a.function) :=
  IBMIntrinsicPredictableProcess.timeStep_predictable s t a

theorem null_rectangle (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t)
    (A : Set IBMSourceLaws.JointSample) (hA : MeasurableSet[naturalFiltration s] A)
    (hnull : IBMSourceLaws.jointMeasure A = 0) : predictableMeasure F (rect s t A) = 0 := by
  rw [predictableMeasure_rectangle F s t A hst hA]
  exact withDensity_absolutelyContinuous _ _ hnull

theorem ae_lift (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t)
    (P : IBMSourceLaws.JointSample → Prop) (hP : MeasurableSet[naturalFiltration s] {ω | P ω})
    (h : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, P ω) :
    ∀ᵐ p ∂predictableMeasure F, p.1 ∈ Ioc s t → P p.2 := by
  have hn : IBMSourceLaws.jointMeasure ({ω | P ω}ᶜ) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    simpa only [mem_compl_iff, mem_setOf_eq, not_not] using h
  have hz := measure_eq_zero_iff_ae_notMem.mp (null_rectangle F hst _ hP.compl hn)
  filter_upwards [hz] with p hp hr
  by_contra hnot
  exact hp ⟨hr, hnot⟩

theorem coefficient_memLp (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t) (a : Coefficient s) :
    MemLp (lift s t a.function) 2 (predictableMeasure F) := by
  apply MemLp.of_bound (coefficient_stronglyMeasurable s t a).aestronglyMeasurable
    (max a.bound 0)
  have hB : MeasurableSet[naturalFiltration s] {ω | ‖a.function ω‖ ≤ a.bound} := by
    let : MeasurableSpace IBMSourceLaws.JointSample := naturalFiltration s
    exact measurableSet_le a.adapted.measurable.norm measurable_const
  have hb := ae_lift F hst (fun ω => ‖a.function ω‖ ≤ a.bound) hB a.bounded
  filter_upwards [hb] with p hp
  by_cases hr : p.1 ∈ Ioc s t
  · simpa only [lift, indicator_of_mem hr] using (hp hr).trans (le_max_left a.bound 0)
  · simp only [lift, indicator_of_notMem hr, norm_zero]
    exact le_max_right _ _

def coefficientLp (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t) (a : Coefficient s) : PredictableL2 F :=
  (coefficient_memLp F hst a).toLp _

theorem coefficientLp_ae (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t) (a : Coefficient s) :
    coefficientLp F hst a =ᵐ[predictableMeasure F] lift s t a.function :=
  (coefficient_memLp F hst a).coeFn_toLp

end OperatorDerivativeRewrite.Foundation.IBMPredictableCoefficientLift
