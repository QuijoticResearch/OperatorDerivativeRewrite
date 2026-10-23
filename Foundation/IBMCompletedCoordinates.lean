import Foundation.IBMMultichannelCompletion
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! Predictable coordinate realization of every fixed-family completed IBM input. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology DirectSum
namespace OperatorDerivativeRewrite.Foundation.IBMCompletedCoordinates
open IBMTimeAveragedObservable IBMPredictableRectangles IBMPredictableLpDictionary
open IBMMultichannelCompletion IBMFixedStochasticFamily
attribute [local instance] componentAdd componentGroup componentModule componentZeroDec
local instance : DecidableEq basisSet := Classical.decEq _
local instance : MeasurableSpace Space := IBMNaturalFiltrationObstruction.naturalFiltration.predictable
local instance : MeasurableSpace basisSet := ⊤
local instance : Countable basisSet := basis_countable

def output (z : Completed fixedFamily) : IntrinsicSpace :=
  ⟨completedIntegral fixedFamily z, (completed_mem_remainder fixedFamily z).1⟩

theorem output_initial_zero (z : Completed fixedFamily) :
    IBMObservedTerminalMartingale.channelClass (output z : JointL2) 0 = 0 :=
  (Submodule.starProjection_apply_eq_zero_iff (IBMIntrinsicRightGerm.rightPast 0)).mpr
    (completed_mem_remainder fixedFamily z).2

def coordinates (z : Completed fixedFamily) (i : basisSet) : PredictableL2 (fixedFamily i) :=
  coefficient (output z) i • integrand i

theorem coordinates_actual_sum (z : Completed fixedFamily) :
    HasSum (fun i => IBMFullPredictableIntegral.integral (fixedFamily i) (coordinates z i))
      (completedIntegral fixedFamily z) := by
  have hs := stochastic_reconstruction (output z)
  rw [output_initial_zero, sub_zero] at hs
  exact hs

theorem coordinates_energy_tails (z : Completed fixedFamily) :
    ∀ ε > (0 : ℝ), ∃ s : Finset basisSet, ∀ t, Disjoint t s →
      finiteEnergy fixedFamily t (coordinates z) < ε^2 := by
  intro ε hε
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp (coordinates_actual_sum z).summable ε hε
  refine ⟨s, fun t ht => ?_⟩
  rw [finiteEnergy_actual]
  have hn := hs t ht
  nlinarith [norm_nonneg (∑ i ∈ t, IBMFullPredictableIntegral.integral (fixedFamily i) (coordinates z i))]

theorem coordinates_completed_sum (z : Completed fixedFamily) :
    HasSum (fun i => IBMMultichannelCompletion.embed fixedFamily
      (DirectSum.lof ℝ basisSet _ i (coordinates z i))) z := by
  obtain ⟨w, hw, hi⟩ := series_realization fixedFamily (coordinates z) (coordinates_energy_tails z)
  have he : w = z := (completedIntegral fixedFamily).injective (hi.unique (coordinates_actual_sum z))
  exact he ▸ hw

theorem remainder_output_norm (z : Completed fixedFamily) : ‖remainder (output z)‖ = ‖z‖ := by
  change ‖(output z : JointL2)-IBMObservedTerminalMartingale.channelClass (output z : JointL2) 0‖ = ‖z‖
  rw [output_initial_zero, sub_zero]
  exact (completedIntegral fixedFamily).norm_map z

theorem coordinates_norm_energy (z : Completed fixedFamily) :
    HasSum (fun i => ‖coordinates z i‖^2) (‖z‖^2) := by
  have he := stochastic_energy (output z)
  rw [remainder_output_norm] at he
  exact he

def coordinateField (z : Completed fixedFamily) (i : basisSet) : Space → ℝ :=
  (Lp.memLp (coordinates z i)).aestronglyMeasurable.mk (coordinates z i)

theorem coordinateField_measurable (z : Completed fixedFamily) (i : basisSet) :
    Measurable (coordinateField z i) :=
  (Lp.memLp (coordinates z i)).aestronglyMeasurable.stronglyMeasurable_mk.measurable

theorem coordinateField_ae (z : Completed fixedFamily) (i : basisSet) :
    coordinateField z i =ᵐ[IBMJointPredictableEnergyMeasure.predictableMeasure (fixedFamily i)] coordinates z i :=
  (Lp.memLp (coordinates z i)).aestronglyMeasurable.ae_eq_mk.symm

theorem coordinateField_memLp (z : Completed fixedFamily) (i : basisSet) :
    MemLp (coordinateField z i) 2 (IBMJointPredictableEnergyMeasure.predictableMeasure (fixedFamily i)) :=
  (Lp.memLp (coordinates z i)).ae_eq (coordinateField_ae z i).symm

def fieldClass (z : Completed fixedFamily) (i : basisSet) : PredictableL2 (fixedFamily i) :=
  (coordinateField_memLp z i).toLp (coordinateField z i)

theorem fieldClass_eq (z : Completed fixedFamily) (i : basisSet) : fieldClass z i = coordinates z i := by
  apply Lp.ext
  exact (coordinateField_memLp z i).coeFn_toLp.trans (coordinateField_ae z i)

theorem field_completed_sum (z : Completed fixedFamily) :
    HasSum (fun i => IBMMultichannelCompletion.embed fixedFamily
      (DirectSum.lof ℝ basisSet _ i (fieldClass z i))) z := by
  simpa only [fieldClass_eq] using coordinates_completed_sum z

theorem field_actual_sum (z : Completed fixedFamily) :
    HasSum (fun i => IBMFullPredictableIntegral.integral (fixedFamily i) (fieldClass z i))
      (completedIntegral fixedFamily z) := by
  simpa only [fieldClass_eq] using coordinates_actual_sum z

def jointField (z : Completed fixedFamily) (q : basisSet × Space) : ℝ :=
  coordinateField z q.1 q.2

theorem jointField_measurable (z : Completed fixedFamily) : Measurable (jointField z) :=
  measurable_from_prod_countable_right (coordinateField_measurable z)

theorem coordinateField_energy (z : Completed fixedFamily) :
    HasSum (fun i => ∫ p, (coordinateField z i p)^2
      ∂IBMJointPredictableEnergyMeasure.predictableMeasure (fixedFamily i)) (‖z‖^2) := by
  have he : ∀ i, (∫ p, (coordinateField z i p)^2
      ∂IBMJointPredictableEnergyMeasure.predictableMeasure (fixedFamily i)) = ‖coordinates z i‖^2 := by
    intro i
    have hp : (fun p => (coordinateField z i p)^2) =ᵐ[
        IBMJointPredictableEnergyMeasure.predictableMeasure (fixedFamily i)]
        (fun p => (coordinates z i p)^2) := by
      filter_upwards [coordinateField_ae z i] with p hp
      rw [hp]
    rw [integral_congr_ae hp]
    have hi := real_inner_self_eq_norm_sq (coordinates z i)
    rw [L2.inner_def] at hi
    simpa only [Real.inner_apply, pow_two] using hi
  simpa only [he] using coordinates_norm_energy z

end OperatorDerivativeRewrite.Foundation.IBMCompletedCoordinates
