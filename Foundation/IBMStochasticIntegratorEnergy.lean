import Foundation.IBMCompletedStochasticAssociativity
import Mathlib.MeasureTheory.Measure.WithDensityFinite

/-! The original predictable energy measure of an actual stochastic output
is the square-weighted original input energy measure. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMStochasticIntegratorEnergy
open IBMTimeAveragedObservable IBMPredictableRectangles IBMPredictableLpDictionary
open IBMJointPredictableEnergyMeasure IBMPredictableRectanglePullout
open IBMJointPredictableMultiplier IBMObservedTerminalMartingale
local instance : MeasurableSpace Space := IBMNaturalFiltrationObstruction.naturalFiltration.predictable
local instance (F : JointL2) : IsFiniteMeasure (predictableMeasure F) := finite_measure F
set_option backward.isDefEq.respectTransparency false

def weightedMeasure (F : JointL2) (H : PredictableL2 F) : Measure Space :=
  (predictableMeasure F).withDensity (fun p => ENNReal.ofReal (H p^2))

theorem weighted_finite (F : JointL2) (H : PredictableL2 F) : IsFiniteMeasure (weightedMeasure F H) :=
  isFiniteMeasure_withDensity_ofReal (Lp.memLp H).integrable_sq.2
local instance (F : JointL2) (H : PredictableL2 F) : IsFiniteMeasure (weightedMeasure F H) := weighted_finite F H

theorem weighted_apply (F : JointL2) (H : PredictableL2 F) {E : Set Space} (hE : MeasurableSet E) :
    weightedMeasure F H E = ENNReal.ofReal (∫ p in E, H p^2 ∂predictableMeasure F) := by
  rw [weightedMeasure,withDensity_apply _ hE]
  exact (ofReal_integral_eq_lintegral_ofReal (Lp.memLp H).integrable_sq.integrableOn
    (Eventually.of_forall fun p => sq_nonneg (H p))).symm

theorem weighted_origin (F : JointL2) (H : PredictableL2 F)
    (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration 0] A) :
    weightedMeasure F H (origin A)=0 :=
  (withDensity_absolutelyContinuous _ _) (predictableMeasure_origin F A hA)

theorem mask_energy (F : JointL2) (H : PredictableL2 F) (E : Set Space) (hE : MeasurableSet E) :
    ‖IBMFullPredictableIntegral.integral F
      (multiplier (IBMCompletedPredictableMultiplier.indicator E hE) F H)‖^2 =
      ∫ p in E, H p^2 ∂predictableMeasure F := by
  rw [← real_inner_self_eq_norm_sq,IBMFullPredictableIntegral.integral_inner,L2.inner_def,
    ← integral_indicator hE]
  apply integral_congr_ae
  filter_upwards [multiplier_ae (IBMCompletedPredictableMultiplier.indicator E hE) F H] with p hp
  rw [hp,Real.inner_apply]
  by_cases he : p ∈ E <;>
    simp [IBMCompletedPredictableMultiplier.indicator,Set.indicator,he,pow_two]

theorem stepOutput_energy (Y : JointL2) {s t : ℝ≥0} (hst : s ≤ t)
    (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration s] A) :
    ‖stepOutput s t A hA Y‖^2 =
      ∫ ω in A, (channel Y t ω-channel Y s ω)^2 ∂IBMSourceLaws.jointMeasure := by
  rw [stepOutput_eq_stepClass Y hst,IBMGermPredictableStep.step_energy Y hst,
    ← integral_indicator (IBMNaturalFiltrationObstruction.naturalFiltration.le s _ hA)]
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => by
    by_cases hω : ω ∈ A <;> simp [IBMWeightedTerminalEnergy.eventCoefficient,Set.indicator,hω]

theorem weighted_rectangle (F : JointL2) (H : PredictableL2 F) {s t : ℝ≥0} (hst : s ≤ t)
    (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration s] A) :
    predictableMeasure (IBMFullPredictableIntegral.integral F H) (rect s t A)=
      weightedMeasure F H (rect s t A) := by
  rw [predictableMeasure_rectangle _ s t A hst hA,
    IBMWeightedTerminalEnergy.incrementMeasure_apply _ s t
      (IBMNaturalFiltrationObstruction.naturalFiltration.le s _ hA),
    weighted_apply F H (rect_predictable s t A hA)]
  apply congrArg ENNReal.ofReal
  calc
    _ = ‖stepOutput s t A hA (IBMFullPredictableIntegral.integral F H)‖^2 :=
      (stepOutput_energy _ hst A hA).symm
    _ = ‖IBMFullPredictableIntegral.integral F (multiplier (rectangleMultiplier s t A hA) F H)‖^2 := by
      rw [rectangle_integral F hst]
    _ = _ := mask_energy F H (rect s t A) (rect_predictable s t A hA)

theorem ring_measure_agreement (μ ν : Measure Space)
    (hrect : ∀ R ∈ rectangles, μ R=ν R) {E : Set Space} (hE : E ∈ elementaryRing) : μ E=ν E := by
  classical
  obtain ⟨P,hP⟩ := rectangle_semiring.mem_supClosure_iff.mp hE
  have hc : ⋃₀ (P.parts : Set (Set Space))=E := by
    simpa only [Finset.sup_id_set_eq_sUnion] using P.sup_parts
  have he : (⋃ R ∈ P.parts, R)=E := by simpa only [sUnion_eq_biUnion,Finset.mem_coe] using hc
  have hm : ∀ R ∈ P.parts, MeasurableSet R := fun R hR => elementary_predictable (subset_supClosure (hP hR))
  rw [← he]
  calc
    _ = ∑ R ∈ P.parts, μ R := by simpa only [id_eq] using (measure_biUnion_finset (μ := μ) P.disjoint hm)
    _ = ∑ R ∈ P.parts, ν R := Finset.sum_congr rfl fun R hR => hrect R (hP hR)
    _ = _ := by simpa only [id_eq] using (measure_biUnion_finset (μ := ν) P.disjoint hm).symm

theorem energy_change (F : JointL2) (H : PredictableL2 F) :
    predictableMeasure (IBMFullPredictableIntegral.integral F H) = weightedMeasure F H := by
  apply Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp
  apply IBMCovarianceCauchySchwarz.signed_ext
  intro E hE
  rcases hE with hE | ⟨A,hA,rfl⟩
  · rw [Measure.toSignedMeasure_apply_measurable (elementary_predictable hE),
      Measure.toSignedMeasure_apply_measurable (elementary_predictable hE)]
    apply congrArg ENNReal.toReal
    exact ring_measure_agreement _ _ (fun R hR => by
      obtain ⟨s,t,A,hst,hA,rfl⟩ := hR
      exact weighted_rectangle F H hst A hA) hE
  · change (predictableMeasure (IBMFullPredictableIntegral.integral F H)).toSignedMeasure (origin A) =
      (weightedMeasure F H).toSignedMeasure (origin A)
    rw [Measure.toSignedMeasure_apply_measurable (IBMCovarianceCauchySchwarz.origin_measurable hA),
      Measure.toSignedMeasure_apply_measurable (IBMCovarianceCauchySchwarz.origin_measurable hA)]
    simp only [measureReal_def,predictableMeasure_origin _ A hA,weighted_origin F H A hA]

end OperatorDerivativeRewrite.Foundation.IBMStochasticIntegratorEnergy
