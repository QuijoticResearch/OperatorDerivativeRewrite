import Foundation.IBMBoundedC2SecondProjection
import Foundation.IBMObservableQuartic

/-! Actual bounded continuous IBM observations and their source-section means.
The latter are genuine clock L2 classes, not formal conditional expectations. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMBoundedObservationSections
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMRawStepSources
open IBMFirstChaosMixedStein
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
variable {φ : ℝ → ℝ} (hc : Continuous φ) {A : ℝ} (hA : ∀ x, ‖φ x‖ ≤ A)

def jointClass (R : ℝ≥0) : JointL2 :=
  (MemLp.of_bound (hc.comp_stronglyMeasurable
    (IBMNaturalFiltrationObstruction.point_stronglyMeasurable R)).aestronglyMeasurable A
      (Eventually.of_forall fun p => hA (IBMConstructedSources.ibmValue R p))).toLp _

theorem joint_actual (R : ℝ≥0) : jointClass hc hA R =ᵐ[IBMSourceLaws.jointMeasure]
    fun p => φ (IBMConstructedSources.ibmValue R p) := MemLp.coeFn_toLp _

theorem joint_observable (R : ℝ≥0) : jointClass hc hA R ∈ IntrinsicSpace := by
  change AEStronglyMeasurable[IBMConditionalObservable.observableSigma
    IBMConstructedSources.sceneryPath IBMConstructedSources.clockPath]
      (jointClass hc hA R) IBMSourceLaws.jointMeasure
  have hm : Measurable[IBMConditionalObservable.observableSigma
      IBMConstructedSources.sceneryPath IBMConstructedSources.clockPath]
      (fun p => φ (IBMConstructedSources.ibmValue R p)) :=
    hc.measurable.comp (IBMObservableQuartic.observable_value_measurable _ _ R)
  exact hm.aestronglyMeasurable.congr (joint_actual hc hA R).symm

def observation (R : ℝ≥0) : IntrinsicSpace := ⟨jointClass hc hA R,joint_observable hc hA R⟩

theorem source_sections (R : ℝ≥0) : sourceUnitary (jointClass hc hA R) =ᵐ[gaussianProduct]
    fun Y => testClass (clockDirection R Y) hc hA := by
  have hu := ProductL2Curry.curry_coeFn gaussianProduct gaussianProduct
    (ProductL2Curry.swap gaussianProduct gaussianProduct (jointClass hc hA R))
  have hs := ae_ae_of_ae_prod (ProductL2Curry.swap_coeFn gaussianProduct gaussianProduct
    (jointClass hc hA R))
  have hq := ae_ae_of_ae_prod (measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp
    (joint_actual hc hA R))
  filter_upwards [hu,hs,hq,IBMConstructedSources.clockPath_coordinate_ae R] with Y hu hs hq hcR
  apply Lp.ext
  filter_upwards [hu,hs,hq,IBMActualQuarticMoment.scenery_firstChaos_ae
    |GaussianTimeProcess.process R Y|,testClass_coeFn (clockDirection R Y) hc hA]
      with X hu hs hq hf hp
  have hu' : sourceUnitary (jointClass hc hA R) Y X = jointClass hc hA R (X,Y) := hu.trans hs
  have hq' : jointClass hc hA R (X,Y) = φ (IBMConstructedSources.ibmValue R (X,Y)) := hq
  rw [hu',hq',IBMConstructedSources.ibmValue_eq,hcR,hf,hp]
  rfl

def clockMean (R : ℝ≥0) : GaussianL2 :=
  (innerSL ℝ gaussianOne).compLpL 2 gaussianProduct (sourceUnitary (jointClass hc hA R))

theorem clockMean_actual (R : ℝ≥0) : clockMean hc hA R =ᵐ[gaussianProduct] fun Y =>
    ∫ X, φ (firstChaosEmbedding (clockDirection R Y) X) ∂gaussianProduct := by
  filter_upwards [(innerSL ℝ gaussianOne).coeFn_compLpL (sourceUnitary (jointClass hc hA R)),
    source_sections hc hA R] with Y ha hs
  change clockMean hc hA R Y = inner ℝ gaussianOne (sourceUnitary (jointClass hc hA R) Y) at ha
  rw [ha,hs,gaussianOne_inner_eq_integral]
  exact integral_congr_ae (testClass_coeFn (clockDirection R Y) hc hA)

theorem clockMean_bound (R : ℝ≥0) : ∀ᵐ Y ∂gaussianProduct, ‖clockMean hc hA R Y‖ ≤ A := by
  filter_upwards [clockMean_actual hc hA R] with Y hY
  rw [hY]
  simpa using norm_integral_le_of_norm_le_const (μ := gaussianProduct)
    (Eventually.of_forall fun X => hA (firstChaosEmbedding (clockDirection R Y) X))

theorem sine_observation_eq (R : ℝ≥0) :
    observation Real.continuous_sin Real.abs_sin_le_one R =
      IBMActualSineDomainObstruction.sinePoint R := by
  apply Subtype.ext
  apply Lp.ext
  exact (joint_actual Real.continuous_sin Real.abs_sin_le_one R).trans
    (IBMActualSineDomainObstruction.sinePoint_actual_ae R).symm

theorem sine_not_joint_domain (R : ℝ≥0) (hR : 0 < R) :
    observation Real.continuous_sin Real.abs_sin_le_one R ∉
      IBMJointIntrinsicDerivative.jointDerivative.domain := by
  rw [sine_observation_eq]
  exact IBMActualSineDomainObstruction.sinePoint_not_joint_domain R hR

end OperatorDerivativeRewrite.Foundation.IBMBoundedObservationSections
