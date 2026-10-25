import Foundation.IBMBoundedC2NativeReconstruction

/-! Actual nonlinear finite-ridge IBM observations and exact source sections.
Repeated times, zero coefficients and cancelling directions are allowed. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMFiniteRidgeObservation
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMRawStepSources
open IBMFirstChaosMixedStein
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
variable {ι : Type*} [Fintype ι] (a : ι → ℝ) (r : ι → ℝ≥0)

def value (p : IBMSourceLaws.JointSample) : ℝ :=
  ∑ i, a i*IBMConstructedSources.ibmValue (r i) p

def direction (Y : SampleSpace) : CoefficientSpace := ∑ i, a i • clockDirection (r i) Y

theorem value_measurable : Measurable (value a r) := by
  apply Finset.measurable_sum
  intro i hi
  exact (IBMNaturalFiltrationObstruction.point_stronglyMeasurable (r i)).measurable.const_mul (a i)

theorem firstChaos_sections : ∀ᵐ Y ∂gaussianProduct,
    firstChaosEmbedding (direction a r Y) =ᵐ[gaussianProduct] fun X => value a r (X,Y) := by
  filter_upwards [ae_all_iff.mpr (fun i => IBMUnmollifiedSourceDerivative.actual_section_ae (r i))]
    with Y hi
  have he : firstChaosEmbedding (direction a r Y) =
      ∑ i, a i • firstChaosEmbedding (clockDirection (r i) Y) := by simp [direction]
  rw [he]
  have hj (i : ι) : (fun X => IBMConstructedSources.ibmValue (r i) (X,Y)) =ᵐ[gaussianProduct]
      firstChaosEmbedding (clockDirection (r i) Y) := hi i
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun i => a i • firstChaosEmbedding (clockDirection (r i) Y)),
    ae_all_iff.mpr (fun i => Lp.coeFn_smul (a i) (firstChaosEmbedding (clockDirection (r i) Y))),
    ae_all_iff.mpr hj] with X hs hm hv
  rw [hs]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hm i,Pi.smul_apply,smul_eq_mul,hv i]

variable {φ : ℝ → ℝ} (hc : Continuous φ) {A : ℝ} (hA : ∀ x, ‖φ x‖ ≤ A)

def jointClass : JointL2 :=
  (MemLp.of_bound (hc.measurable.comp (value_measurable a r)).aestronglyMeasurable A
    (Eventually.of_forall fun p => hA (value a r p))).toLp _

theorem joint_actual : jointClass a r hc hA =ᵐ[IBMSourceLaws.jointMeasure]
    fun p => φ (value a r p) :=
  MemLp.coeFn_toLp _

theorem joint_observable : jointClass a r hc hA ∈ IntrinsicSpace := by
  change AEStronglyMeasurable[IBMConditionalObservable.observableSigma
    IBMConstructedSources.sceneryPath IBMConstructedSources.clockPath]
      (jointClass a r hc hA) IBMSourceLaws.jointMeasure
  have hm : Measurable[IBMConditionalObservable.observableSigma
      IBMConstructedSources.sceneryPath IBMConstructedSources.clockPath] (value a r) := by
    apply Finset.measurable_sum
    intro i hi
    exact (IBMObservableQuartic.observable_value_measurable _ _ (r i)).const_mul (a i)
  exact (hc.measurable.comp hm).aestronglyMeasurable.congr (joint_actual a r hc hA).symm

def observation : IntrinsicSpace := ⟨jointClass a r hc hA,joint_observable a r hc hA⟩

theorem source_sections : sourceUnitary (jointClass a r hc hA) =ᵐ[gaussianProduct]
    fun Y => testClass (direction a r Y) hc hA := by
  have hu := ProductL2Curry.curry_coeFn gaussianProduct gaussianProduct
    (ProductL2Curry.swap gaussianProduct gaussianProduct (jointClass a r hc hA))
  have hs := ae_ae_of_ae_prod (ProductL2Curry.swap_coeFn gaussianProduct gaussianProduct
    (jointClass a r hc hA))
  have hq := ae_ae_of_ae_prod (measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp
    (joint_actual a r hc hA))
  filter_upwards [hu,hs,hq,firstChaos_sections a r] with Y hu hs hq hv
  apply Lp.ext
  filter_upwards [hu,hs,hq,hv,testClass_coeFn (direction a r Y) hc hA]
    with X hu hs hq hv hp
  have hu' : sourceUnitary (jointClass a r hc hA) Y X = jointClass a r hc hA (X,Y) := hu.trans hs
  have hq' : jointClass a r hc hA (X,Y) = φ (value a r (X,Y)) := hq
  rw [hu',hq',hp,hv]

def clockMean : GaussianL2 :=
  (innerSL ℝ gaussianOne).compLpL 2 gaussianProduct (sourceUnitary (jointClass a r hc hA))

theorem clockMean_actual : clockMean a r hc hA =ᵐ[gaussianProduct] fun Y =>
    ∫ X, φ (firstChaosEmbedding (direction a r Y) X) ∂gaussianProduct := by
  filter_upwards [(innerSL ℝ gaussianOne).coeFn_compLpL (sourceUnitary (jointClass a r hc hA)),
    source_sections a r hc hA] with Y ha hs
  change clockMean a r hc hA Y = inner ℝ gaussianOne (sourceUnitary (jointClass a r hc hA) Y) at ha
  rw [ha,hs,gaussianOne_inner_eq_integral]
  exact integral_congr_ae (testClass_coeFn (direction a r Y) hc hA)

end OperatorDerivativeRewrite.Foundation.IBMFiniteRidgeObservation
