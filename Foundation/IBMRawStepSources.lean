import Foundation.IBMRawIntrinsicIntegral
import Foundation.IBMSourceProductBounds
import Foundation.IBMSineSourceField

/-! Actual clock-varying Gaussian rank fields for random raw-IBM steps.
The raw product and its SOURCE Wick compensation are constructed in genuine
Bochner L2, using existing quadratic Gaussian calculus. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRawStepSources
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators
open GaussianTimeProcess IBMQuarticSecondChaos IBMQuadraticSpatialCalculus
open IBMSourceProductBounds IBMClockAverageCandidate
open IBMSchwartzSourceContinuity IBMFiniteAverageCore
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
  FractionalSpectralKernel.spectralSpace_secondCountable
local instance : MeasurableSpace CoefficientSpace := borel CoefficientSpace
local instance : BorelSpace CoefficientSpace := ⟨rfl⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def clockDirection (t : ℝ≥0) (Y : SampleSpace) : CoefficientSpace :=
  IBMSineSourceField.direction |process t Y|

theorem direction_stronglyMeasurable (t : ℝ≥0) : StronglyMeasurable (clockDirection t) :=
  IBMSineSourceField.direction_continuous.stronglyMeasurable.comp_measurable
    (continuous_abs.measurable.comp (process_stronglyMeasurable t).measurable)

theorem direction_norm_sq (t : ℝ≥0) (Y : SampleSpace) :
    ‖clockDirection t Y‖ ^ 2 = |process t Y| := by
  change ‖IBMActualQuarticMoment.sceneryDirection |process t Y|‖ ^ 2 = _
  rw [IBMActualQuarticMoment.sceneryDirection_norm_sq, abs_abs]

private theorem pair_measurable (s t : ℝ≥0) :
    StronglyMeasurable (fun Y => (clockDirection t Y - clockDirection s Y, clockDirection s Y)) :=
  ((direction_stronglyMeasurable t).sub (direction_stronglyMeasurable s)).prodMk
    (direction_stronglyMeasurable s)

private theorem product_bound (s t : ℝ≥0) (Y : SampleSpace) :
    ‖clockDirection t Y - clockDirection s Y‖ * ‖clockDirection s Y‖ ≤
      2 * (|process s Y| + |process t Y|) := by
  have hm := mul_le_mul_of_nonneg_right
    (norm_sub_le (clockDirection t Y) (clockDirection s Y)) (norm_nonneg (clockDirection s Y))
  have hs := direction_norm_sq s Y
  have ht := direction_norm_sq t Y
  have hsq := sq_nonneg (‖clockDirection t Y‖ - ‖clockDirection s Y‖)
  nlinarith [abs_nonneg (process s Y), abs_nonneg (process t Y)]

def rawSections (s t : ℝ≥0) (Y : SampleSpace) : GaussianL2 :=
  rawProduct (clockDirection t Y - clockDirection s Y) (clockDirection s Y)

def crossSections (s t : ℝ≥0) (Y : SampleSpace) : GaussianL2 :=
  cross (clockDirection t Y - clockDirection s Y) (clockDirection s Y)

def fieldSections (s t : ℝ≥0) (Y : SampleSpace) : GaussianVectorL2 :=
  scalarTensor (clockDirection t Y - clockDirection s Y) (firstChaosEmbedding (clockDirection s Y))

private theorem majorant_memLp (s t : ℝ≥0) :
    MemLp (fun Y => 6 * (|process s Y| + |process t Y|)) 2 gaussianProduct := by
  simpa only [Real.norm_eq_abs, Pi.add_apply] using
    (((process_memLp s 2 (by simp)).norm).add ((process_memLp t 2 (by simp)).norm)).const_mul 6

theorem raw_memLp (s t : ℝ≥0) : MemLp (rawSections s t) 2 gaussianProduct := by
  have hc : Continuous (fun p : CoefficientSpace × CoefficientSpace => rawProduct p.1 p.2) :=
    (rawBilinear.continuous.comp continuous_fst).clm_apply continuous_snd
  apply (majorant_memLp s t).mono' (hc.comp_stronglyMeasurable (pair_measurable s t)).aestronglyMeasurable
  apply ae_of_all
  intro Y
  exact (rawProduct_norm_le _ _).trans (by linarith [product_bound s t Y])

theorem cross_memLp (s t : ℝ≥0) : MemLp (crossSections s t) 2 gaussianProduct := by
  have hc : Continuous (fun p : CoefficientSpace × CoefficientSpace => cross p.1 p.2) :=
    (crossBilinear.continuous.comp continuous_fst).clm_apply continuous_snd
  apply (majorant_memLp s t).mono' (hc.comp_stronglyMeasurable (pair_measurable s t)).aestronglyMeasurable
  apply ae_of_all
  intro Y
  have hm := cross_norm_le (clockDirection t Y - clockDirection s Y) (clockDirection s Y)
  have hp := product_bound s t Y
  change ‖crossSections s t Y‖ ≤ _ at hm
  change ‖crossSections s t Y‖ ≤ _
  nlinarith [abs_nonneg (process s Y), abs_nonneg (process t Y)]

theorem field_memLp (s t : ℝ≥0) : MemLp (fieldSections s t) 2 gaussianProduct := by
  have hc : Continuous (fun p : CoefficientSpace × CoefficientSpace =>
      scalarTensor p.1 (firstChaosEmbedding p.2)) :=
    scalarTensor_joint_continuous.comp
      (continuous_fst.prodMk (firstChaosEmbedding.continuous.comp continuous_snd))
  apply (majorant_memLp s t).mono' (hc.comp_stronglyMeasurable (pair_measurable s t)).aestronglyMeasurable
  apply ae_of_all
  intro Y
  change ‖scalarTensor _ _‖ ≤ _
  rw [scalarTensor_norm, firstChaosEmbedding.norm_map, mul_comm]
  exact (product_bound s t Y).trans (by nlinarith [abs_nonneg (process s Y), abs_nonneg (process t Y)])

def rawSource (s t : ℝ≥0) : ValueSpace := (raw_memLp s t).toLp (rawSections s t)
def crossSource (s t : ℝ≥0) : ValueSpace := (cross_memLp s t).toLp (crossSections s t)
def field (s t : ℝ≥0) : FieldSpace := (field_memLp s t).toLp (fieldSections s t)

theorem fiber_divergence_graph (s t : ℝ≥0) :
    (field s t, crossSource s t) ∈ (BochnerClosedOperator.lift gaussianProduct hilbertDivergence).graph := by
  rw [BochnerClosedOperator.mem_lift_graph_iff]
  filter_upwards [(field_memLp s t).coeFn_toLp, (cross_memLp s t).coeFn_toLp] with Y hf hc
  change field s t Y = fieldSections s t Y at hf
  change crossSource s t Y = crossSections s t Y at hc
  rw [hf, hc]
  change (scalarTensor _ _, cross _ _) ∈ _
  rw [cross_eq_mixedTarget]
  exact GaussianQuadraticSourceHodge.mixed_divergence_graph _ _

theorem native_source_graph (s t : ℝ≥0) :
    (field s t, jointRealization (crossSource s t)) ∈ sourceDerivative.adjoint.graph := by
  have hg := LinearPMap.le_graph_of_le
    (BochnerLiftAdjointInclusion.lift_adjoint_le gaussianProduct
      closedCylindricalDerivative closedCylindricalDerivative_dense_domain)
    (fiber_divergence_graph s t)
  have hm := LinearPMap.mem_domain_of_mem_graph hg
  have hs : field s t ∈ sourceDerivative.adjoint.domain := by
    rw [source_adjoint_domain]
    exact hm
  apply sourceDerivative.adjoint.mem_graph_iff.mpr
  refine ⟨⟨_, hs⟩, rfl, ?_⟩
  rw [source_adjoint_apply _ hs hm]
  apply sourceUnitary.injective
  rw [LinearIsometryEquiv.apply_symm_apply, IBMRawIntegralSourceCalculus.source_curry]
  exact ((partialDerivative.adjoint.image_iff hm).mpr hg).symm

end OperatorDerivativeRewrite.Foundation.IBMRawStepSources
