import Foundation.IBMQuarticBochnerDomain
import Foundation.ProductL2Equivalence
import Foundation.IBMClockConditionalCorrection

/-! Native joint L2 realization. Coordinates in this module are ordered
(clock, source), matching the existing product/Bochner equivalence. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMQuarticJointRealization
open InfiniteGaussian IBMQuarticBochnerDomain IBMQuarticTimeProjection IBMQuarticClockMean
open GaussianNumberSectors
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

abbrev jointMeasure := gaussianProduct.prod gaussianProduct

def jointClass (n : ℕ) (T : ℝ≥0) : Lp ℝ 2 jointMeasure :=
  (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm (wholeClass n T)

theorem joint_sections (n : ℕ) (T : ℝ≥0) :
    ∀ᵐ ωY ∂gaussianProduct, wholeCorrection n T ωY =ᵐ[gaussianProduct]
      fun ωX => jointClass n T (ωY,ωX) := by
  have he := ProductL2Curry.curryEquiv_symm_coeFn gaussianProduct gaussianProduct (wholeClass n T)
  filter_upwards [he, wholeClass_coeFn n T] with ωY hy hw
  rwa [hw] at hy

/-- Transport the existing source-sector projection through the verified
onto product/Bochner isometry; no new chaos definition is introduced. -/
def jointSourceSector (k : ℕ) (F : Lp ℝ 2 jointMeasure) : Lp ℝ 2 jointMeasure :=
  (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm
    (((projection k).compLpL 2 gaussianProduct)
      (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct F))

def projectedJoint (n : ℕ) (T : ℝ≥0) : Lp ℝ 2 jointMeasure :=
  (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm
    (((projection 2).compLpL 2 gaussianProduct) (wholeClass n T))

theorem sourceSector_jointClass (n : ℕ) (T : ℝ≥0) :
    jointSourceSector 2 (jointClass n T) = projectedJoint n T := by
  simp only [jointSourceSector, jointClass, LinearIsometryEquiv.apply_symm_apply, projectedJoint]

theorem projected_sections (n : ℕ) (T : ℝ≥0) :
    ∀ᵐ ωY ∂gaussianProduct, projection 2 (wholeCorrection n T ωY) =ᵐ[gaussianProduct]
      fun ωX => projectedJoint n T (ωY,ωX) := by
  have he := ProductL2Curry.curryEquiv_symm_coeFn gaussianProduct gaussianProduct
    (((projection 2).compLpL 2 gaussianProduct) (wholeClass n T))
  have hp := (projection 2).coeFn_compLpL (wholeClass n T)
  filter_upwards [he, hp, wholeClass_coeFn n T] with ωY hy hp hw
  rw [hp, hw] at hy
  exact hy

theorem source_mean_ae (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    correctedMean n T =ᵐ[gaussianProduct]
      fun ωX => ∫ ωY, projectedJoint n T (ωY,ωX) ∂gaussianProduct := by
  have he := BochnerL2RepresentativeFubini.integral_coeFn_ae
    (fun ωY => projection 2 (wholeCorrection n T ωY)) (projected_whole_integrable n T hT)
    (fun p => projectedJoint n T p) (Lp.stronglyMeasurable _).aestronglyMeasurable
    (projected_sections n T)
  rwa [projected_whole_mean n T hT] at he

def sourceLift : GaussianL2 →ₗᵢ[ℝ] Lp ℝ 2 jointMeasure :=
  Lp.compMeasurePreservingₗᵢ ℝ (Prod.snd : SampleSpace × SampleSpace → SampleSpace)
    (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct))

theorem sourceLift_coeFn (f : GaussianL2) :
    sourceLift f =ᵐ[jointMeasure] fun p => f p.2 :=
  Lp.coeFn_compMeasurePreserving f _

theorem conditional_source_ae (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    jointMeasure[projectedJoint n T |
      MeasurableSpace.comap (Prod.snd : SampleSpace × SampleSpace → SampleSpace) inferInstance] =ᵐ[jointMeasure]
      fun p => correctedMean n T p.2 := by
  have hi : IndepFun (Prod.snd : SampleSpace × SampleSpace → SampleSpace) Prod.fst jointMeasure :=
    (indepFun_prod (μ := gaussianProduct) (ν := gaussianProduct) measurable_id measurable_id).symm
  have he := IndependentInnovationConditioning.conditional_integral jointMeasure
    (Prod.snd : SampleSpace × SampleSpace → SampleSpace) Prod.fst measurable_snd measurable_fst hi
    (fun p : SampleSpace × SampleSpace => projectedJoint n T (p.2,p.1))
    ((Lp.stronglyMeasurable (projectedJoint n T)).comp_measurable measurable_swap)
    ((Lp.memLp (projectedJoint n T)).integrable (by norm_num))
  have hm : jointMeasure.map (Prod.fst : SampleSpace × SampleSpace → SampleSpace) = gaussianProduct :=
    (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).map_eq
  have hmean := (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae
    (source_mean_ae n T hT).symm
  have hc : jointMeasure[projectedJoint n T |
      MeasurableSpace.comap (Prod.snd : SampleSpace × SampleSpace → SampleSpace) inferInstance] =ᵐ[jointMeasure]
      fun p => ∫ ωY, projectedJoint n T (ωY,p.2) ∂gaussianProduct := by
    simpa only [hm, Prod.mk.eta] using he
  exact hc.trans hmean

theorem sourceSigma_le :
    MeasurableSpace.comap (Prod.snd : SampleSpace × SampleSpace → SampleSpace) inferInstance ≤
      (inferInstance : MeasurableSpace (SampleSpace × SampleSpace)) := measurable_snd.comap_le

/-- Native joint L2 conditional projection of the source-2 component is
the actual source mean lifted back to the product probability space. -/
theorem native_block_eq (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    (condExpL2 ℝ ℝ sourceSigma_le (projectedJoint n T) : Lp ℝ 2 jointMeasure) =
      sourceLift (correctedMean n T) := by
  apply Lp.ext
  have he := (Lp.memLp (projectedJoint n T)).condExpL2_ae_eq_condExp (𝕜 := ℝ) sourceSigma_le
  have hh : (condExpL2 ℝ ℝ sourceSigma_le (projectedJoint n T) : Lp ℝ 2 jointMeasure) =ᵐ[jointMeasure]
      jointMeasure[projectedJoint n T |
        MeasurableSpace.comap (Prod.snd : SampleSpace × SampleSpace → SampleSpace) inferInstance] := by
    simpa only [Lp.toLp_coeFn] using he
  exact hh.trans ((conditional_source_ae n T hT).trans (sourceLift_coeFn _).symm)

theorem native_block_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => (condExpL2 ℝ ℝ sourceSigma_le (projectedJoint n T) : Lp ℝ 2 jointMeasure))
      atTop (𝓝 (sourceLift (IBMQuarticClockTerminal.terminalLimit T))) := by
  simp_rw [native_block_eq _ T hT]
  change Tendsto (sourceLift ∘ fun n => correctedMean n T) atTop _
  exact sourceLift.continuous.tendsto _ |>.comp (correctedMean_tendsto T hT)

end OperatorDerivativeRewrite.Foundation.IBMQuarticJointRealization
