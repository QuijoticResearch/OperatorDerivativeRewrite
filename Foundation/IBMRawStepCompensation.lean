import Foundation.IBMRawStepSources

/-! Actual random raw steps, source Wick compensation and the ORIGINAL
intrinsic divergence. The conditional clock correction is kept explicitly;
it is not replaced by a deterministic expectation. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRawStepCompensation
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators
open IBMJointIntrinsicDerivative IBMRawStepSources IBMSchwartzSourceContinuity IBMQuarticSecondChaos
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
  FractionalSpectralKernel.spectralSpace_secondCountable
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
attribute [local irreducible] IBMConstructedSources.ibmValue IBMConstructedSources.clockPath
  sourceDerivative clockDerivative jointDerivative LinearPMap.adjoint LinearPMap.graph

def rawFunction (s t : ℝ≥0) (p : IBMSourceLaws.JointSample) : ℝ :=
  IBMConstructedSources.ibmValue s p *
    (IBMConstructedSources.ibmValue t p - IBMConstructedSources.ibmValue s p)

def clockFunction (s t : ℝ≥0) (p : IBMSourceLaws.JointSample) : ℝ :=
  min |IBMConstructedSources.clockPath p.2 s| |IBMConstructedSources.clockPath p.2 t| -
    |IBMConstructedSources.clockPath p.2 s|

private theorem point_measurable (t : ℝ≥0) : Measurable (IBMConstructedSources.ibmValue t) :=
  IBMConstructedSources.ibmValue_jointly_measurable.comp (measurable_const.prodMk measurable_id)

private theorem clock_measurable (t : ℝ≥0) :
    Measurable (fun p : IBMSourceLaws.JointSample => IBMConstructedSources.clockPath p.2 t) :=
  ((ContinuousMap.measurable_eval t).comp IBMConstructedSources.clockPath_measurable).comp measurable_snd

private theorem raw_measurable (s t : ℝ≥0) : Measurable (rawFunction s t) :=
  (point_measurable s).mul ((point_measurable t).sub (point_measurable s))

private theorem clock_measurable_pair (s t : ℝ≥0) : Measurable (clockFunction s t) :=
  ((continuous_abs.measurable.comp (clock_measurable s)).min
    (continuous_abs.measurable.comp (clock_measurable t))).sub
      (continuous_abs.measurable.comp (clock_measurable s))

theorem direction_correction (s t : ℝ≥0) (Y : SampleSpace) :
    inner ℝ (clockDirection t Y - clockDirection s Y) (clockDirection s Y) =
      min |GaussianTimeProcess.process s Y| |GaussianTimeProcess.process t Y| -
        |GaussianTimeProcess.process s Y| := by
  have h := IBMRawTemporalKernel.source_inner
    (abs_nonneg (GaussianTimeProcess.process t Y)) (abs_nonneg (GaussianTimeProcess.process s Y))
  change inner ℝ (firstChaosEmbedding (clockDirection t Y))
    (firstChaosEmbedding (clockDirection s Y)) = _ at h
  rw [firstChaosEmbedding.inner_map_map] at h
  rw [inner_sub_left, real_inner_self_eq_norm_sq, direction_norm_sq, h, min_comm]

def rawStep (s t : ℝ≥0) : JointL2 := jointRealization (rawSource s t)
def compensatedStep (s t : ℝ≥0) : JointL2 := jointRealization (crossSource s t)
def clockCorrection (s t : ℝ≥0) : JointL2 := rawStep s t - compensatedStep s t

theorem field_actual_sections (s t : ℝ≥0) : ∀ᵐ Y ∂gaussianProduct,
    field s t Y =ᵐ[gaussianProduct] fun X => IBMConstructedSources.ibmValue s (X,Y) •
      (clockDirection t Y - clockDirection s Y) := by
  filter_upwards [(field_memLp s t).coeFn_toLp,
    IBMUnmollifiedSourceDerivative.actual_section_ae s] with Y hY hs
  change field s t Y = fieldSections s t Y at hY
  rw [hY]
  filter_upwards [scalarTensor_coeFn (clockDirection t Y - clockDirection s Y)
    (firstChaosEmbedding (clockDirection s Y)), hs] with X hf hs
  change IBMConstructedSources.ibmValue s (X,Y) = firstChaosEmbedding (clockDirection s Y) X at hs
  change scalarTensor _ _ X = _
  rw [hf, ← hs]

theorem raw_actual (s t : ℝ≥0) : rawStep s t =ᵐ[IBMSourceLaws.jointMeasure] rawFunction s t := by
  apply jointRealization_ae_of_sections _ _ (raw_measurable s t)
  filter_upwards [(raw_memLp s t).coeFn_toLp,
    IBMUnmollifiedSourceDerivative.actual_section_ae s,
    IBMUnmollifiedSourceDerivative.actual_section_ae t] with Y hY hs ht
  change rawSource s t Y = rawSections s t Y at hY
  rw [hY]
  filter_upwards [rawProduct_coeFn (clockDirection t Y - clockDirection s Y) (clockDirection s Y),
    Lp.coeFn_sub (firstChaosEmbedding (clockDirection t Y)) (firstChaosEmbedding (clockDirection s Y)),
    hs, ht] with X hr hd hs ht
  have he : firstChaosEmbedding (clockDirection t Y - clockDirection s Y) =
      firstChaosEmbedding (clockDirection t Y) - firstChaosEmbedding (clockDirection s Y) := map_sub _ _ _
  change IBMConstructedSources.ibmValue s (X,Y) = firstChaosEmbedding (clockDirection s Y) X at hs
  change IBMConstructedSources.ibmValue t (X,Y) = firstChaosEmbedding (clockDirection t Y) X at ht
  change rawProduct _ _ X = rawFunction s t (X,Y)
  rw [hr, he, hd, Pi.sub_apply]
  unfold rawFunction
  rw [← hs, ← ht]
  ring

theorem compensated_actual (s t : ℝ≥0) :
    compensatedStep s t =ᵐ[IBMSourceLaws.jointMeasure] fun p => rawFunction s t p - clockFunction s t p := by
  apply jointRealization_ae_of_sections _ _ ((raw_measurable s t).sub (clock_measurable_pair s t))
  filter_upwards [(cross_memLp s t).coeFn_toLp,
    IBMUnmollifiedSourceDerivative.actual_section_ae s,
    IBMUnmollifiedSourceDerivative.actual_section_ae t,
    IBMConstructedSources.clockPath_coordinate_ae s,
    IBMConstructedSources.clockPath_coordinate_ae t] with Y hY hs ht hcs hct
  change crossSource s t Y = crossSections s t Y at hY
  rw [hY]
  filter_upwards [cross_coeFn (clockDirection t Y - clockDirection s Y) (clockDirection s Y),
    Lp.coeFn_sub (firstChaosEmbedding (clockDirection t Y)) (firstChaosEmbedding (clockDirection s Y)),
    hs, ht] with X hr hd hs ht
  have he : firstChaosEmbedding (clockDirection t Y - clockDirection s Y) =
      firstChaosEmbedding (clockDirection t Y) - firstChaosEmbedding (clockDirection s Y) := map_sub _ _ _
  change IBMConstructedSources.ibmValue s (X,Y) = firstChaosEmbedding (clockDirection s Y) X at hs
  change IBMConstructedSources.ibmValue t (X,Y) = firstChaosEmbedding (clockDirection t Y) X at ht
  change cross _ _ X = _
  rw [hr, he, hd, Pi.sub_apply, direction_correction]
  unfold rawFunction clockFunction
  simp only [Pi.sub_apply]
  rw [← hs, ← ht, hcs, hct]
  ring

theorem correction_actual (s t : ℝ≥0) :
    clockCorrection s t =ᵐ[IBMSourceLaws.jointMeasure] clockFunction s t := by
  filter_upwards [Lp.coeFn_sub (rawStep s t) (compensatedStep s t),
    raw_actual s t, compensated_actual s t] with p hd hr hc
  change (rawStep s t - compensatedStep s t) p = _
  rw [hd, Pi.sub_apply, hr, hc]
  ring

theorem raw_actual_memLp (s t : ℝ≥0) : MemLp (rawFunction s t) 2 IBMSourceLaws.jointMeasure :=
  (Lp.memLp (rawStep s t)).ae_eq (raw_actual s t)

theorem raw_observable (s t : ℝ≥0) : rawStep s t ∈ IntrinsicSpace := by
  have hm (r : ℝ≥0) : Measurable[IBMConditionalObservable.observableSigma
      IBMConstructedSources.sceneryPath IBMConstructedSources.clockPath] (IBMConstructedSources.ibmValue r) := by
    unfold IBMConstructedSources.ibmValue
    exact (measurable_pi_apply r).comp (comap_measurable (fun p u =>
      IBMContinuousComposition.value IBMConstructedSources.sceneryPath IBMConstructedSources.clockPath u p))
  exact ⟨rawFunction s t, ((hm s).mul ((hm t).sub (hm s))).stronglyMeasurable, raw_actual s t⟩

def rawObservable (s t : ℝ≥0) : IntrinsicSpace := ⟨rawStep s t, raw_observable s t⟩
def sourceInput (s t : ℝ≥0) : sourceDerivative.adjoint.domain :=
  ⟨field s t, LinearPMap.mem_domain_of_mem_graph (native_source_graph s t)⟩

private theorem source_value (s t : ℝ≥0) :
    sourceDerivative.adjoint (sourceInput s t) = compensatedStep s t :=
  ((sourceDerivative.adjoint.image_iff _).mpr (native_source_graph s t)).symm

def nativeField (s t : ℝ≥0) : JointFieldSpace := pairField (field s t) 0

theorem reconstruction (s t : ℝ≥0) :
    ∃ hm : nativeField s t ∈ jointDivergence.domain,
      jointDivergence ⟨nativeField s t, hm⟩ = IntrinsicSpace.orthogonalProjectionOnto (compensatedStep s t) := by
  let b : clockDerivative.adjoint.domain := ⟨(0 : FieldSpace), Submodule.zero_mem _⟩
  have h := ambient_pair_divergence (sourceInput s t) b
  rcases h with ⟨hm, hv⟩
  refine ⟨hm, hv.trans ?_⟩
  have hz : clockDerivative.adjoint b = 0 := map_zero _
  exact congrArg IntrinsicSpace.orthogonalProjectionOnto (by rw [source_value, hz, add_zero])

def nativeInput (s t : ℝ≥0) : jointDivergence.domain :=
  ⟨nativeField s t, (reconstruction s t).choose⟩

theorem native_value (s t : ℝ≥0) :
    jointDivergence (nativeInput s t) = IntrinsicSpace.orthogonalProjectionOnto (compensatedStep s t) :=
  (reconstruction s t).choose_spec

/-- An actual L2 stochastic identity with the observable conditional clock correction. -/
theorem stochastic_identity (s t : ℝ≥0) :
    rawObservable s t = jointDivergence (nativeInput s t) +
      IntrinsicSpace.orthogonalProjectionOnto (clockCorrection s t) := by
  rw [native_value]
  have he : compensatedStep s t + clockCorrection s t = rawStep s t := by
    unfold clockCorrection
    abel
  have hp := congrArg IntrinsicSpace.orthogonalProjectionOnto he
  rw [map_add] at hp
  exact ((IntrinsicSpace.orthogonalProjectionOnto_mem_subspace_eq_self (rawObservable s t)).symm.trans hp.symm)

theorem corrected_duality (s t : ℝ≥0) (F : jointDerivative.domain) :
    inner ℝ (rawObservable s t) (F : IntrinsicSpace) =
      inner ℝ (nativeField s t) (jointDerivative F) +
        inner ℝ (clockCorrection s t) ((F : IntrinsicSpace) : JointL2) := by
  have hd := jointDerivative.adjoint_isFormalAdjoint jointDerivative_dense (nativeInput s t) F
  have hp := IntrinsicSpace.inner_orthogonalProjectionOnto_eq_of_mem_right
    (F : IntrinsicSpace) (clockCorrection s t)
  have h := congrArg (fun z : IntrinsicSpace => inner ℝ z (F : IntrinsicSpace))
    (stochastic_identity s t)
  rw [inner_add_left, hd, hp] at h
  exact h

theorem correction_nonpos (s t : ℝ≥0) :
    ∀ᵐ p ∂IBMSourceLaws.jointMeasure, clockCorrection s t p ≤ 0 := by
  filter_upwards [correction_actual s t] with p hp
  rw [hp]
  exact sub_nonpos.mpr (min_le_left _ _)

theorem projected_correction_ne_zero :
    IntrinsicSpace.orthogonalProjectionOnto (clockCorrection 1 2) ≠ 0 := by
  intro hz
  have hi := stochastic_identity 1 2
  rw [hz, add_zero] at hi
  apply IBMRawIntrinsicIntegral.no_rawLeftStep_divergence (nativeInput 1 2)
  rw [← hi]
  exact raw_actual 1 2

end OperatorDerivativeRewrite.Foundation.IBMRawStepCompensation
