import Foundation.IBMRawIntegralSourceCalculus
import Foundation.IBMStochasticNativeDivergence
import Foundation.IBMNativeWeakL1Divergence

/-! The ACTUAL completed deterministic raw IBM integral as an original joint
intrinsic divergence. The integrand is the constructed source gradient with
zero clock channel. This does not impose joint differentiability on its value
or assert observed predictability of its field. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRawIntrinsicIntegral
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators
open IBMJointIntrinsicDerivative IBMRawDeterministicIntegral IBMRawIntegralSourceCalculus
local notation "rawIntegral" => IBMRawDeterministicIntegral.integral
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
attribute [local irreducible] sourceDerivative clockDerivative jointDerivative
  LinearPMap.adjoint LinearPMap.graph IBMRawDeterministicIntegral.integral
  IBMRawIntegralSourceCalculus.gradient
  IBMRawIntegralSourceCalculus.divergenceValue

def value (f : Domain) : IntrinsicSpace := ⟨rawIntegral f, integral_observable f⟩

def nativeField : Domain →L[ℝ] JointFieldSpace :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => FieldSpace)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => if i = 0 then gradient else 0)

theorem nativeField_eq (f : Domain) : nativeField f = pairField (gradient f) 0 := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [nativeField, pairField]

attribute [local irreducible] nativeField pairField

theorem native_norm (f : Domain) : ‖nativeField f‖ = ‖rawIntegral f‖ := by
  have hs : ‖nativeField f‖ ^ 2 = ‖gradient f‖ ^ 2 := by
    calc
      _ = ‖pairField (gradient f) 0‖ ^ 2 := congrArg (fun z => ‖z‖ ^ 2) (nativeField_eq f)
      _ = ‖gradient f‖ ^ 2 + ‖(0 : FieldSpace)‖ ^ 2 :=
        IBMStochasticNativeDivergence.pair_norm_sq _ _
      _ = _ := by simp
  exact ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs).trans (gradient_norm f)

theorem native_bound (f : Domain) : ‖nativeField f‖ ≤ bound * ‖f‖ := by
  rw [native_norm]
  exact integral_bound f

private theorem source_pair (a : sourceDerivative.adjoint.domain) :
    ∃ hm : pairField a 0 ∈ jointDivergence.domain,
      jointDivergence ⟨pairField a 0, hm⟩ =
        IntrinsicSpace.orthogonalProjectionOnto (sourceDerivative.adjoint a) := by
  let b : clockDerivative.adjoint.domain := ⟨(0 : FieldSpace), Submodule.zero_mem _⟩
  have h := ambient_pair_divergence a b
  rcases h with ⟨hm, hv⟩
  refine ⟨hm, hv.trans ?_⟩
  have hz : clockDerivative.adjoint b = 0 := map_zero _
  exact congrArg IntrinsicSpace.orthogonalProjectionOnto (by rw [hz, add_zero])

theorem reconstruction (f : Domain) :
    ∃ hm : nativeField f ∈ jointDivergence.domain,
      jointDivergence ⟨nativeField f, hm⟩ = value f := by
  have h := source_pair (divergenceValue f)
  rcases h with ⟨hm, hv⟩
  have he : pairField (divergenceValue f) 0 =
      nativeField f := by
    unfold divergenceValue
    exact (nativeField_eq f).symm
  have hp : nativeField f ∈ jointDivergence.domain := he ▸ hm
  have hv' : jointDivergence ⟨nativeField f, hp⟩ =
      IntrinsicSpace.orthogonalProjectionOnto
        (sourceDerivative.adjoint (divergenceValue f)) := by
    exact (congrArg jointDivergence (Subtype.ext he.symm)).trans hv
  refine ⟨hp, hv'.trans ?_⟩
  have ha : sourceDerivative.adjoint (divergenceValue f) = rawIntegral f := divergence_value f
  exact (congrArg IntrinsicSpace.orthogonalProjectionOnto ha).trans
    (IntrinsicSpace.orthogonalProjectionOnto_mem_subspace_eq_self (value f))

theorem native_mem (f : Domain) : nativeField f ∈ jointDivergence.domain :=
  (reconstruction f).choose

def nativeInput (f : Domain) : jointDivergence.domain := ⟨nativeField f, native_mem f⟩

theorem native_value (f : Domain) : jointDivergence (nativeInput f) = value f :=
  (reconstruction f).choose_spec

theorem actual_finite (a : ℝ≥0 →₀ ℝ) :
    ((jointDivergence (nativeInput (reference a)) : IntrinsicSpace) : JointL2)
      =ᵐ[IBMSourceLaws.jointMeasure]
        fun p => ∑ t ∈ a.support, a t * IBMConstructedSources.ibmValue t p := by
  rw [native_value]
  exact IBMRawDeterministicIntegral.actual_finite a

theorem actual_interval (s t : ℝ≥0) :
    ((jointDivergence (nativeInput (kernelVector t - kernelVector s)) : IntrinsicSpace) : JointL2)
      =ᵐ[IBMSourceLaws.jointMeasure]
        fun p => IBMConstructedSources.ibmValue t p - IBMConstructedSources.ibmValue s p := by
  rw [native_value]
  exact IBMRawDeterministicIntegral.actual_interval s t

theorem integration_by_parts (f : Domain) (F : jointDerivative.domain) :
    inner ℝ (value f) (F : IntrinsicSpace) = inner ℝ (nativeField f) (jointDerivative F) := by
  have h := jointDerivative.adjoint_isFormalAdjoint jointDerivative_dense (nativeInput f) F
  rw [native_value] at h
  exact h

theorem actual_integration_by_parts (f : Domain) (F : jointDerivative.domain) :
    (∫ p, rawIntegral f p * ((F : IntrinsicSpace) : JointL2) p ∂IBMSourceLaws.jointMeasure) =
      inner ℝ (nativeField f) (jointDerivative F) := by
  calc
    _ = inner ℝ (rawIntegral f) ((F : IntrinsicSpace) : JointL2) :=
      IBMNativeWeakL1Divergence.product_mean _ _
    _ = _ := integration_by_parts f F

/-- Analysis of the original derivative by the actual raw integral, not a
substitute observed-martingale or Gaussian inverse operator. -/
theorem native_adjoint (F : jointDerivative.domain) :
    nativeField.adjoint (jointDerivative F) =
      (rawIntegral).adjoint ((F : IntrinsicSpace) : JointL2) := by
  apply ext_inner_left ℝ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right]
  exact (integration_by_parts f F).symm

theorem native_inner (f g : Domain) :
    inner ℝ (nativeField f) (nativeField g) = inner ℝ (rawIntegral f) (rawIntegral g) := by
  rw [nativeField_eq, nativeField_eq]
  unfold pairField
  simp only [PiLp.inner_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, inner_zero_left, add_zero]
  exact gradient_inner f g

/-- Strong convergence in BOTH original joint-adjoint graph coordinates. -/
theorem graph_limit (a : ℕ → (ℝ≥0 →₀ ℝ)) (f : Domain)
    (ha : Tendsto (fun n => reference (a n)) atTop (𝓝 f)) :
    Tendsto (fun n => (nativeField (reference (a n)),
      ((jointDivergence (nativeInput (reference (a n))) : IntrinsicSpace) : JointL2)))
      atTop (𝓝 (nativeField f, rawIntegral f)) := by
  have h := (nativeField.continuous.prodMk (rawIntegral).continuous).continuousAt.tendsto.comp ha
  simpa only [Function.comp_def, native_value, value] using h

/-- A literal past-value coefficient on the physical interval (1,2]. -/
def rawLeftStep (p : IBMSourceLaws.JointSample) : ℝ :=
  IBMConstructedSources.ibmValue 1 p *
    (IBMConstructedSources.ibmValue 2 p - IBMConstructedSources.ibmValue 1 p)

private theorem rawLeftStep_rep :
    (fun p => IBMDeterministicRangeObstruction.observed 1 p *
      (IBMDeterministicRangeObstruction.observed 2 - IBMDeterministicRangeObstruction.observed 1) p)
      =ᵐ[IBMSourceLaws.jointMeasure] rawLeftStep := by
  filter_upwards [IBMDeterministicRangeObstruction.observed_ae 1,
    IBMDeterministicRangeObstruction.observed_ae 2,
    Lp.coeFn_sub (IBMDeterministicRangeObstruction.observed 2)
      (IBMDeterministicRangeObstruction.observed 1)] with p h1 h2 hd
  simp only [rawLeftStep, hd, Pi.sub_apply, h1, h2]

theorem rawLeftStep_integrable : Integrable rawLeftStep IBMSourceLaws.jointMeasure :=
  (IBMNativeWeakL1Divergence.product_integrable
    (IBMDeterministicRangeObstruction.observed 1)
    (IBMDeterministicRangeObstruction.observed 2 -
      IBMDeterministicRangeObstruction.observed 1)).congr
      rawLeftStep_rep

theorem rawLeftStep_mean_negative :
    (∫ p, rawLeftStep p ∂IBMSourceLaws.jointMeasure) < 0 := by
  have he : (∫ p, rawLeftStep p ∂IBMSourceLaws.jointMeasure) =
      inner ℝ (IBMDeterministicRangeObstruction.observed 1)
        (IBMDeterministicRangeObstruction.observed 2 -
          IBMDeterministicRangeObstruction.observed 1) :=
    (integral_congr_ae rawLeftStep_rep).symm.trans (IBMNativeWeakL1Divergence.product_mean _ _)
  exact he.trans_lt IBMTemporalCovarianceObstruction.actual_increment_pairing_negative

/-- No original joint-divergence input gives the uncorrected predictable raw
step. This is not an impossibility theorem for corrected random integration. -/
theorem no_rawLeftStep_divergence (u : jointDivergence.domain) :
    ¬ (((jointDivergence u : IntrinsicSpace) : JointL2)
      =ᵐ[IBMSourceLaws.jointMeasure] rawLeftStep) := by
  intro h
  have hz : (∫ p, rawLeftStep p ∂IBMSourceLaws.jointMeasure) = 0 :=
    (integral_congr_ae h).symm.trans (IBMCenteredSourceRepresentation.divergence_mean_zero u)
  exact (ne_of_lt rawLeftStep_mean_negative) hz

end OperatorDerivativeRewrite.Foundation.IBMRawIntrinsicIntegral
