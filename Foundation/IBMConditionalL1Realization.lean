import Foundation.IBMClockPoissonWeakCalculus
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! Actual conditional L1 densities represented in the ORIGINAL intrinsic adjoint. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMConditionalL1Realization
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative IBMObservableHorizonLimit
open IBMNativeWeakL1Divergence IBMNativeProductOperators
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
set_option backward.isDefEq.respectTransparency false

theorem observation_le : observationSigma ≤
    (inferInstance : MeasurableSpace IBMSourceLaws.JointSample) :=
  IBMConditionalObservable.observableSigma_le _ _
    IBMConstructedSources.sceneryPath_measurable IBMConstructedSources.clockPath_measurable

def conditional (q : IBMSourceLaws.JointSample → ℝ) : IBMSourceLaws.JointSample → ℝ :=
  IBMSourceLaws.jointMeasure[q | observationSigma]

def realization (q : IBMSourceLaws.JointSample → ℝ)
    (hq : MemLp (conditional q) 2 IBMSourceLaws.jointMeasure) : IntrinsicSpace :=
  ⟨hq.toLp _, stronglyMeasurable_condExp.aestronglyMeasurable.congr hq.coeFn_toLp.symm⟩

theorem realization_ae (q : IBMSourceLaws.JointSample → ℝ)
    (hq : MemLp (conditional q) 2 IBMSourceLaws.jointMeasure) :
    ((realization q hq : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure] conditional q :=
  hq.coeFn_toLp

theorem conditional_pairing (q : IBMSourceLaws.JointSample → ℝ)
    (hq : Integrable q IBMSourceLaws.jointMeasure) (v : IntrinsicSpace)
    (hv : MemLp ((v : JointL2) : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure) :
    (∫ ω, (v : JointL2) ω * q ω ∂IBMSourceLaws.jointMeasure) =
      ∫ ω, (v : JointL2) ω * conditional q ω ∂IBMSourceLaws.jointMeasure := by
  have hm : AEStronglyMeasurable[observationSigma] (v : JointL2) IBMSourceLaws.jointMeasure :=
    v.property
  have hi := bounded_times_integrable (v : JointL2) hv q hq
  have hp := condExp_mul_of_aestronglyMeasurable_left hm hi hq
  have he := integral_condExp (μ := IBMSourceLaws.jointMeasure) (m := observationSigma)
    (f := fun ω => (v : JointL2) ω * q ω) observation_le
  exact he.symm.trans (integral_congr_ae hp)

theorem realization_pairing (q : IBMSourceLaws.JointSample → ℝ)
    (hq : Integrable q IBMSourceLaws.jointMeasure)
    (h2 : MemLp (conditional q) 2 IBMSourceLaws.jointMeasure) (v : IntrinsicSpace)
    (hv : MemLp ((v : JointL2) : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure) :
    inner ℝ (realization q h2) v =
      ∫ ω, (v : JointL2) ω * q ω ∂IBMSourceLaws.jointMeasure := by
  have hr := integral_congr_ae ((realization_ae q h2).mono fun ω hω =>
    congrArg (fun z : ℝ => (v : JointL2) ω * z) hω)
  have he : inner ℝ (realization q h2) v =
      ∫ ω, (v : JointL2) ω * (realization q h2 : JointL2) ω ∂IBMSourceLaws.jointMeasure :=
    (real_inner_comm _ _).trans (product_mean (v : JointL2) (realization q h2 : JointL2)).symm
  exact he.trans (hr.trans (conditional_pairing q hq v hv).symm)

def BoundedWeakPairing (U : JointFieldSpace) (q : IBMSourceLaws.JointSample → ℝ) : Prop :=
  ∀ v : jointDerivative.domain, ∀ C : ℝ, 0 ≤ C →
    (∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((v : IntrinsicSpace) : JointL2) ω)| ≤ C) →
    inner ℝ U (jointDerivative v) =
      ∫ ω, (((v : IntrinsicSpace) : JointL2) ω) * q ω ∂IBMSourceLaws.jointMeasure

theorem full_pairing (U : JointFieldSpace) (q : IBMSourceLaws.JointSample → ℝ)
    (hq : Integrable q IBMSourceLaws.jointMeasure)
    (h2 : MemLp (conditional q) 2 IBMSourceLaws.jointMeasure)
    (hU : BoundedWeakPairing U q) (v : jointDerivative.domain) :
    inner ℝ (realization q h2) (v : IntrinsicSpace) = inner ℝ U (jointDerivative v) :=
  IBMNativeWeightedDivergence.extend_pairing (realization q h2) U
    (fun v C hC hv => (realization_pairing q hq h2 (v : IntrinsicSpace)
      (bounded_memLp v C hv)).trans (hU v C hC hv).symm) v

theorem realization_graph (U : JointFieldSpace) (q : IBMSourceLaws.JointSample → ℝ)
    (hq : Integrable q IBMSourceLaws.jointMeasure)
    (h2 : MemLp (conditional q) 2 IBMSourceLaws.jointMeasure)
    (hU : BoundedWeakPairing U q) :
    (U,realization q h2) ∈ jointDivergence.graph := by
  have hm : U ∈ jointDivergence.domain :=
    jointDerivative.mem_adjoint_domain_of_exists U ⟨realization q h2,full_pairing U q hq h2 hU⟩
  have hv := jointDerivative.adjoint_apply_eq jointDerivative_dense ⟨U,hm⟩
    (full_pairing U q hq h2 hU)
  exact jointDivergence.mem_graph_iff.mpr ⟨⟨U,hm⟩,rfl,hv⟩

theorem conditional_memLp (q : JointL2) :
    MemLp (conditional q) 2 IBMSourceLaws.jointMeasure :=
  MemLp.condExp (by norm_num) (Lp.memLp q)

theorem realization_eq_projection (q : JointL2) :
    realization q (conditional_memLp q) = IntrinsicSpace.orthogonalProjectionOnto q := by
  have hp : (IntrinsicSpace.orthogonalProjectionOnto q : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
      conditional q := by
    simpa only [Lp.toLp_coeFn,condExpL2,conditional,IBMTimeAveragedObservable.IntrinsicSpace,
      IBMConditionalObservable.observableSpace,IBMObservableHorizonLimit.observationSigma] using
      (Lp.memLp q).condExpL2_ae_eq_condExp (E := ℝ) (𝕜 := ℝ) observation_le
  exact Subtype.ext (Lp.ext ((realization_ae q (conditional_memLp q)).trans hp.symm))

theorem realization_eq_self (q : IntrinsicSpace) :
    realization (q : JointL2) (conditional_memLp (q : JointL2)) = q :=
  (realization_eq_projection (q : JointL2)).trans
    (IntrinsicSpace.orthogonalProjectionOnto_mem_subspace_eq_self q)

end OperatorDerivativeRewrite.Foundation.IBMConditionalL1Realization
