import Foundation.IBMNativeDirectionalDrift

/-! Actual unbounded-observable multiplication of deterministic native IBM directions. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNativeUnboundedDirections
open InfiniteGaussian (CoefficientSpace)
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative IBMIntrinsicChainRule
open IBMIntrinsicChainApproximation IBMIntrinsicUnboundedChain IBMNativeBoundedGraphCore
open IBMNativeProductOperators IBMNativeDeterministicFields IBMNativeDirectionalMaps
open IBMNativeDirectionalDrift
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
set_option backward.isDefEq.respectTransparency false

def nativeDrift (h k : CoefficientSpace) : JointL2 :=
  ((jointDivergence (directionElement h k) : IntrinsicSpace) : JointL2)

def boundedOutput (h k : CoefficientSpace) (f : jointDerivative.domain)
    (hf : MemLp (((f : IntrinsicSpace) : JointL2) : IBMSourceLaws.JointSample → ℝ)
      ∞ IBMSourceLaws.jointMeasure) : IntrinsicSpace :=
  IntrinsicSpace.orthogonalProjectionOnto
    (boundedMultiplier ((f : IntrinsicSpace) : JointL2) hf (nativeDrift h k) -
      contract h k (jointDerivative f))

theorem bounded_graph (h k : CoefficientSpace) (f : jointDerivative.domain)
    (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((f : IntrinsicSpace) : JointL2) ω)| ≤ C) :
    (lift h k ((f : IntrinsicSpace) : JointL2),boundedOutput h k f (bounded_memLp f C hf))
      ∈ jointDivergence.graph := by
  have hv := weighted_direction_value f C hC hf h k
  have ho : IBMNativeIntegrableDivergence.output f (bounded_memLp f C hf)
      (directionElement h k) (direction_correction_mem f h k) =
        boundedOutput h k f (bounded_memLp f C hf) :=
    congrArg IntrinsicSpace.orthogonalProjectionOnto
      (congrArg (fun q : JointL2 =>
        boundedMultiplier ((f : IntrinsicSpace) : JointL2) (bounded_memLp f C hf) (nativeDrift h k)-q)
        (correction_eq h k (jointDerivative f) (direction_correction_mem f h k)))
  exact jointDivergence.mem_graph_iff.mpr
    ⟨⟨_,weighted_direction_mem f C hC hf h k⟩,
      bounded_weight_eq h k _ (bounded_memLp f C hf),hv.trans ho⟩

def output (h k : CoefficientSpace) (f : jointDerivative.domain)
    (hp : MemLp (fun ω => (((f : IntrinsicSpace) : JointL2) ω)*nativeDrift h k ω)
      2 IBMSourceLaws.jointMeasure) : IntrinsicSpace :=
  IntrinsicSpace.orthogonalProjectionOnto
    (drift ((f : IntrinsicSpace) : JointL2) (nativeDrift h k) hp - contract h k (jointDerivative f))

theorem unbounded_graph (h k : CoefficientSpace) (f : jointDerivative.domain)
    (hp : MemLp (fun ω => (((f : IntrinsicSpace) : JointL2) ω)*nativeDrift h k ω)
      2 IBMSourceLaws.jointMeasure) :
    (lift h k ((f : IntrinsicSpace) : JointL2),output h k f hp) ∈ jointDivergence.graph := by
  obtain ⟨a,ha,hc,hs⟩ := bounded_approximants f (fun z => z) (fun _ => 1)
    (fun z => hasDerivAt_id z) continuous_const 1 (by intro; norm_num)
  let av : ℕ → JointL2 := fun n => ((a n : IntrinsicSpace) : JointL2)
  let A : ℕ → ℝ := fun n => (width n)⁻¹
  have hA (n : ℕ) : 0 ≤ A n := inv_nonneg.mpr (RealSteklovApprox.width_pos n).le
  have haClip (n : ℕ) : av n =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
      clip n (((f : IntrinsicSpace) : JointL2) ω) := ha n
  have hab (n : ℕ) : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(av n) ω| ≤ A n := by
    filter_upwards [haClip n] with ω hω
    rw [hω]
    exact Real.norm_eq_abs _ ▸ clip_bound n _
  let hb (n : ℕ) : MemLp (av n : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure :=
    bounded_memLp (a n) (A n) (hab n)
  have he (n : ℕ) : av n = clippedValue n ((f : IntrinsicSpace) : JointL2) :=
    Lp.ext ((haClip n).trans (clippedValue_ae n _).symm)
  have hv : Tendsto av atTop (𝓝 ((f : IntrinsicSpace) : JointL2)) :=
    (clippedValue_tendsto _).congr' (Eventually.of_forall fun n => (he n).symm)
  have hg : Tendsto (fun n => jointDerivative (a n)) atTop (𝓝 (jointDerivative f)) := by
    apply field_limit
    intro i
    fin_cases i
    · exact identity_gradient_limit
        (ProductL2Curry.swap InfiniteGaussian.gaussianProduct InfiniteGaussian.gaussianProduct
          ((f : IntrinsicSpace) : JointL2)) (jointDerivative f 0)
        (fun n => jointDerivative (a n) 0) hs
    · exact identity_gradient_limit ((f : IntrinsicSpace) : JointL2) (jointDerivative f 1)
        (fun n => jointDerivative (a n) 1) hc
  have hfield := (lift h k).continuous.continuousAt.tendsto.comp hv
  have hd := drift_limit ((f : IntrinsicSpace) : JointL2) (nativeDrift h k) hp av haClip hb
  have hcorr := (contract h k).continuous.continuousAt.tendsto.comp hg
  have hout := IntrinsicSpace.orthogonalProjectionOnto.continuous.continuousAt.tendsto.comp
    (hd.sub hcorr)
  exact (jointDerivative.adjoint_isClosed jointDerivative_dense).mem_of_tendsto
    (hfield.prodMk_nhds hout) (Eventually.of_forall fun n => bounded_graph h k (a n) (A n) (hA n) (hab n))

theorem unbounded_mem (h k : CoefficientSpace) (f : jointDerivative.domain)
    (hp : MemLp (fun ω => (((f : IntrinsicSpace) : JointL2) ω)*nativeDrift h k ω)
      2 IBMSourceLaws.jointMeasure) :
    lift h k ((f : IntrinsicSpace) : JointL2) ∈ jointDivergence.domain :=
  LinearPMap.mem_domain_of_mem_graph (unbounded_graph h k f hp)

theorem unbounded_value (h k : CoefficientSpace) (f : jointDerivative.domain)
    (hp : MemLp (fun ω => (((f : IntrinsicSpace) : JointL2) ω)*nativeDrift h k ω)
      2 IBMSourceLaws.jointMeasure) :
    jointDivergence ⟨lift h k ((f : IntrinsicSpace) : JointL2),unbounded_mem h k f hp⟩ =
      output h k f hp :=
  ((jointDivergence.image_iff (unbounded_mem h k f hp)).mpr (unbounded_graph h k f hp)).symm

end OperatorDerivativeRewrite.Foundation.IBMNativeUnboundedDirections
