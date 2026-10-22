import Foundation.IBMNativeContractionDomain

/-! Strong native IBM divergence with only the actual total-contraction L2 condition. -/
noncomputable section
open MeasureTheory
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNativeIntegrableDivergence
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative IBMNativeFieldMultiplier
open IBMNativeProductOperators IBMNativeWeightedDivergence IBMNativeContractionDomain
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
set_option backward.isDefEq.respectTransparency false

def output (f : jointDerivative.domain)
    (hf : MemLp (((f : IntrinsicSpace) : JointL2) : IBMSourceLaws.JointSample → ℝ)
      ∞ IBMSourceLaws.jointMeasure) (u : jointDivergence.domain)
    (h : MemLp (pairingFunction (jointDerivative f) u) 2 IBMSourceLaws.jointMeasure) :
    IntrinsicSpace :=
  IntrinsicSpace.orthogonalProjectionOnto
    (boundedMultiplier ((f : IntrinsicSpace) : JointL2) hf
      ((jointDivergence u : IntrinsicSpace) : JointL2) - correction (jointDerivative f) u h)

theorem bounded_pairing (f g : jointDerivative.domain) (C D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((f : IntrinsicSpace) : JointL2) ω)| ≤ C)
    (hg : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((g : IntrinsicSpace) : JointL2) ω)| ≤ D)
    (u : jointDivergence.domain)
    (h : MemLp (pairingFunction (jointDerivative f) u) 2 IBMSourceLaws.jointMeasure) :
    PairingResult (output f (bounded_memLp f C hf) u h)
      (multiply ((f : IntrinsicSpace) : JointL2) (bounded_memLp f C hf) u) g := by
  obtain ⟨F,hF,hi⟩ := weak_divergence f g C D hC hD hf hg u
  have hp := product_pairing ((f : IntrinsicSpace) : JointL2) ((g : IntrinsicSpace) : JointL2)
    ((F : IntrinsicSpace) : JointL2) ((jointDivergence u : IntrinsicSpace) : JointL2)
    (bounded_memLp f C hf) hF
  have hc := correction_pairing (jointDerivative f) u h
    ((g : IntrinsicSpace) : JointL2) (bounded_memLp g D hg)
  exact projected_sub_pairing _ _ (g : IntrinsicSpace) _ _ (hp.symm.trans hi) hc

theorem full_pairing (f : jointDerivative.domain) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((f : IntrinsicSpace) : JointL2) ω)| ≤ C)
    (u : jointDivergence.domain)
    (h : MemLp (pairingFunction (jointDerivative f) u) 2 IBMSourceLaws.jointMeasure)
    (g : jointDerivative.domain) :
    PairingResult (output f (bounded_memLp f C hf) u h)
      (multiply ((f : IntrinsicSpace) : JointL2) (bounded_memLp f C hf) u) g :=
  extend_pairing _ _ (fun g D hD hg => bounded_pairing f g C D hC hD hf hg u h) g

theorem weighted_mem (f : jointDerivative.domain) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((f : IntrinsicSpace) : JointL2) ω)| ≤ C)
    (u : jointDivergence.domain)
    (h : MemLp (pairingFunction (jointDerivative f) u) 2 IBMSourceLaws.jointMeasure) :
    multiply ((f : IntrinsicSpace) : JointL2) (bounded_memLp f C hf) u ∈ jointDivergence.domain :=
  jointDerivative.mem_adjoint_domain_of_exists _
    ⟨output f (bounded_memLp f C hf) u h,full_pairing f C hC hf u h⟩

theorem weighted_value (f : jointDerivative.domain) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((f : IntrinsicSpace) : JointL2) ω)| ≤ C)
    (u : jointDivergence.domain)
    (h : MemLp (pairingFunction (jointDerivative f) u) 2 IBMSourceLaws.jointMeasure) :
    jointDivergence ⟨multiply ((f : IntrinsicSpace) : JointL2) (bounded_memLp f C hf) u,
      weighted_mem f C hC hf u h⟩ = output f (bounded_memLp f C hf) u h :=
  jointDerivative.adjoint_apply_eq jointDerivative_dense _ (full_pairing f C hC hf u h)

end OperatorDerivativeRewrite.Foundation.IBMNativeIntegrableDivergence
