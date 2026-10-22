import Foundation.IBMNativeContraction
import Foundation.IBMNativeBoundedGraphCore

/-! Strong multiplier-domain invariance for the actual native IBM divergence. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNativeWeightedDivergence
open InfiniteGaussian (CoefficientSpace)
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative IBMIntrinsicChainRule
open IBMNativeFieldMultiplier IBMNativeProductOperators IBMNativeContraction
open IBMNativeBoundedGraphCore
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
set_option backward.isDefEq.respectTransparency false

theorem product_pairing (f g F z : JointL2)
    (hf : MemLp (f : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure)
    (hF : F =ᵐ[IBMSourceLaws.jointMeasure] fun ω => f ω*g ω) :
    inner ℝ z F = inner ℝ (boundedMultiplier f hf z) g := by
  have he : F = boundedMultiplier f hf g := by
    apply Lp.ext
    have hm : boundedMultiplier f hf g =ᵐ[IBMSourceLaws.jointMeasure] fun ω => f ω*g ω := by
      simpa only [smul_eq_mul] using boundedMultiplier_coeFn f hf g
    exact hF.trans hm.symm
  exact (congrArg (fun w : JointL2 => inner ℝ z w) he).trans
    (boundedMultiplier_symmetric f hf z g).symm

theorem projection_pairing (v : JointL2) (g : IntrinsicSpace) :
    inner ℝ (IntrinsicSpace.orthogonalProjectionOnto v) g = inner ℝ v (g : JointL2) :=
  IntrinsicSpace.inner_orthogonalProjectionOnto_eq_of_mem_right g v

def output (f : jointDerivative.domain)
    (hf : MemLp (((f : IntrinsicSpace) : JointL2) : IBMSourceLaws.JointSample → ℝ)
      ∞ IBMSourceLaws.jointMeasure)
    (hDf : ∀ i : Fin 2, MemLp (coordinate i (jointDerivative f i) :
      IBMSourceLaws.JointSample → CoefficientSpace) ∞ IBMSourceLaws.jointMeasure)
    (u : jointDivergence.domain) : IntrinsicSpace :=
  IntrinsicSpace.orthogonalProjectionOnto
    (boundedMultiplier ((f : IntrinsicSpace) : JointL2) hf
      ((jointDivergence u : IntrinsicSpace) : JointL2) - correction (jointDerivative f) hDf u)

def PairingResult (R : IntrinsicSpace) (v : JointFieldSpace)
    (g : jointDerivative.domain) : Prop :=
  inner ℝ R (g : IntrinsicSpace) = inner ℝ v (jointDerivative g)

theorem projected_sub_pairing (s c : JointL2) (g : IntrinsicSpace) (A B : ℝ)
    (hs : inner ℝ s (g : JointL2) = A+B) (hc : inner ℝ c (g : JointL2) = B) :
    inner ℝ (IntrinsicSpace.orthogonalProjectionOnto (s-c)) g = A := by
  calc
    _ = inner ℝ s (g : JointL2) - inner ℝ c (g : JointL2) :=
      (projection_pairing (s-c) g).trans (inner_sub_left _ _ _)
    _ = A := by rw [hs,hc]; ring

theorem bounded_pairing (f g : jointDerivative.domain) (C D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((f : IntrinsicSpace) : JointL2) ω)| ≤ C)
    (hg : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((g : IntrinsicSpace) : JointL2) ω)| ≤ D)
    (hDf : ∀ i : Fin 2, MemLp (coordinate i (jointDerivative f i) :
      IBMSourceLaws.JointSample → CoefficientSpace) ∞ IBMSourceLaws.jointMeasure)
    (u : jointDivergence.domain) :
    PairingResult (output f (bounded_memLp f C hf) hDf u)
      (multiply ((f : IntrinsicSpace) : JointL2) (bounded_memLp f C hf) u) g := by
  obtain ⟨F,hF,hi⟩ := weak_divergence f g C D hC hD hf hg u
  have hp := product_pairing ((f : IntrinsicSpace) : JointL2) ((g : IntrinsicSpace) : JointL2)
    ((F : IntrinsicSpace) : JointL2) ((jointDivergence u : IntrinsicSpace) : JointL2)
    (bounded_memLp f C hf) hF
  have hc := correction_pairing (jointDerivative f) hDf u
    ((g : IntrinsicSpace) : JointL2) (bounded_memLp g D hg)
  exact projected_sub_pairing _ _ (g : IntrinsicSpace) _ _ (hp.symm.trans hi) hc

theorem extend_pairing (R : IntrinsicSpace) (w : JointFieldSpace)
    (h : ∀ g : jointDerivative.domain, ∀ C : ℝ, 0 ≤ C →
      (∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((g : IntrinsicSpace) : JointL2) ω)| ≤ C) →
      PairingResult R w g) (g : jointDerivative.domain) : PairingResult R w g := by
  obtain ⟨v,hv,h0,h1⟩ := bounded_graph g
  have he (n : ℕ) : inner ℝ R (v n : IntrinsicSpace) = inner ℝ w (jointDerivative (v n)) := by
    obtain ⟨C,hC,hc⟩ := hv n
    exact h (v n) C hC hc
  exact tendsto_nhds_unique
    ((tendsto_const_nhds.inner h0).congr' (Eventually.of_forall he))
    (tendsto_const_nhds.inner h1)

theorem full_pairing (f : jointDerivative.domain) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((f : IntrinsicSpace) : JointL2) ω)| ≤ C)
    (hDf : ∀ i : Fin 2, MemLp (coordinate i (jointDerivative f i) :
      IBMSourceLaws.JointSample → CoefficientSpace) ∞ IBMSourceLaws.jointMeasure)
    (u : jointDivergence.domain) (g : jointDerivative.domain) :
    PairingResult (output f (bounded_memLp f C hf) hDf u)
      (multiply ((f : IntrinsicSpace) : JointL2) (bounded_memLp f C hf) u) g := by
  exact extend_pairing _ _ (fun g D hD hg => bounded_pairing f g C D hC hD hf hg hDf u) g

theorem weighted_mem (f : jointDerivative.domain) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((f : IntrinsicSpace) : JointL2) ω)| ≤ C)
    (hDf : ∀ i : Fin 2, MemLp (coordinate i (jointDerivative f i) :
      IBMSourceLaws.JointSample → CoefficientSpace) ∞ IBMSourceLaws.jointMeasure)
    (u : jointDivergence.domain) :
    multiply ((f : IntrinsicSpace) : JointL2) (bounded_memLp f C hf) u ∈ jointDivergence.domain :=
  jointDerivative.mem_adjoint_domain_of_exists _
    ⟨output f (bounded_memLp f C hf) hDf u,full_pairing f C hC hf hDf u⟩

theorem weighted_value (f : jointDerivative.domain) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((f : IntrinsicSpace) : JointL2) ω)| ≤ C)
    (hDf : ∀ i : Fin 2, MemLp (coordinate i (jointDerivative f i) :
      IBMSourceLaws.JointSample → CoefficientSpace) ∞ IBMSourceLaws.jointMeasure)
    (u : jointDivergence.domain) :
    jointDivergence ⟨multiply ((f : IntrinsicSpace) : JointL2) (bounded_memLp f C hf) u,
      weighted_mem f C hC hf hDf u⟩ = output f (bounded_memLp f C hf) hDf u :=
  jointDerivative.adjoint_apply_eq jointDerivative_dense _ (full_pairing f C hC hf hDf u)

end OperatorDerivativeRewrite.Foundation.IBMNativeWeightedDivergence
