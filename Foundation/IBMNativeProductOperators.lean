import Foundation.IBMNativeFieldMultiplier

/-! Actual Leibniz equality in the native field Hilbert space and weak divergence. -/
noncomputable section
open MeasureTheory
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNativeProductOperators
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative IBMIntrinsicChainRule
open IBMIntrinsicChainEnergy IBMIntrinsicProductCalculus IBMNativeFieldMultiplier
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
set_option backward.isDefEq.respectTransparency false

theorem bounded_memLp (f : jointDerivative.domain) (C : ℝ)
    (hf : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((f : IntrinsicSpace) : JointL2) ω)| ≤ C) :
    MemLp (((f : IntrinsicSpace) : JointL2) : IBMSourceLaws.JointSample → ℝ)
      ∞ IBMSourceLaws.jointMeasure :=
  MemLp.of_bound (Lp.aestronglyMeasurable _) C (by simpa only [Real.norm_eq_abs] using hf)

theorem fields_eq (x y : JointL2)
    (hx : MemLp (x : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure)
    (hy : MemLp (y : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure)
    (U V W : JointFieldSpace)
    (h : ∀ i : Fin 2, coordinate i (W i) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => x ω • coordinate i (V i) ω+y ω • coordinate i (U i) ω) :
    W = multiply x hx V + multiply y hy U := by
  apply PiLp.ext
  intro i
  apply (coordinate i).injective
  apply Lp.ext
  exact (h i).trans (multiply_add_ae x y hx hy U V i).symm

theorem pairing_leibniz (x y : JointL2)
    (hx : MemLp (x : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure)
    (hy : MemLp (y : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure)
    (u U V W : JointFieldSpace) (hW : W = multiply x hx V + multiply y hy U) :
    inner ℝ u W = inner ℝ (multiply x hx u) V + inner ℝ (multiply y hy u) U := by
  calc
    inner ℝ u W = inner ℝ u (multiply x hx V + multiply y hy U) :=
      congrArg (fun z : JointFieldSpace => inner ℝ u z) hW
    _ = inner ℝ u (multiply x hx V) + inner ℝ u (multiply y hy U) := inner_add_right _ _ _
    _ = _ := congrArg₂ (fun a b : ℝ => a+b)
      (multiply_symmetric x hx u V).symm (multiply_symmetric y hy u U).symm

def LeibnizResult (f g : jointDerivative.domain) (C D : ℝ)
    (hf : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((f : IntrinsicSpace) : JointL2) ω)| ≤ C)
    (hg : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((g : IntrinsicSpace) : JointL2) ω)| ≤ D) : Prop :=
  ∃ F : jointDerivative.domain,
    (((F : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
      (((f : IntrinsicSpace) : JointL2) ω)*(((g : IntrinsicSpace) : JointL2) ω)) ∧
    jointDerivative F =
      multiply ((f : IntrinsicSpace) : JointL2) (bounded_memLp f C hf) (jointDerivative g) +
      multiply ((g : IntrinsicSpace) : JointL2) (bounded_memLp g D hg) (jointDerivative f)

theorem bounded_leibniz (f g : jointDerivative.domain) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((f : IntrinsicSpace) : JointL2) ω)| ≤ C)
    (hg : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((g : IntrinsicSpace) : JointL2) ω)| ≤ D) :
    LeibnizResult f g C D hf hg := by
  obtain ⟨F,hF,hc,hs⟩ := bounded_product f g C D hC hD hf hg
  refine ⟨F,hF,fields_eq _ _ (bounded_memLp f C hf) (bounded_memLp g D hg)
    (jointDerivative f) (jointDerivative g) (jointDerivative F) ?_⟩
  intro i
  fin_cases i
  · exact hs
  · exact hc

def WeakDivergenceResult (f g : jointDerivative.domain) (C D : ℝ)
    (hf : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((f : IntrinsicSpace) : JointL2) ω)| ≤ C)
    (hg : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((g : IntrinsicSpace) : JointL2) ω)| ≤ D)
    (u : jointDivergence.domain) : Prop :=
    ∃ F : jointDerivative.domain,
      (((F : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
        (((f : IntrinsicSpace) : JointL2) ω)*(((g : IntrinsicSpace) : JointL2) ω)) ∧
      inner ℝ (jointDivergence u) (F : IntrinsicSpace) =
        inner ℝ (multiply ((f : IntrinsicSpace) : JointL2) (bounded_memLp f C hf) u)
          (jointDerivative g) +
        inner ℝ (multiply ((g : IntrinsicSpace) : JointL2) (bounded_memLp g D hg) u)
          (jointDerivative f)

theorem weak_divergence (f g : jointDerivative.domain) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((f : IntrinsicSpace) : JointL2) ω)| ≤ C)
    (hg : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((g : IntrinsicSpace) : JointL2) ω)| ≤ D)
    (u : jointDivergence.domain) :
    WeakDivergenceResult f g C D hf hg u := by
  obtain ⟨F,hF,hD⟩ := bounded_leibniz f g C D hC hD hf hg
  refine ⟨F,hF,?_⟩
  exact (jointDerivative.adjoint_isFormalAdjoint jointDerivative_dense u F).trans
    (pairing_leibniz _ _ (bounded_memLp f C hf) (bounded_memLp g D hg)
      u (jointDerivative f) (jointDerivative g) (jointDerivative F) hD)

end OperatorDerivativeRewrite.Foundation.IBMNativeProductOperators
