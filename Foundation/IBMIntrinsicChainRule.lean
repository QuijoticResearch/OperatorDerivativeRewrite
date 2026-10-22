import Foundation.IBMJointIntrinsicDerivative

/-! Explicit bounded C1 chain calculus on the original full native IBM domain. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicChainRule
open InfiniteGaussian IBMTimeAveragedObservable IBMFiniteAverageCore
open IBMIntrinsicOperators IBMJointIntrinsicDerivative
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
set_option backward.isDefEq.respectTransparency false

abbrev JointVectorL2 := Lp CoefficientSpace 2 IBMSourceLaws.jointMeasure

def uncurryField (g : FieldSpace) : JointVectorL2 :=
  (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm g

theorem uncurryField_norm (g : FieldSpace) : ‖uncurryField g‖ = ‖g‖ :=
  (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm.norm_map g

theorem clock_partial_graph (f : jointDerivative.domain) :
    (clockUnitary ((f : IntrinsicSpace) : JointL2), jointDerivative f 1) ∈ partialDerivative.graph :=
  partialDerivative.mem_graph ⟨clockUnitary ((f : IntrinsicSpace) : JointL2), f.property.2⟩

theorem source_partial_graph (f : jointDerivative.domain) :
    (sourceUnitary ((f : IntrinsicSpace) : JointL2), jointDerivative f 0) ∈ partialDerivative.graph :=
  partialDerivative.mem_graph ⟨sourceUnitary ((f : IntrinsicSpace) : JointL2), f.property.1⟩

theorem clock_intrinsic_graph (F : IntrinsicSpace) (g : FieldSpace)
    (h : (clockUnitary (F : JointL2), g) ∈ partialDerivative.graph) :
    (F,g) ∈ intrinsicClock.graph :=
  (ObservableRestriction.derivative_graph clockDerivative IntrinsicSpace F g).mpr
    ((AdjointUnitaryTransport.mem_pullback_graph clockUnitary partialDerivative _ _).mpr h)

theorem source_intrinsic_graph (F : IntrinsicSpace) (g : FieldSpace)
    (h : (sourceUnitary (F : JointL2), g) ∈ partialDerivative.graph) :
    (F,g) ∈ intrinsicSource.graph :=
  (ObservableRestriction.derivative_graph sourceDerivative IntrinsicSpace F g).mpr
    ((AdjointUnitaryTransport.mem_pullback_graph sourceUnitary partialDerivative _ _).mpr h)

theorem clock_product_graph (f : jointDerivative.domain) :
    (ProductL2Curry.curry gaussianProduct gaussianProduct ((f : IntrinsicSpace) : JointL2),
      ProductL2Curry.curry gaussianProduct gaussianProduct (uncurryField (jointDerivative f 1)))
        ∈ partialDerivative.graph := by
  change (clockUnitary ((f : IntrinsicSpace) : JointL2),
    (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct)
      ((ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm (jointDerivative f 1))) ∈ _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact clock_partial_graph f

theorem source_product_graph (f : jointDerivative.domain) :
    (ProductL2Curry.curry gaussianProduct gaussianProduct
      (ProductL2Curry.swap gaussianProduct gaussianProduct ((f : IntrinsicSpace) : JointL2)),
      ProductL2Curry.curry gaussianProduct gaussianProduct (uncurryField (jointDerivative f 0)))
        ∈ partialDerivative.graph := by
  change (sourceUnitary ((f : IntrinsicSpace) : JointL2),
    (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct)
      ((ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm (jointDerivative f 0))) ∈ _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact source_partial_graph f

theorem swap_composition_eq (x F Fs : JointL2) (φ : ℝ → ℝ)
    (hF : F =ᵐ[IBMSourceLaws.jointMeasure] fun ω => φ (x ω))
    (hFs : Fs =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
      φ (ProductL2Curry.swap gaussianProduct gaussianProduct x ω)) :
    ProductL2Curry.swap gaussianProduct gaussianProduct F = Fs := by
  apply Lp.ext
  have hs := (measurePreserving_swap (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp hF
  filter_upwards [ProductL2Curry.swap_coeFn gaussianProduct gaussianProduct F,
    ProductL2Curry.swap_coeFn gaussianProduct gaussianProduct x, hs, hFs]
    with ω h1 h2 h3 h4
  rw [h1,h4,h2]
  exact h3

theorem composition_observable (x : IntrinsicSpace) (F : JointL2) (φ : ℝ → ℝ)
    (hc : Continuous φ)
    (hF : F =ᵐ[IBMSourceLaws.jointMeasure] fun ω => φ ((x : JointL2) ω)) :
    F ∈ IntrinsicSpace :=
  (hc.comp_aestronglyMeasurable (show AEStronglyMeasurable[
    IBMConditionalObservable.observableSigma IBMConstructedSources.sceneryPath
      IBMConstructedSources.clockPath] (x : JointL2) IBMSourceLaws.jointMeasure from
        x.property)).congr hF.symm

theorem assemble_graph (F : JointL2) (hobs : F ∈ IntrinsicSpace) (Gs Gc : JointVectorL2)
    (hs : (ProductL2Curry.curry gaussianProduct gaussianProduct
      (ProductL2Curry.swap gaussianProduct gaussianProduct F),
      ProductL2Curry.curry gaussianProduct gaussianProduct Gs) ∈ partialDerivative.graph)
    (hc : (ProductL2Curry.curry gaussianProduct gaussianProduct F,
      ProductL2Curry.curry gaussianProduct gaussianProduct Gc) ∈ partialDerivative.graph) :
    ((⟨F,hobs⟩ : IntrinsicSpace), pairField
      (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct Gs)
      (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct Gc)) ∈ jointDerivative.graph :=
  (joint_graph_iff ⟨F,hobs⟩ _).mpr
    ⟨source_intrinsic_graph ⟨F,hobs⟩ _ hs, clock_intrinsic_graph ⟨F,hobs⟩ _ hc⟩

theorem bounded_native_graph (x : IntrinsicSpace) (gs gc : FieldSpace)
    (hcg : (ProductL2Curry.curry gaussianProduct gaussianProduct (x : JointL2),
      ProductL2Curry.curry gaussianProduct gaussianProduct (uncurryField gc)) ∈ partialDerivative.graph)
    (hsg : (ProductL2Curry.curry gaussianProduct gaussianProduct
      (ProductL2Curry.swap gaussianProduct gaussianProduct (x : JointL2)),
      ProductL2Curry.curry gaussianProduct gaussianProduct (uncurryField gs)) ∈ partialDerivative.graph)
    (φ dφ : ℝ → ℝ) (hd : ∀ z, HasDerivAt φ (dφ z) z) (hc : Continuous dφ)
    (A B : ℝ) (hA : ∀ z, ‖φ z‖ ≤ A) (hB : ∀ z, ‖dφ z‖ ≤ B) :
    ∃ F : IntrinsicSpace, ∃ Gs Gc : JointVectorL2,
      (F, pairField (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct Gs)
        (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct Gc)) ∈ jointDerivative.graph ∧
      (F : JointL2) =ᵐ[IBMSourceLaws.jointMeasure] (fun ω => φ ((x : JointL2) ω)) ∧
      Gc =ᵐ[IBMSourceLaws.jointMeasure] (fun ω => dφ ((x : JointL2) ω) • uncurryField gc ω) ∧
      Gs =ᵐ[IBMSourceLaws.jointMeasure] (fun ω =>
        dφ (ProductL2Curry.swap gaussianProduct gaussianProduct (x : JointL2) ω) • uncurryField gs ω) := by
  obtain ⟨F,Gc,hFc,hF,hGc⟩ := GaussianClosedChainRule.bounded_product_chain_graph
    (x : JointL2) (uncurryField gc) hcg φ dφ hd hc A B hA hB
  obtain ⟨Fs,Gs,hFs,hFsae,hGs⟩ := GaussianClosedChainRule.bounded_product_chain_graph
    (ProductL2Curry.swap gaussianProduct gaussianProduct (x : JointL2))
    (uncurryField gs) hsg φ dφ hd hc A B hA hB
  have he := swap_composition_eq (x : JointL2) F Fs φ hF hFsae
  have hφ : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  have hobs := composition_observable x F φ hφ hF
  let Fi : IntrinsicSpace := ⟨F,hobs⟩
  have hsource : (ProductL2Curry.curry gaussianProduct gaussianProduct
      (ProductL2Curry.swap gaussianProduct gaussianProduct F),
      ProductL2Curry.curry gaussianProduct gaussianProduct Gs) ∈ partialDerivative.graph := by
    exact (congrArg (fun y : JointL2 =>
      (ProductL2Curry.curry gaussianProduct gaussianProduct y,
        ProductL2Curry.curry gaussianProduct gaussianProduct Gs) ∈ partialDerivative.graph) he).mpr hFs
  have hg := assemble_graph F hobs Gs Gc hsource hFc
  exact ⟨Fi,Gs,Gc,hg,hF,hGc,hGs⟩

theorem bounded_chain (f : jointDerivative.domain)
    (φ dφ : ℝ → ℝ) (hd : ∀ x, HasDerivAt φ (dφ x) x) (hc : Continuous dφ)
    (A B : ℝ) (hA : ∀ x, ‖φ x‖ ≤ A) (hB : ∀ x, ‖dφ x‖ ≤ B) :
    ∃ F : jointDerivative.domain,
      ((F : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
        (fun ω => φ (((f : IntrinsicSpace) : JointL2) ω)) ∧
      uncurryField (jointDerivative F 1) =ᵐ[IBMSourceLaws.jointMeasure]
        (fun ω => dφ (((f : IntrinsicSpace) : JointL2) ω) •
          uncurryField (jointDerivative f 1) ω) ∧
      uncurryField (jointDerivative F 0) =ᵐ[IBMSourceLaws.jointMeasure]
        (fun ω => dφ (ProductL2Curry.swap gaussianProduct gaussianProduct
          ((f : IntrinsicSpace) : JointL2) ω) • uncurryField (jointDerivative f 0) ω) := by
  obtain ⟨Fi,Gs,Gc,hg,hF,hGc,hGs⟩ := bounded_native_graph (f : IntrinsicSpace)
    (jointDerivative f 0) (jointDerivative f 1) (clock_product_graph f) (source_product_graph f)
    φ dφ hd hc A B hA hB
  have hm := LinearPMap.mem_domain_of_mem_graph hg
  let Fe : jointDerivative.domain := ⟨Fi,hm⟩
  have hdF : jointDerivative Fe = pairField
      (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct Gs)
      (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct Gc) :=
    ((jointDerivative.image_iff hm).mpr hg).symm
  refine ⟨Fe,hF,?_,?_⟩
  · have hu : uncurryField (jointDerivative Fe 1) = Gc := by
      rw [hdF]
      exact (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm_apply_apply Gc
    rw [hu]
    exact hGc
  · have hu : uncurryField (jointDerivative Fe 0) = Gs := by
      rw [hdF]
      exact (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm_apply_apply Gs
    rw [hu]
    exact hGs

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicChainRule
