import Foundation.IBMClockSteinIdentity

/-! Nonlinear closure of the original positive native operator delta D. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNativeGeneratorChain
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative IBMIntrinsicChainRule
open IBMIntrinsicChainEnergy IBMNativeFieldMultiplier IBMNativeContractionDomain
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
set_option backward.isDefEq.respectTransparency false

def energyDensity (f : jointDerivative.domain) : IBMSourceLaws.JointSample → ℝ :=
  pairingFunction (jointDerivative f) (jointDerivative f)

theorem energyDensity_eq (f : jointDerivative.domain) (ω : IBMSourceLaws.JointSample) :
    energyDensity f ω = ‖coordinate 0 (jointDerivative f 0) ω‖^2 +
      ‖coordinate 1 (jointDerivative f 1) ω‖^2 := by
  simp only [energyDensity,pairingFunction,real_inner_self_eq_norm_sq]

theorem energyDensity_integrable (f : jointDerivative.domain) :
    Integrable (energyDensity f) IBMSourceLaws.jointMeasure :=
  (L2.integrable_inner (coordinate 0 (jointDerivative f 0))
    (coordinate 0 (jointDerivative f 0))).add
    (L2.integrable_inner (coordinate 1 (jointDerivative f 1))
      (coordinate 1 (jointDerivative f 1)))

theorem energyDensity_integral (f : jointDerivative.domain) :
    (∫ ω, energyDensity f ω ∂IBMSourceLaws.jointMeasure) = ‖jointDerivative f‖^2 := by
  have h0 := L2.integrable_inner (𝕜 := ℝ) (coordinate 0 (jointDerivative f 0))
    (coordinate 0 (jointDerivative f 0))
  have h1 := L2.integrable_inner (𝕜 := ℝ) (coordinate 1 (jointDerivative f 1))
    (coordinate 1 (jointDerivative f 1))
  exact (integral_add h0 h1).trans
    ((congrArg₂ (fun x y : ℝ => x+y) (L2.inner_def _ _).symm (L2.inner_def _ _).symm).trans
      ((IBMObservableClockKernel.coordinate_inner (jointDerivative f) (jointDerivative f)).symm.trans
        (real_inner_self_eq_norm_sq _)))

theorem energyDensity_mem_of_four (f : jointDerivative.domain)
    (hf : ∀ i : Fin 2, MemLp (coordinate i (jointDerivative f i) :
      IBMSourceLaws.JointSample → InfiniteGaussian.CoefficientSpace) 4 IBMSourceLaws.jointMeasure) :
    MemLp (energyDensity f) 2 IBMSourceLaws.jointMeasure :=
  four_four_domain (jointDerivative f) (jointDerivative f) hf hf

theorem chain_coordinates (f F : jointDerivative.domain) (a : ℝ → ℝ)
    (hc : uncurryField (jointDerivative F 1) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => a (((f : IntrinsicSpace) : JointL2) ω) • uncurryField (jointDerivative f 1) ω)
    (hs : sourceField (jointDerivative F 0) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => a (((f : IntrinsicSpace) : JointL2) ω) • sourceField (jointDerivative f 0) ω)
    (i : Fin 2) :
    coordinate i (jointDerivative F i) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => a (((f : IntrinsicSpace) : JointL2) ω) • coordinate i (jointDerivative f i) ω := by
  fin_cases i
  · exact hs
  · exact hc

theorem multiply_eq_of_coordinates (U V : JointFieldSpace) (g : JointL2)
    (hb : MemLp (g : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure)
    (hV : ∀ i : Fin 2, coordinate i (V i) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => g ω • coordinate i (U i) ω) : V = multiply g hb U := by
  apply PiLp.ext
  intro i
  apply (coordinate i).injective
  exact Lp.ext ((hV i).trans (multiply_ae g hb U i).symm)

theorem chain_multiply (f F : jointDerivative.domain) (g : JointL2) (a : ℝ → ℝ)
    (hg : g =ᵐ[IBMSourceLaws.jointMeasure] fun ω => a (((f : IntrinsicSpace) : JointL2) ω))
    (hb : MemLp (g : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure)
    (hF : ∀ i : Fin 2, coordinate i (jointDerivative F i) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => a (((f : IntrinsicSpace) : JointL2) ω) • coordinate i (jointDerivative f i) ω) :
    jointDerivative F = multiply g hb (jointDerivative f) := by
  apply multiply_eq_of_coordinates
  intro i
  exact (hF i).trans (hg.symm.mono fun ω hω =>
    congrArg (fun z : ℝ => z • coordinate i (jointDerivative f i) ω) hω)

theorem chain_pairing (f g : jointDerivative.domain) (a : ℝ → ℝ)
    (hg : ∀ i : Fin 2, coordinate i (jointDerivative g i) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => a (((f : IntrinsicSpace) : JointL2) ω) • coordinate i (jointDerivative f i) ω) :
    pairingFunction (jointDerivative g) (jointDerivative f) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => a (((f : IntrinsicSpace) : JointL2) ω) * energyDensity f ω := by
  filter_upwards [hg 0,hg 1] with ω h0 h1
  simp only [pairingFunction,energyDensity,h0,h1,real_inner_smul_left]
  ring

theorem chain_pairing_mem (f g : jointDerivative.domain) (a : ℝ → ℝ)
    (hg : ∀ i : Fin 2, coordinate i (jointDerivative g i) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => a (((f : IntrinsicSpace) : JointL2) ω) • coordinate i (jointDerivative f i) ω)
    (ha : MemLp (fun ω => a (((f : IntrinsicSpace) : JointL2) ω)) ∞ IBMSourceLaws.jointMeasure)
    (he : MemLp (energyDensity f) 2 IBMSourceLaws.jointMeasure) :
    MemLp (pairingFunction (jointDerivative g) (jointDerivative f)) 2
      IBMSourceLaws.jointMeasure :=
  (memLp_congr_ae (chain_pairing f g a hg)).mpr (mul_memLp ha he)

theorem composition_bound (f g : jointDerivative.domain) (a : ℝ → ℝ) (B : ℝ)
    (hg : ((g : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => a (((f : IntrinsicSpace) : JointL2) ω)) (hB : ∀ x, ‖a x‖ ≤ B) :
    ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((g : IntrinsicSpace) : JointL2) ω)| ≤ B := by
  filter_upwards [hg] with ω hω
  rw [hω,← Real.norm_eq_abs]
  exact hB _

theorem multiplier_sub_ae (a y : JointL2)
    (ha : MemLp (a : IBMSourceLaws.JointSample → ℝ) ∞ IBMSourceLaws.jointMeasure)
    (V U : JointFieldSpace) (h : MemLp (pairingFunction V U) 2 IBMSourceLaws.jointMeasure) :
    boundedMultiplier a ha y - correction V U h =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => a ω * y ω - pairingFunction V U ω := by
  filter_upwards [Lp.coeFn_sub (boundedMultiplier a ha y) (correction V U h),
    boundedMultiplier_coeFn a ha y,correction_ae V U h] with ω hs hm hc
  change (boundedMultiplier a ha y - correction V U h) ω =
    boundedMultiplier a ha y ω - correction V U h ω at hs
  exact hs.trans (congrArg₂ (fun x z : ℝ => x-z) hm hc)

theorem closure_of_multiplier (f F g : jointDerivative.domain) (y : IntrinsicSpace)
    (hy : (jointDerivative f,y) ∈ jointDivergence.graph)
    (B : ℝ) (hB : 0 ≤ B)
    (hg : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((g : IntrinsicSpace) : JointL2) ω)| ≤ B)
    (hpair : MemLp (pairingFunction (jointDerivative g) (jointDerivative f)) 2
      IBMSourceLaws.jointMeasure)
    (hF : jointDerivative F = multiply ((g : IntrinsicSpace) : JointL2)
      (IBMNativeProductOperators.bounded_memLp g B hg) (jointDerivative f)) :
    ∃ W : JointL2,
      (W =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
        (((g : IntrinsicSpace) : JointL2) ω) * (y : JointL2) ω -
          pairingFunction (jointDerivative g) (jointDerivative f) ω) ∧
      (jointDerivative F,IntrinsicSpace.orthogonalProjectionOnto W) ∈ jointDivergence.graph := by
  have hu := LinearPMap.mem_domain_of_mem_graph hy
  let u : jointDivergence.domain := ⟨jointDerivative f,hu⟩
  have huy : jointDivergence u = y := ((jointDivergence.image_iff hu).mpr hy).symm
  let hb := IBMNativeProductOperators.bounded_memLp g B hg
  let W : JointL2 := boundedMultiplier ((g : IntrinsicSpace) : JointL2) hb (y : JointL2) -
    correction (jointDerivative g) (jointDerivative f) hpair
  have hW := multiplier_sub_ae ((g : IntrinsicSpace) : JointL2) (y : JointL2) hb
    (jointDerivative g) (jointDerivative f) hpair
  have hmem := IBMNativeIntegrableDivergence.weighted_mem g B hB hg u hpair
  have hv := IBMNativeIntegrableDivergence.weighted_value g B hB hg u hpair
  have hout : IBMNativeIntegrableDivergence.output g hb u hpair =
      IntrinsicSpace.orthogonalProjectionOnto W := by
    exact congrArg (fun z : IntrinsicSpace => IntrinsicSpace.orthogonalProjectionOnto
      (boundedMultiplier ((g : IntrinsicSpace) : JointL2) hb (z : JointL2) -
        correction (jointDerivative g) (jointDerivative f) hpair)) huy
  have hgraph : (multiply ((g : IntrinsicSpace) : JointL2) hb (jointDerivative f),
      IntrinsicSpace.orthogonalProjectionOnto W) ∈ jointDivergence.graph :=
    jointDivergence.mem_graph_iff.mpr ⟨⟨_,hmem⟩,rfl,hv.trans hout⟩
  exact ⟨W,hW,hF.symm ▸ hgraph⟩

theorem composition_top (f : jointDerivative.domain) (a : ℝ → ℝ)
    (ha : Continuous a) (C : ℝ) (hC : ∀ x, ‖a x‖ ≤ C) :
    MemLp (fun ω => a (((f : IntrinsicSpace) : JointL2) ω)) ∞
      IBMSourceLaws.jointMeasure := MemLp.of_bound
    (ha.comp_aestronglyMeasurable (Lp.aestronglyMeasurable ((f : IntrinsicSpace) : JointL2))) C
    (ae_of_all _ fun ω => hC _)

theorem graph_of_chain_results (f : jointDerivative.domain) (y : IntrinsicSpace)
    (hy : (jointDerivative f,y) ∈ jointDivergence.graph)
    (he : MemLp (energyDensity f) 2 IBMSourceLaws.jointMeasure)
    (φ dφ ddφ : ℝ → ℝ) (B C : ℝ) (hB : ∀ x, ‖dφ x‖ ≤ B)
    (hab : MemLp (fun ω => ddφ (((f : IntrinsicSpace) : JointL2) ω)) ∞
      IBMSourceLaws.jointMeasure)
    (hchain : IBMIntrinsicUnboundedChain.ChainResult f φ dφ B)
    (hdchain : IBMIntrinsicUnboundedChain.ChainResult f dφ ddφ C) :
    ∃ F : jointDerivative.domain, ∃ W : JointL2,
      (((F : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
        fun ω => φ (((f : IntrinsicSpace) : JointL2) ω)) ∧
      (W =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
        dφ (((f : IntrinsicSpace) : JointL2) ω) * (y : JointL2) ω -
          ddφ (((f : IntrinsicSpace) : JointL2) ω) * energyDensity f ω) ∧
      (jointDerivative F,IntrinsicSpace.orthogonalProjectionOnto W) ∈ jointDivergence.graph := by
  obtain ⟨F,hF,hFc,hFs,_⟩ := hchain
  obtain ⟨g,hg,hgc,hgs,_⟩ := hdchain
  have hgb := composition_bound f g dφ B hg hB
  have hB0 : 0 ≤ B := (norm_nonneg (dφ 0)).trans (hB 0)
  have hpair := chain_pairing_mem f g ddφ (chain_coordinates f g ddφ hgc hgs) hab he
  have hmul := chain_multiply f F ((g : IntrinsicSpace) : JointL2) dφ hg
    (IBMNativeProductOperators.bounded_memLp g B hgb) (chain_coordinates f F dφ hFc hFs)
  obtain ⟨W,hW,hgraph⟩ := closure_of_multiplier f F g y hy B hB0 hgb hpair hmul
  have hY : (fun ω => (y : JointL2) ω) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => (y : JointL2) ω := Filter.EventuallyEq.rfl
  exact ⟨F,W,hF,hW.trans ((hg.mul hY).sub
    (chain_pairing f g ddφ (chain_coordinates f g ddφ hgc hgs))),hgraph⟩

theorem nonlinear_graph (f : jointDerivative.domain) (y : IntrinsicSpace)
    (hy : (jointDerivative f,y) ∈ jointDivergence.graph)
    (he : MemLp (energyDensity f) 2 IBMSourceLaws.jointMeasure)
    (φ dφ ddφ : ℝ → ℝ) (hd : ∀ x, HasDerivAt φ (dφ x) x)
    (hdd : ∀ x, HasDerivAt dφ (ddφ x) x) (hc : Continuous dφ) (hcc : Continuous ddφ)
    (B C : ℝ) (hB : ∀ x, ‖dφ x‖ ≤ B) (hC : ∀ x, ‖ddφ x‖ ≤ C) :
    ∃ F : jointDerivative.domain, ∃ W : JointL2,
      (((F : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
        fun ω => φ (((f : IntrinsicSpace) : JointL2) ω)) ∧
      (W =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
        dφ (((f : IntrinsicSpace) : JointL2) ω) * (y : JointL2) ω -
          ddφ (((f : IntrinsicSpace) : JointL2) ω) * energyDensity f ω) ∧
      (jointDerivative F,IntrinsicSpace.orthogonalProjectionOnto W) ∈ jointDivergence.graph :=
  graph_of_chain_results f y hy he φ dφ ddφ B C hB (composition_top f ddφ hcc C hC)
    (IBMIntrinsicUnboundedChain.unbounded_chain f φ dφ hd hc B hB)
    (IBMIntrinsicUnboundedChain.unbounded_chain f dφ ddφ hdd hcc C hC)

end OperatorDerivativeRewrite.Foundation.IBMNativeGeneratorChain
