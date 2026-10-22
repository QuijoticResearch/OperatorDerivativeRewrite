import Foundation.IBMIntrinsicChainMultiplier

/-! Unbounded C1 composition through actual strong graph convergence. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicUnboundedChain
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMIntrinsicChainRule IBMIntrinsicChainEnergy IBMIntrinsicChainApproximation IBMIntrinsicChainMultiplier
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
set_option backward.isDefEq.respectTransparency false

theorem gradient_limit (x : JointL2) (φ dφ : ℝ → ℝ)
    (hφ : Continuous φ) (hc : Continuous dφ) (B : ℝ) (hB : ∀ z, ‖dφ z‖ ≤ B)
    (g : FieldSpace) (u : ℕ → FieldSpace)
    (hu : ∀ n, uncurryField (u n) =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
      approximantDerivative φ dφ n (x ω) • uncurryField g ω) :
    ∃ G : JointVectorL2,
      G =ᵐ[IBMSourceLaws.jointMeasure] (fun ω => dφ (x ω) • uncurryField g ω) ∧
      Tendsto (fun n => uncurryField (u n)) atTop (𝓝 G) := by
  let a : ℕ → IBMSourceLaws.JointSample → ℝ := fun n ω => approximantDerivative φ dφ n (x ω)
  let b : IBMSourceLaws.JointSample → ℝ := fun ω => dφ (x ω)
  have ha : ∀ n, AEStronglyMeasurable (a n) IBMSourceLaws.jointMeasure := fun n =>
    (approximantDerivative_continuous φ dφ hφ hc n).comp_aestronglyMeasurable (Lp.aestronglyMeasurable x)
  have hb : AEStronglyMeasurable b IBMSourceLaws.jointMeasure :=
    hc.comp_aestronglyMeasurable (Lp.aestronglyMeasurable x)
  have hba : ∀ n, ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ‖a n ω‖ ≤ B :=
    fun n => ae_of_all _ fun ω => approximantDerivative_bound φ dφ B hB n (x ω)
  have hbb : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ‖b ω‖ ≤ B := ae_of_all _ fun ω => hB _
  have hB0 : 0 ≤ B := (norm_nonneg (dφ 0)).trans (hB 0)
  have ht := multiply_tendsto a b ha hb B hB0 hba hbb
    (ae_of_all _ fun ω => approximantDerivative_tendsto φ dφ (x ω)) (uncurryField g)
  have he (n : ℕ) : uncurryField (u n) = multiply (a n) (ha n) B (hba n) (uncurryField g) :=
    Lp.ext ((hu n).trans (multiply_ae (a n) (ha n) B (hba n) (uncurryField g)).symm)
  exact ⟨multiply b hb B hbb (uncurryField g), multiply_ae b hb B hbb _,
    ht.congr' (Eventually.of_forall fun n => (he n).symm)⟩

theorem close_graph (F : IntrinsicSpace) (u : ℕ → jointDerivative.domain) (Gs Gc : JointVectorL2)
    (hu : Tendsto (fun n => ((u n : IntrinsicSpace) : JointL2)) atTop (𝓝 (F : JointL2)))
    (hs : Tendsto (fun n => uncurryField (jointDerivative (u n) 0)) atTop (𝓝 Gs))
    (hc : Tendsto (fun n => uncurryField (jointDerivative (u n) 1)) atTop (𝓝 Gc)) :
    (F,pairField (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct Gs)
      (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct Gc)) ∈ jointDerivative.graph := by
  have hs' := (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).continuous.continuousAt.tendsto.comp hs
  have hc' := (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).continuous.continuousAt.tendsto.comp hc
  simp only [Function.comp_def,uncurryField,LinearIsometryEquiv.apply_symm_apply] at hs' hc'
  have hp : Tendsto (fun n => WithLp.ofLp (jointDerivative (u n))) atTop
      (𝓝 (![ProductL2Curry.curryEquiv gaussianProduct gaussianProduct Gs,
        ProductL2Curry.curryEquiv gaussianProduct gaussianProduct Gc] : Fin 2 → FieldSpace)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · exact hs'
    · exact hc'
  have hg := (PiLp.continuous_toLp (p := 2) (fun _ : Fin 2 => FieldSpace)).continuousAt.tendsto.comp hp
  exact jointDerivative_closed.mem_of_tendsto
    ((tendsto_subtype_rng.mpr hu).prodMk_nhds hg)
    (Eventually.of_forall fun n => jointDerivative.mem_graph (u n))

theorem approximation_values (f : JointL2) (φ dφ : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt φ (dφ x) x) (B : ℝ) (hB : ∀ x, ‖dφ x‖ ≤ B)
    (u : ℕ → JointL2)
    (hu : ∀ n, u n =ᵐ[IBMSourceLaws.jointMeasure] fun ω => approximant φ n (f ω)) :
    ∃ F : JointL2, F =ᵐ[IBMSourceLaws.jointMeasure] (fun ω => φ (f ω)) ∧
      Tendsto u atTop (𝓝 F) := by
  let hm := composition_memLp φ dφ hd B hB f
  let F : JointL2 := hm.toLp _
  have hF : F =ᵐ[IBMSourceLaws.jointMeasure] fun ω => φ (f ω) := hm.coeFn_toLp
  have he (n : ℕ) : u n = clippedValue n F := by
    apply Lp.ext
    exact (hu n).trans ((clippedValue_ae n F).trans (hF.fun_comp (clip n))).symm
  exact ⟨F,hF,(clippedValue_tendsto F).congr' (Eventually.of_forall fun n => (he n).symm)⟩

def ChainResult (f : jointDerivative.domain) (φ dφ : ℝ → ℝ) (B : ℝ) : Prop :=
    ∃ F : jointDerivative.domain,
      ((F : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
        (fun ω => φ (((f : IntrinsicSpace) : JointL2) ω)) ∧
      uncurryField (jointDerivative F 1) =ᵐ[IBMSourceLaws.jointMeasure]
        (fun ω => dφ (((f : IntrinsicSpace) : JointL2) ω) • uncurryField (jointDerivative f 1) ω) ∧
      sourceField (jointDerivative F 0) =ᵐ[IBMSourceLaws.jointMeasure]
        (fun ω => dφ (((f : IntrinsicSpace) : JointL2) ω) • sourceField (jointDerivative f 0) ω) ∧
      ‖jointDerivative F‖ ≤ B * ‖jointDerivative f‖

theorem package_chain (f : jointDerivative.domain) (F : IntrinsicSpace)
    (Gs Gc : JointVectorL2) (φ dφ : ℝ → ℝ) (B : ℝ) (hB : ∀ x, ‖dφ x‖ ≤ B)
    (hF : (F : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => φ (((f : IntrinsicSpace) : JointL2) ω))
    (hg : (F,pairField (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct Gs)
      (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct Gc)) ∈ jointDerivative.graph)
    (hGc : Gc =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => dφ (((f : IntrinsicSpace) : JointL2) ω) • uncurryField (jointDerivative f 1) ω)
    (hGs : Gs =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => dφ (ProductL2Curry.swap gaussianProduct gaussianProduct
        ((f : IntrinsicSpace) : JointL2) ω) • uncurryField (jointDerivative f 0) ω) :
    ChainResult f φ dφ B := by
  have hm := LinearPMap.mem_domain_of_mem_graph hg
  let Fe : jointDerivative.domain := ⟨F,hm⟩
  have he : jointDerivative Fe = pairField
      (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct Gs)
      (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct Gc) :=
    ((jointDerivative.image_iff hm).mpr hg).symm
  have hclock : uncurryField (jointDerivative Fe 1) = Gc := by
    rw [he]
    exact (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm_apply_apply Gc
  have hsource : uncurryField (jointDerivative Fe 0) = Gs := by
    rw [he]
    exact (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm_apply_apply Gs
  have hcAE : uncurryField (jointDerivative Fe 1) =ᵐ[IBMSourceLaws.jointMeasure]
      (fun ω => dφ (((f : IntrinsicSpace) : JointL2) ω) • uncurryField (jointDerivative f 1) ω) := by
    rw [hclock]
    exact hGc
  have hsAE : uncurryField (jointDerivative Fe 0) =ᵐ[IBMSourceLaws.jointMeasure]
      (fun ω => dφ (ProductL2Curry.swap gaussianProduct gaussianProduct
        ((f : IntrinsicSpace) : JointL2) ω) • uncurryField (jointDerivative f 0) ω) := by
    rw [hsource]
    exact hGs
  exact ⟨Fe,hF,hcAE,swap_chain_ae ((f : IntrinsicSpace) : JointL2)
    (uncurryField (jointDerivative f 0)) (uncurryField (jointDerivative Fe 0)) dφ hsAE,
      joint_chain_bound f Fe dφ B hB hcAE hsAE⟩

theorem bounded_approximants (f : jointDerivative.domain)
    (φ dφ : ℝ → ℝ) (hd : ∀ x, HasDerivAt φ (dφ x) x) (hc : Continuous dφ)
    (B : ℝ) (hB : ∀ x, ‖dφ x‖ ≤ B) :
    ∃ u : ℕ → jointDerivative.domain,
      (∀ n, ((u n : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
        fun ω => approximant φ n (((f : IntrinsicSpace) : JointL2) ω)) ∧
      (∀ n, uncurryField (jointDerivative (u n) 1) =ᵐ[IBMSourceLaws.jointMeasure]
        fun ω => approximantDerivative φ dφ n (((f : IntrinsicSpace) : JointL2) ω) •
          uncurryField (jointDerivative f 1) ω) ∧
      (∀ n, uncurryField (jointDerivative (u n) 0) =ᵐ[IBMSourceLaws.jointMeasure]
        fun ω => approximantDerivative φ dφ n (ProductL2Curry.swap gaussianProduct gaussianProduct
          ((f : IntrinsicSpace) : JointL2) ω) • uncurryField (jointDerivative f 0) ω) := by
  have hφ : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  choose u hu huc hus using fun n => bounded_chain f (approximant φ n)
    (approximantDerivative φ dφ n) (approximant_hasDerivAt φ dφ hd n)
    (approximantDerivative_continuous φ dφ hφ hc n) ((width n)⁻¹) B
    (fun x => clip_bound n (φ x)) (approximantDerivative_bound φ dφ B hB n)
  exact ⟨u,hu,huc,hus⟩

def GraphResult (f : jointDerivative.domain) (φ dφ : ℝ → ℝ) : Prop :=
    ∃ F : IntrinsicSpace, ∃ Gs Gc : JointVectorL2,
      (F : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
        (fun ω => φ (((f : IntrinsicSpace) : JointL2) ω)) ∧
      (F,pairField (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct Gs)
        (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct Gc)) ∈ jointDerivative.graph ∧
      (Gc =ᵐ[IBMSourceLaws.jointMeasure]
        fun ω => dφ (((f : IntrinsicSpace) : JointL2) ω) • uncurryField (jointDerivative f 1) ω) ∧
      (Gs =ᵐ[IBMSourceLaws.jointMeasure]
        fun ω => dφ (ProductL2Curry.swap gaussianProduct gaussianProduct
          ((f : IntrinsicSpace) : JointL2) ω) • uncurryField (jointDerivative f 0) ω)

theorem approximation_graph (f : jointDerivative.domain)
    (φ dφ : ℝ → ℝ) (hd : ∀ x, HasDerivAt φ (dφ x) x) (hc : Continuous dφ)
    (B : ℝ) (hB : ∀ x, ‖dφ x‖ ≤ B) (u : ℕ → jointDerivative.domain)
    (hu : ∀ n, ((u n : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => approximant φ n (((f : IntrinsicSpace) : JointL2) ω))
    (huc : ∀ n, uncurryField (jointDerivative (u n) 1) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => approximantDerivative φ dφ n (((f : IntrinsicSpace) : JointL2) ω) • uncurryField (jointDerivative f 1) ω)
    (hus : ∀ n, uncurryField (jointDerivative (u n) 0) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => approximantDerivative φ dφ n (ProductL2Curry.swap gaussianProduct gaussianProduct
        ((f : IntrinsicSpace) : JointL2) ω) • uncurryField (jointDerivative f 0) ω) :
    GraphResult f φ dφ := by
  have hφ : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  obtain ⟨F,hF,hv⟩ := approximation_values ((f : IntrinsicSpace) : JointL2) φ dφ hd B hB
    (fun n => ((u n : IntrinsicSpace) : JointL2)) hu
  obtain ⟨Gc,hGc,hcLim⟩ := gradient_limit ((f : IntrinsicSpace) : JointL2) φ dφ hφ hc B hB
    (jointDerivative f 1) (fun n => jointDerivative (u n) 1) huc
  obtain ⟨Gs,hGs,hsLim⟩ := gradient_limit
    (ProductL2Curry.swap gaussianProduct gaussianProduct ((f : IntrinsicSpace) : JointL2))
    φ dφ hφ hc B hB (jointDerivative f 0) (fun n => jointDerivative (u n) 0) hus
  have hobs := composition_observable (f : IntrinsicSpace) F φ hφ hF
  have hg := close_graph ⟨F,hobs⟩ u Gs Gc hv hsLim hcLim
  exact ⟨⟨F,hobs⟩,Gs,Gc,hF,hg,hGc,hGs⟩

theorem unbounded_chain (f : jointDerivative.domain)
    (φ dφ : ℝ → ℝ) (hd : ∀ x, HasDerivAt φ (dφ x) x) (hc : Continuous dφ)
    (B : ℝ) (hB : ∀ x, ‖dφ x‖ ≤ B) :
    ChainResult f φ dφ B := by
  obtain ⟨u,hu,huc,hus⟩ := bounded_approximants f φ dφ hd hc B hB
  obtain ⟨F,Gs,Gc,hF,hg,hGc,hGs⟩ := approximation_graph f φ dφ hd hc B hB u hu huc hus
  exact package_chain f F Gs Gc φ dφ B hB hF hg hGc hGs

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicUnboundedChain
