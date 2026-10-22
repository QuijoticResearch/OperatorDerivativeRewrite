import Foundation.IBMNativeWeakL1Divergence
import Foundation.IBMIntrinsicPoisson

/-! A genuine weak L1 chain rule on the ENTIRE original native generator domain. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNativeWeakGeneratorChain
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative IBMIntrinsicChainRule
open IBMNativeGeneratorChain IBMNativeWeakL1Divergence IBMNativeFieldMultiplier
open IBMNativeContractionDomain IBMNativeProductOperators
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
set_option backward.isDefEq.respectTransparency false

def density (f : jointDerivative.domain) (y : IntrinsicSpace) (dφ ddφ : ℝ → ℝ)
    (ω : IBMSourceLaws.JointSample) : ℝ :=
  dφ (((f : IntrinsicSpace) : JointL2) ω) * (y : JointL2) ω -
    ddφ (((f : IntrinsicSpace) : JointL2) ω) * energyDensity f ω

def WeakChainResult (f : jointDerivative.domain) (y : IntrinsicSpace)
    (φ dφ ddφ : ℝ → ℝ) : Prop :=
  Integrable (density f y dφ ddφ) IBMSourceLaws.jointMeasure ∧
  (∫ ω, density f y dφ ddφ ω ∂IBMSourceLaws.jointMeasure) = 0 ∧
  ∃ F : jointDerivative.domain,
    (((F : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => φ (((f : IntrinsicSpace) : JointL2) ω)) ∧
    ∀ v : jointDerivative.domain, ∀ C : ℝ, 0 ≤ C →
      (∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((v : IntrinsicSpace) : JointL2) ω)| ≤ C) →
      Integrable (fun ω => (((v : IntrinsicSpace) : JointL2) ω) * density f y dφ ddφ ω)
        IBMSourceLaws.jointMeasure ∧
      inner ℝ (jointDerivative F) (jointDerivative v) =
        ∫ ω, (((v : IntrinsicSpace) : JointL2) ω) * density f y dφ ddφ ω
          ∂IBMSourceLaws.jointMeasure

theorem density_ae (f g : jointDerivative.domain) (u : jointDivergence.domain)
    (y : IntrinsicSpace) (dφ ddφ : ℝ → ℝ) (hy : jointDivergence u = y)
    (hg : ((g : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => dφ (((f : IntrinsicSpace) : JointL2) ω))
    (hp : pairingFunction (jointDerivative g) u =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => ddφ (((f : IntrinsicSpace) : JointL2) ω) * energyDensity f ω) :
    weakDensity g u =ᵐ[IBMSourceLaws.jointMeasure] density f y dφ ddφ := by
  filter_upwards [hg,hp] with ω hg hp
  have hyω := congrArg (fun z : IntrinsicSpace => (z : JointL2) ω) hy
  exact congrArg₂ (fun x z : ℝ => x-z) (congrArg₂ (fun a b : ℝ => a*b) hg hyω) hp

theorem from_chain_results (f : jointDerivative.domain) (y : IntrinsicSpace)
    (hy : (jointDerivative f,y) ∈ jointDivergence.graph)
    (φ dφ ddφ : ℝ → ℝ) (B C : ℝ) (hB : ∀ x, ‖dφ x‖ ≤ B)
    (hchain : IBMIntrinsicUnboundedChain.ChainResult f φ dφ B)
    (hdchain : IBMIntrinsicUnboundedChain.ChainResult f dφ ddφ C) :
    WeakChainResult f y φ dφ ddφ := by
  obtain ⟨F,hF,hFc,hFs,_⟩ := hchain
  obtain ⟨g,hg,hgc,hgs,_⟩ := hdchain
  have hgb := composition_bound f g dφ B hg hB
  have hB0 : 0 ≤ B := (norm_nonneg (dφ 0)).trans (hB 0)
  have hu := LinearPMap.mem_domain_of_mem_graph hy
  let u : jointDivergence.domain := ⟨jointDerivative f,hu⟩
  have huy : jointDivergence u = y := ((jointDivergence.image_iff hu).mpr hy).symm
  have hw := density_ae f g u y dφ ddφ huy hg
    (chain_pairing f g ddφ (chain_coordinates f g ddφ hgc hgs))
  have hi := (weakDensity_integrable g u).congr hw
  have hmean := (integral_congr_ae hw).symm.trans (weakDensity_mean_zero g u)
  have hmul := chain_multiply f F ((g : IntrinsicSpace) : JointL2) dφ hg
    (bounded_memLp g B hgb) (chain_coordinates f F dφ hFc hFs)
  refine ⟨hi,hmean,F,hF,?_⟩
  intro v D hD hv
  have hvb := bounded_memLp v D hv
  have hp := weak_pairing g v B D hB0 hD hgb hv u
  have hvw := hw.mono fun ω hω => congrArg (fun z : ℝ => (((v : IntrinsicSpace) : JointL2) ω)*z) hω
  exact ⟨bounded_times_integrable ((v : IntrinsicSpace) : JointL2) hvb _ hi,
    (congrArg (fun V : JointFieldSpace => inner ℝ V (jointDerivative v)) hmul).trans
      (hp.trans (integral_congr_ae hvw))⟩

theorem nonlinear_weak_chain (f : jointDerivative.domain) (y : IntrinsicSpace)
    (hy : (jointDerivative f,y) ∈ jointDivergence.graph)
    (φ dφ ddφ : ℝ → ℝ) (hd : ∀ x, HasDerivAt φ (dφ x) x)
    (hdd : ∀ x, HasDerivAt dφ (ddφ x) x) (hc : Continuous dφ) (hcc : Continuous ddφ)
    (B C : ℝ) (hB : ∀ x, ‖dφ x‖ ≤ B) (hC : ∀ x, ‖ddφ x‖ ≤ C) :
    WeakChainResult f y φ dφ ddφ :=
  from_chain_results f y hy φ dφ ddφ B C hB
    (IBMIntrinsicUnboundedChain.unbounded_chain f φ dφ hd hc B hB)
    (IBMIntrinsicUnboundedChain.unbounded_chain f dφ ddφ hdd hcc C hC)

theorem poisson_sine_weak (x : IBMIntrinsicPoisson.centered) :
    WeakChainResult (IBMIntrinsicPoisson.solutionElement x) (x : IntrinsicSpace)
      Real.sin Real.cos (fun z => -Real.sin z) :=
  nonlinear_weak_chain _ _ (IBMIntrinsicPoisson.poisson_graph x)
    Real.sin Real.cos (fun z => -Real.sin z) Real.hasDerivAt_sin Real.hasDerivAt_cos
    Real.continuous_cos Real.continuous_sin.neg 1 1
    (fun z => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one z)
    (fun z => by simpa only [norm_neg,Real.norm_eq_abs] using Real.abs_sin_le_one z)

end OperatorDerivativeRewrite.Foundation.IBMNativeWeakGeneratorChain
