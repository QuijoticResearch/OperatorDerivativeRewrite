import Foundation.IBMNativeL1TestSeparation

/-! Exact ORIGINAL adjoint-domain characterization by actual conditional L1 densities. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMConditionalAdjointDomain
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative IBMObservableHorizonLimit
open IBMConditionalL1Realization IBMNativeWeakL1Divergence IBMNativeWeakGeneratorChain
open IBMNativeL1TestSeparation IBMNativeProductOperators IBMNativeFieldMultiplier
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
set_option backward.isDefEq.respectTransparency false

theorem bounded_difference_zero (u : jointDivergence.domain)
    (q : IBMSourceLaws.JointSample → ℝ) (hq : Integrable q IBMSourceLaws.jointMeasure)
    (hu : BoundedWeakPairing (u : JointFieldSpace) q) (v : jointDerivative.domain)
    (hv : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((v : IntrinsicSpace) : JointL2) ω)| ≤ 1) :
    (∫ ω, (((v : IntrinsicSpace) : JointL2) ω) *
      (conditional q ω - ((jointDivergence u : IntrinsicSpace) : JointL2) ω)
      ∂IBMSourceLaws.jointMeasure) = 0 := by
  have hb := bounded_memLp v 1 hv
  have h1 := conditional_pairing q hq (v : IntrinsicSpace) hb
  have h2 : (∫ ω, (((v : IntrinsicSpace) : JointL2) ω) *
      ((jointDivergence u : IntrinsicSpace) : JointL2) ω ∂IBMSourceLaws.jointMeasure) =
      inner ℝ (jointDivergence u) (v : IntrinsicSpace) :=
    (product_mean ((v : IntrinsicSpace) : JointL2)
      ((jointDivergence u : IntrinsicSpace) : JointL2)).trans (real_inner_comm _ _)
  have h3 := jointDerivative.adjoint_isFormalAdjoint jointDerivative_dense u v
  have h4 := hu v 1 (by norm_num) hv
  have hc : Integrable (conditional q) IBMSourceLaws.jointMeasure := integrable_condExp
  have hr := (Lp.memLp ((jointDivergence u : IntrinsicSpace) : JointL2)).integrable (by norm_num)
  have hs := weighted_sub_integral ((v : IntrinsicSpace) : JointL2) hb
    (conditional q) (((jointDivergence u : IntrinsicSpace) : JointL2) : IBMSourceLaws.JointSample → ℝ)
    hc hr
  linarith

theorem conditional_eq_adjoint (u : jointDivergence.domain)
    (q : IBMSourceLaws.JointSample → ℝ) (hq : Integrable q IBMSourceLaws.jointMeasure)
    (hu : BoundedWeakPairing (u : JointFieldSpace) q) :
    conditional q =ᵐ[IBMSourceLaws.jointMeasure]
      ((jointDivergence u : IntrinsicSpace) : JointL2) := by
  have hc : Integrable (conditional q) IBMSourceLaws.jointMeasure := integrable_condExp
  have hr := (Lp.memLp ((jointDivergence u : IntrinsicSpace) : JointL2)).integrable (by norm_num)
  have hm : AEStronglyMeasurable[observationSigma] (conditional q) IBMSourceLaws.jointMeasure :=
    stronglyMeasurable_condExp.aestronglyMeasurable
  have hmr : AEStronglyMeasurable[observationSigma]
      ((jointDivergence u : IntrinsicSpace) : JointL2) IBMSourceLaws.jointMeasure :=
    (jointDivergence u).property
  have hz := annihilator_zero
    (conditional q - (((jointDivergence u : IntrinsicSpace) : JointL2) : IBMSourceLaws.JointSample → ℝ))
    (hc.sub hr) (hm.sub hmr) (fun v hv => bounded_difference_zero u q hq hu v hv)
  filter_upwards [hz] with ω hω
  exact sub_eq_zero.mp hω

theorem conditional_mem_of_adjoint (u : jointDivergence.domain)
    (q : IBMSourceLaws.JointSample → ℝ) (hq : Integrable q IBMSourceLaws.jointMeasure)
    (hu : BoundedWeakPairing (u : JointFieldSpace) q) :
    MemLp (conditional q) 2 IBMSourceLaws.jointMeasure :=
  (memLp_congr_ae (conditional_eq_adjoint u q hq hu)).mpr
    (Lp.memLp ((jointDivergence u : IntrinsicSpace) : JointL2))

theorem domain_iff_conditional_L2 (U : JointFieldSpace) (q : IBMSourceLaws.JointSample → ℝ)
    (hq : Integrable q IBMSourceLaws.jointMeasure) (hU : BoundedWeakPairing U q) :
    U ∈ jointDivergence.domain ↔ MemLp (conditional q) 2 IBMSourceLaws.jointMeasure := by
  constructor
  · intro hm
    exact conditional_mem_of_adjoint ⟨U,hm⟩ q hq hU
  · intro h2
    exact LinearPMap.mem_domain_of_mem_graph (realization_graph U q hq h2 hU)

theorem realization_eq_adjoint (u : jointDivergence.domain)
    (q : IBMSourceLaws.JointSample → ℝ) (hq : Integrable q IBMSourceLaws.jointMeasure)
    (hu : BoundedWeakPairing (u : JointFieldSpace) q) :
    realization q (conditional_mem_of_adjoint u q hq hu) = jointDivergence u :=
  Subtype.ext (Lp.ext ((realization_ae q _).trans (conditional_eq_adjoint u q hq hu)))

theorem weighted_domain_iff (g : jointDerivative.domain) (B : ℝ) (hB : 0 ≤ B)
    (hg : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((g : IntrinsicSpace) : JointL2) ω)| ≤ B)
    (u : jointDivergence.domain) :
    multiply ((g : IntrinsicSpace) : JointL2) (bounded_memLp g B hg) u ∈ jointDivergence.domain ↔
      MemLp (conditional (weakDensity g u)) 2 IBMSourceLaws.jointMeasure :=
  domain_iff_conditional_L2 _ _ (weakDensity_integrable g u)
    (fun v C hC hv => weak_pairing g v B C hB hC hg hv u)

theorem weak_chain_domain_iff (f F : jointDerivative.domain) (y : IntrinsicSpace)
    (φ dφ ddφ : ℝ → ℝ) (hw : WeakChainResult f y φ dφ ddφ)
    (hF : ((F : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => φ (((f : IntrinsicSpace) : JointL2) ω)) :
    jointDerivative F ∈ jointDivergence.domain ↔
      MemLp (conditional (density f y dφ ddφ)) 2 IBMSourceLaws.jointMeasure := by
  obtain ⟨hi,_,G,hG,ht⟩ := hw
  have he : F = G := Subtype.ext (Subtype.ext (Lp.ext (hF.trans hG.symm)))
  subst F
  exact domain_iff_conditional_L2 _ _ hi (fun v C hC hv => (ht v C hC hv).2)

theorem clock_potential_sine_domain_iff (T : ℝ≥0) (F : jointDerivative.domain)
    (hF : ((F : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
      Real.sin ((((IBMClockPoissonWeakCalculus.potential T) : IntrinsicSpace) : JointL2) ω)) :
    jointDerivative F ∈ jointDivergence.domain ↔
      MemLp (conditional (density (IBMClockPoissonWeakCalculus.potential T)
        (IBMClockPoissonWeakCalculus.target T) Real.cos (fun z => -Real.sin z)))
        2 IBMSourceLaws.jointMeasure :=
  weak_chain_domain_iff _ F _ _ _ _ (IBMClockPoissonWeakCalculus.actual_potential_sine_weak T) hF

end OperatorDerivativeRewrite.Foundation.IBMConditionalAdjointDomain
