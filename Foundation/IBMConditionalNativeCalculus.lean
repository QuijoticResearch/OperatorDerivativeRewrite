import Foundation.IBMConditionalL1Realization

/-! Strong original-domain calculus from ACTUAL conditional L1 densities in L2. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMConditionalNativeCalculus
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative IBMConditionalL1Realization
open IBMNativeWeakL1Divergence IBMNativeWeakGeneratorChain IBMNativeProductOperators
open IBMNativeFieldMultiplier

theorem weighted_graph (g : jointDerivative.domain) (B : ℝ) (hB : 0 ≤ B)
    (hg : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((g : IntrinsicSpace) : JointL2) ω)| ≤ B)
    (u : jointDivergence.domain)
    (h2 : MemLp (conditional (weakDensity g u)) 2 IBMSourceLaws.jointMeasure) :
    (multiply ((g : IntrinsicSpace) : JointL2) (bounded_memLp g B hg) u,
      realization (weakDensity g u) h2) ∈ jointDivergence.graph :=
  realization_graph _ _ (weakDensity_integrable g u) h2
    (fun v C hC hv => weak_pairing g v B C hB hC hg hv u)

theorem upgrade_weak_chain (f : jointDerivative.domain) (y : IntrinsicSpace)
    (φ dφ ddφ : ℝ → ℝ) (hw : WeakChainResult f y φ dφ ddφ)
    (h2 : MemLp (conditional (density f y dφ ddφ)) 2 IBMSourceLaws.jointMeasure) :
    ∃ F : jointDerivative.domain,
      (((F : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
        fun ω => φ (((f : IntrinsicSpace) : JointL2) ω)) ∧
      (jointDerivative F,realization (density f y dφ ddφ) h2) ∈ jointDivergence.graph := by
  obtain ⟨hi,_,F,hF,ht⟩ := hw
  exact ⟨F,hF,realization_graph (jointDerivative F) _ hi h2
    (fun v C hC hv => (ht v C hC hv).2)⟩

theorem nonlinear_conditional_graph (f : jointDerivative.domain) (y : IntrinsicSpace)
    (hy : (jointDerivative f,y) ∈ jointDivergence.graph)
    (φ dφ ddφ : ℝ → ℝ) (hd : ∀ x, HasDerivAt φ (dφ x) x)
    (hdd : ∀ x, HasDerivAt dφ (ddφ x) x) (hc : Continuous dφ) (hcc : Continuous ddφ)
    (B C : ℝ) (hB : ∀ x, ‖dφ x‖ ≤ B) (hC : ∀ x, ‖ddφ x‖ ≤ C)
    (h2 : MemLp (conditional (density f y dφ ddφ)) 2 IBMSourceLaws.jointMeasure) :
    ∃ F : jointDerivative.domain,
      (((F : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
        fun ω => φ (((f : IntrinsicSpace) : JointL2) ω)) ∧
      (jointDerivative F,realization (density f y dφ ddφ) h2) ∈ jointDivergence.graph :=
  upgrade_weak_chain f y φ dφ ddφ
    (nonlinear_weak_chain f y hy φ dφ ddφ hd hdd hc hcc B C hB hC) h2

theorem clock_potential_sine_graph (T : ℝ≥0)
    (h2 : MemLp (conditional (density (IBMClockPoissonWeakCalculus.potential T)
      (IBMClockPoissonWeakCalculus.target T) Real.cos (fun z => -Real.sin z)))
      2 IBMSourceLaws.jointMeasure) :
    ∃ F : jointDerivative.domain,
      (((F : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
        Real.sin ((((IBMClockPoissonWeakCalculus.potential T) : IntrinsicSpace) : JointL2) ω)) ∧
      (jointDerivative F,realization (density (IBMClockPoissonWeakCalculus.potential T)
        (IBMClockPoissonWeakCalculus.target T) Real.cos (fun z => -Real.sin z)) h2)
        ∈ jointDivergence.graph :=
  upgrade_weak_chain _ _ _ _ _ (IBMClockPoissonWeakCalculus.actual_potential_sine_weak T) h2

end OperatorDerivativeRewrite.Foundation.IBMConditionalNativeCalculus
