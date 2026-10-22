import Foundation.IBMIntrinsicUnboundedChain

/-! Actual bounded observables form a strong graph core for the original native IBM D. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNativeBoundedGraphCore
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMIntrinsicChainRule IBMIntrinsicChainApproximation IBMIntrinsicUnboundedChain
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
set_option backward.isDefEq.respectTransparency false

theorem identity_gradient_limit (x : JointL2) (g : FieldSpace) (u : ℕ → FieldSpace)
    (hu : ∀ n, uncurryField (u n) =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
      approximantDerivative (fun z => z) (fun _ => 1) n (x ω) • uncurryField g ω) :
    Tendsto u atTop (𝓝 g) := by
  obtain ⟨G,hG,ht⟩ := gradient_limit x (fun z => z) (fun _ => 1)
    continuous_id continuous_const 1 (by intro; norm_num) g u hu
  have he : G = uncurryField g := Lp.ext (by simpa only [one_smul] using hG)
  rw [he] at ht
  have hc := (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).continuous.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def,uncurryField,LinearIsometryEquiv.apply_symm_apply] using hc

theorem field_limit (u : ℕ → JointFieldSpace) (g : JointFieldSpace)
    (h : ∀ i : Fin 2, Tendsto (fun n => u n i) atTop (𝓝 (g i))) :
    Tendsto u atTop (𝓝 g) := by
  have hp := tendsto_pi_nhds.mpr h
  exact (PiLp.continuous_toLp (p := 2) (fun _ : Fin 2 => FieldSpace)).continuousAt.tendsto.comp hp

def BoundedGraphResult (f : jointDerivative.domain) : Prop :=
  ∃ u : ℕ → jointDerivative.domain,
    (∀ n, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((u n : IntrinsicSpace) : JointL2) ω)| ≤ C) ∧
    Tendsto (fun n => (u n : IntrinsicSpace)) atTop (𝓝 (f : IntrinsicSpace)) ∧
    Tendsto (fun n => jointDerivative (u n)) atTop (𝓝 (jointDerivative f))

theorem bounded_graph (f : jointDerivative.domain) : BoundedGraphResult f := by
  obtain ⟨u,hu,hc,hs⟩ := bounded_approximants f (fun z => z) (fun _ => 1)
    (fun z => hasDerivAt_id z) continuous_const 1 (by intro; norm_num)
  obtain ⟨F,hF,hv⟩ := approximation_values ((f : IntrinsicSpace) : JointL2)
    (fun z => z) (fun _ => 1) (fun z => hasDerivAt_id z) 1 (by intro; norm_num)
    (fun n => ((u n : IntrinsicSpace) : JointL2)) hu
  have he : F = ((f : IntrinsicSpace) : JointL2) := Lp.ext hF
  rw [he] at hv
  refine ⟨u,?_,tendsto_subtype_rng.mpr hv,field_limit _ _ ?_⟩
  · intro n
    refine ⟨(width n)⁻¹,inv_nonneg.mpr (RealSteklovApprox.width_pos n).le,?_⟩
    filter_upwards [hu n] with ω hω
    rw [hω]
    exact (Real.norm_eq_abs _ ▸ clip_bound n (((f : IntrinsicSpace) : JointL2) ω))
  · intro i
    fin_cases i
    · exact identity_gradient_limit
        (ProductL2Curry.swap gaussianProduct gaussianProduct ((f : IntrinsicSpace) : JointL2))
        (jointDerivative f 0) (fun n => jointDerivative (u n) 0) hs
    · exact identity_gradient_limit ((f : IntrinsicSpace) : JointL2)
        (jointDerivative f 1) (fun n => jointDerivative (u n) 1) hc

end OperatorDerivativeRewrite.Foundation.IBMNativeBoundedGraphCore
