import Foundation.IBMTruncatedSquare

/-! The actual square of a bounded full-domain native IBM observable. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicBoundedSquare
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative IBMIntrinsicChainRule
open IBMIntrinsicChainEnergy IBMIntrinsicUnboundedChain IBMTruncatedSquare
set_option backward.isDefEq.respectTransparency false

theorem bounded_square (f : jointDerivative.domain) (R : ℝ) (hR : 0 ≤ R)
    (hf : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((f : IntrinsicSpace) : JointL2) ω)| ≤ R) :
    ChainResult f (fun x => x^2) (fun x => 2*x) (2*R) := by
  obtain ⟨F,hF,hc,hs,hb⟩ := unbounded_chain f (squareExtension R) (fun x => 2*clamp R x)
    (squareExtension_hasDerivAt R) (continuous_const.mul (clamp_continuous R))
    (2*R) (derivative_bound R hR)
  refine ⟨F,?_,?_,?_,hb⟩
  · filter_upwards [hF,hf] with ω hF hf
    exact hF.trans (squareExtension_eq R _ hR hf)
  · filter_upwards [hc,hf] with ω hc hf
    exact hc.trans (congrArg (fun x : ℝ => (2*x) • uncurryField (jointDerivative f 1) ω)
      (clamp_eq R _ hf))
  · filter_upwards [hs,hf] with ω hs hf
    exact hs.trans (congrArg (fun x : ℝ => (2*x) • sourceField (jointDerivative f 0) ω)
      (clamp_eq R _ hf))

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicBoundedSquare
