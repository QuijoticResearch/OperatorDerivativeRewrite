import Foundation.IBMIntrinsicAbsoluteApproximation
import Foundation.IBMIntrinsicPoincare

/-! An actual nonsmooth absolute-value rule on the original full IBM native domain. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicAbsoluteChain
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMIntrinsicChainRule IBMIntrinsicChainEnergy IBMIntrinsicChainApproximation
open IBMIntrinsicUnboundedChain IBMIntrinsicAbsoluteApproximation SmoothAbsoluteApproximation
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
set_option backward.isDefEq.respectTransparency false

theorem radius_sequence (f : jointDerivative.domain) :
    ∃ u : ℕ → jointDerivative.domain,
      (∀ n, ((u n : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
        fun ω => radius (width n) (((f : IntrinsicSpace) : JointL2) ω)) ∧
      (∀ n, uncurryField (jointDerivative (u n) 1) =ᵐ[IBMSourceLaws.jointMeasure]
        fun ω => slope (width n) (((f : IntrinsicSpace) : JointL2) ω) •
          uncurryField (jointDerivative f 1) ω) ∧
      (∀ n, uncurryField (jointDerivative (u n) 0) =ᵐ[IBMSourceLaws.jointMeasure]
        fun ω => slope (width n) (ProductL2Curry.swap gaussianProduct gaussianProduct
          ((f : IntrinsicSpace) : JointL2) ω) • uncurryField (jointDerivative f 0) ω) := by
  choose u hu huc hus using fun n => radius_chain f n
  exact ⟨u,hu,huc,hus⟩

theorem absolute_graph (f : jointDerivative.domain) :
    GraphResult f (fun x => |x|) BrownianSignIntegral.signum := by
  obtain ⟨u,hu,huc,hus⟩ := radius_sequence f
  have hv := radius_value_limit ((f : IntrinsicSpace) : JointL2)
    (fun n => ((u n : IntrinsicSpace) : JointL2)) hu
  obtain ⟨Gc,hGc,hcLim⟩ := radius_gradient_limit ((f : IntrinsicSpace) : JointL2)
    (jointDerivative f 1) (fun n => jointDerivative (u n) 1) huc
  obtain ⟨Gs,hGs,hsLim⟩ := radius_gradient_limit
    (ProductL2Curry.swap gaussianProduct gaussianProduct ((f : IntrinsicSpace) : JointL2))
    (jointDerivative f 0) (fun n => jointDerivative (u n) 0) hus
  have hF := absoluteValue_ae ((f : IntrinsicSpace) : JointL2)
  have hobs := composition_observable (f : IntrinsicSpace)
    (absoluteValue ((f : IntrinsicSpace) : JointL2)) (fun x => |x|) continuous_abs hF
  have hg := close_graph ⟨_,hobs⟩ u Gs Gc hv hsLim hcLim
  exact ⟨⟨_,hobs⟩,Gs,Gc,hF,hg,hGc,hGs⟩

theorem absolute_chain (f : jointDerivative.domain) :
    ChainResult f (fun x => |x|) BrownianSignIntegral.signum 1 := by
  obtain ⟨F,Gs,Gc,hF,hg,hGc,hGs⟩ := absolute_graph f
  exact package_chain f F Gs Gc (fun x => |x|) BrownianSignIntegral.signum 1
    BrownianSignIntegral.signum_bound hF hg hGc hGs

theorem shifted_value (f : jointDerivative.domain) (a : ℝ) :
    ((((f-a • IBMIntrinsicPoincare.oneElement) : jointDerivative.domain) : IntrinsicSpace) : JointL2)
      =ᵐ[IBMSourceLaws.jointMeasure] fun ω => (((f : IntrinsicSpace) : JointL2) ω)-a := by
  have ho : ((IBMIntrinsicPoincare.oneElement : IntrinsicSpace) : JointL2)
      =ᵐ[IBMSourceLaws.jointMeasure] fun _ => (1 : ℝ) := IBMGlobalVacuum.one_coeFn
  filter_upwards [Lp.coeFn_sub ((f : IntrinsicSpace) : JointL2)
    (a • ((IBMIntrinsicPoincare.oneElement : IntrinsicSpace) : JointL2)),
    Lp.coeFn_smul a ((IBMIntrinsicPoincare.oneElement : IntrinsicSpace) : JointL2),ho] with ω hs hm ho
  change (((f : IntrinsicSpace) : JointL2)-a •
    ((IBMIntrinsicPoincare.oneElement : IntrinsicSpace) : JointL2)) ω = _
  rw [hs,Pi.sub_apply,hm,Pi.smul_apply,ho,smul_eq_mul,mul_one]

theorem shifted_derivative (f : jointDerivative.domain) (a : ℝ) :
    jointDerivative (f-a • IBMIntrinsicPoincare.oneElement) = jointDerivative f := by
  rw [jointDerivative.map_sub,jointDerivative.map_smul,IBMIntrinsicPoincare.one_derivative,
    smul_zero,sub_zero]

theorem absolute_shift_chain (f : jointDerivative.domain) (a : ℝ) :
    ChainResult f (fun x => |x-a|) (fun x => BrownianSignIntegral.signum (x-a)) 1 := by
  let g : jointDerivative.domain := f-a • IBMIntrinsicPoincare.oneElement
  obtain ⟨F,hF,hc,hs,hb⟩ := absolute_chain g
  have hv := shifted_value f a
  have hd : jointDerivative g = jointDerivative f := shifted_derivative f a
  rw [hd] at hc hs hb
  refine ⟨F,?_,?_,?_,hb⟩
  · exact hF.trans (hv.fun_comp (fun x : ℝ => |x|))
  · filter_upwards [hc,hv] with ω hc hv
    exact hc.trans (congrArg (fun x : ℝ => BrownianSignIntegral.signum x •
      uncurryField (jointDerivative f 1) ω) hv)
  · filter_upwards [hs,hv] with ω hs hv
    exact hs.trans (congrArg (fun x : ℝ => BrownianSignIntegral.signum x •
      sourceField (jointDerivative f 0) ω) hv)

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicAbsoluteChain
