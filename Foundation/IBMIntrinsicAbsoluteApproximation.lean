import Foundation.IBMIntrinsicUnboundedChain
import Foundation.BrownianTanakaApproximation

/-! Actual native IBM radius/sign approximations using the existing scalar calculus. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicAbsoluteApproximation
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMIntrinsicChainRule IBMIntrinsicChainEnergy IBMIntrinsicChainApproximation
open IBMIntrinsicChainMultiplier IBMIntrinsicUnboundedChain SmoothAbsoluteApproximation
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
set_option backward.isDefEq.respectTransparency false

def absoluteValue (x : JointL2) : JointL2 := (Lp.memLp x).norm.toLp _

theorem absoluteValue_ae (x : JointL2) :
    absoluteValue x =ᵐ[IBMSourceLaws.jointMeasure] fun ω => |x ω| := by
  have h : absoluteValue x =ᵐ[IBMSourceLaws.jointMeasure] fun ω => ‖x ω‖ :=
    MemLp.coeFn_toLp _
  exact h.trans (ae_of_all _ fun ω => Real.norm_eq_abs (x ω))

theorem radius_value_limit (x : JointL2) (u : ℕ → JointL2)
    (hu : ∀ n, u n =ᵐ[IBMSourceLaws.jointMeasure] fun ω => radius (width n) (x ω)) :
    Tendsto u atTop (𝓝 (absoluteValue x)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ IBMIntrinsicChainApproximation.width_tendsto
  intro n
  have hb : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ‖(u n-absoluteValue x) ω‖ ≤ width n := by
    filter_upwards [hu n,absoluteValue_ae x,Lp.coeFn_sub (u n) (absoluteValue x)] with ω hn hx hs
    rw [hs,Pi.sub_apply,hn,hx]
    exact uniform_error (RealSteklovApprox.width_pos n) _
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (RealSteklovApprox.width_pos n).le hb

theorem radius_gradient_limit (x : JointL2) (g : FieldSpace) (u : ℕ → FieldSpace)
    (hu : ∀ n, uncurryField (u n) =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
      slope (width n) (x ω) • uncurryField g ω) :
    ∃ G : JointVectorL2,
      G =ᵐ[IBMSourceLaws.jointMeasure] (fun ω => BrownianSignIntegral.signum (x ω) • uncurryField g ω) ∧
      Tendsto (fun n => uncurryField (u n)) atTop (𝓝 G) := by
  let a : ℕ → IBMSourceLaws.JointSample → ℝ := fun n ω => slope (width n) (x ω)
  let b : IBMSourceLaws.JointSample → ℝ := fun ω => BrownianSignIntegral.signum (x ω)
  have ha : ∀ n, AEStronglyMeasurable (a n) IBMSourceLaws.jointMeasure := fun n =>
    (slopeLip (RealSteklovApprox.width_pos n)).continuous.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable x)
  have hb : AEStronglyMeasurable b IBMSourceLaws.jointMeasure :=
    (BrownianSignIntegral.signum_measurable.comp (Lp.stronglyMeasurable x).measurable).stronglyMeasurable.aestronglyMeasurable
  have hba : ∀ n, ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ‖a n ω‖ ≤ (1 : ℝ) :=
    fun n => ae_of_all _ fun _ => slope_bound (RealSteklovApprox.width_pos n) _
  have hbb : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ‖b ω‖ ≤ (1 : ℝ) :=
    ae_of_all _ fun _ => BrownianSignIntegral.signum_bound _
  have ht := multiply_tendsto a b ha hb 1 (by norm_num) hba hbb
    (ae_of_all _ fun ω => BrownianTanakaApproximation.slope_tendsto_sign (x ω)) (uncurryField g)
  have he (n : ℕ) : uncurryField (u n) = multiply (a n) (ha n) 1 (hba n) (uncurryField g) :=
    Lp.ext ((hu n).trans (multiply_ae (a n) (ha n) 1 (hba n) (uncurryField g)).symm)
  exact ⟨multiply b hb 1 hbb (uncurryField g),multiply_ae b hb 1 hbb _,
    ht.congr' (Eventually.of_forall fun n => (he n).symm)⟩

def RadiusResult (f : jointDerivative.domain) (n : ℕ) : Prop :=
    ∃ F : jointDerivative.domain,
      ((F : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
        (fun ω => radius (width n) (((f : IntrinsicSpace) : JointL2) ω)) ∧
      uncurryField (jointDerivative F 1) =ᵐ[IBMSourceLaws.jointMeasure]
        (fun ω => slope (width n) (((f : IntrinsicSpace) : JointL2) ω) • uncurryField (jointDerivative f 1) ω) ∧
      uncurryField (jointDerivative F 0) =ᵐ[IBMSourceLaws.jointMeasure]
        (fun ω => slope (width n) (ProductL2Curry.swap gaussianProduct gaussianProduct
          ((f : IntrinsicSpace) : JointL2) ω) • uncurryField (jointDerivative f 0) ω)

theorem radius_chain (f : jointDerivative.domain) (n : ℕ) : RadiusResult f n := by
  have hn := RealSteklovApprox.width_pos n
  obtain ⟨u,hu,huc,hus⟩ := bounded_approximants f (radius (width n)) (slope (width n))
    (radius_hasDerivAt hn) (slopeLip hn).continuous 1 (slope_bound hn)
  obtain ⟨F,Gs,Gc,hF,hg,hGc,hGs⟩ := approximation_graph f (radius (width n)) (slope (width n))
    (radius_hasDerivAt hn) (slopeLip hn).continuous 1 (slope_bound hn) u hu huc hus
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
  refine ⟨Fe,hF,?_,?_⟩
  · rw [hclock]
    exact hGc
  · rw [hsource]
    exact hGs

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicAbsoluteApproximation
