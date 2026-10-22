import Foundation.IBMIntrinsicBoundedSquare
import Mathlib.Tactic.Module

/-! Actual bounded-observable product closure and native Leibniz fields. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMIntrinsicProductCalculus
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMIntrinsicChainRule IBMIntrinsicChainEnergy IBMIntrinsicUnboundedChain IBMIntrinsicBoundedSquare
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
set_option backward.isDefEq.respectTransparency false

def sectionMap (i : Fin 2) : JointFieldSpace →ₗ[ℝ] JointVectorL2 where
  toFun g := uncurryField (g i)
  map_add' g h := by
    change (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm (g i+h i) = _
    exact (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm.map_add _ _
  map_smul' c g := by
    change (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm (c • g i) = _
    exact (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm.map_smul c _

def originalSourceMap : JointFieldSpace →ₗ[ℝ] JointVectorL2 :=
  vectorSwap.toLinearMap.comp (sectionMap 0)

theorem sum_bound (f g : jointDerivative.domain) (C D : ℝ)
    (hf : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((f : IntrinsicSpace) : JointL2) ω)| ≤ C)
    (hg : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((g : IntrinsicSpace) : JointL2) ω)| ≤ D) :
    ∀ᵐ ω ∂IBMSourceLaws.jointMeasure,
      |((((f+g : jointDerivative.domain) : IntrinsicSpace) : JointL2) ω)| ≤ C+D := by
  filter_upwards [hf,hg,Lp.coeFn_add ((f : IntrinsicSpace) : JointL2)
    ((g : IntrinsicSpace) : JointL2)] with ω hf hg ha
  change |((((f : IntrinsicSpace) : JointL2)+((g : IntrinsicSpace) : JointL2)) ω)| ≤ _
  rw [ha,Pi.add_apply]
  exact (abs_add_le _ _).trans (add_le_add hf hg)

theorem difference_bound (f g : jointDerivative.domain) (C D : ℝ)
    (hf : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((f : IntrinsicSpace) : JointL2) ω)| ≤ C)
    (hg : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((g : IntrinsicSpace) : JointL2) ω)| ≤ D) :
    ∀ᵐ ω ∂IBMSourceLaws.jointMeasure,
      |((((f-g : jointDerivative.domain) : IntrinsicSpace) : JointL2) ω)| ≤ C+D := by
  filter_upwards [hf,hg,Lp.coeFn_sub ((f : IntrinsicSpace) : JointL2)
    ((g : IntrinsicSpace) : JointL2)] with ω hf hg ha
  change |((((f : IntrinsicSpace) : JointL2)-((g : IntrinsicSpace) : JointL2)) ω)| ≤ _
  rw [ha,Pi.sub_apply]
  exact (abs_sub _ _).trans (add_le_add hf hg)

theorem scalar_polarization (x y : ℝ) : (1/4 : ℝ)*((x+y)^2-(x-y)^2)=x*y := by ring

theorem vector_polarization (x y : ℝ) (u v : CoefficientSpace) :
    (1/4 : ℝ) • ((2*(x+y)) • (u+v)-(2*(x-y)) • (u-v)) = x • v+y • u := by
  module

theorem lp_polarization_value (x y P M : JointL2)
    (hp : P =ᵐ[IBMSourceLaws.jointMeasure] fun ω => (x ω+y ω)^2)
    (hm : M =ᵐ[IBMSourceLaws.jointMeasure] fun ω => (x ω-y ω)^2) :
    (1/4 : ℝ) • (P-M) =ᵐ[IBMSourceLaws.jointMeasure] fun ω => x ω*y ω := by
  filter_upwards [hp,hm,Lp.coeFn_sub P M,Lp.coeFn_smul (1/4 : ℝ) (P-M)] with ω hp hm hs ho
  rw [ho,Pi.smul_apply,hs,Pi.sub_apply,hp,hm,smul_eq_mul]
  exact scalar_polarization _ _

theorem polarization_value (f g P M : jointDerivative.domain)
    (hp : ((P : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => ((((f+g : jointDerivative.domain) : IntrinsicSpace) : JointL2) ω)^2)
    (hm : ((M : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => ((((f-g : jointDerivative.domain) : IntrinsicSpace) : JointL2) ω)^2) :
    (((((1/4 : ℝ) • (P-M)) : jointDerivative.domain) : IntrinsicSpace) : JointL2)
      =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
        (((f : IntrinsicSpace) : JointL2) ω) * (((g : IntrinsicSpace) : JointL2) ω) := by
  have hp' : ((P : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => (((f : IntrinsicSpace) : JointL2) ω+((g : IntrinsicSpace) : JointL2) ω)^2 := by
    filter_upwards [hp,Lp.coeFn_add ((f : IntrinsicSpace) : JointL2)
      ((g : IntrinsicSpace) : JointL2)] with ω hp ha
    exact hp.trans (congrArg (fun z : ℝ => z^2) ha)
  have hm' : ((M : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => (((f : IntrinsicSpace) : JointL2) ω-((g : IntrinsicSpace) : JointL2) ω)^2 := by
    filter_upwards [hm,Lp.coeFn_sub ((f : IntrinsicSpace) : JointL2)
      ((g : IntrinsicSpace) : JointL2)] with ω hm hs
    exact hm.trans (congrArg (fun z : ℝ => z^2) hs)
  exact lp_polarization_value _ _ _ _ hp' hm'

theorem linear_quarter_sub {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (L : V →ₗ[ℝ] W) (P M : V) :
    L ((1/4 : ℝ) • (P-M)) = (1/4 : ℝ) • (L P-L M) := by
  rw [L.map_smul,L.map_sub]

theorem lp_quarter_sub_ae (P M : JointVectorL2) :
    (1/4 : ℝ) • (P-M) =ᵐ[IBMSourceLaws.jointMeasure] fun ω => (1/4 : ℝ) • (P ω-M ω) := by
  filter_upwards [Lp.coeFn_smul (1/4 : ℝ) (P-M),Lp.coeFn_sub P M] with ω ha hs
  rw [ha,Pi.smul_apply,hs,Pi.sub_apply]

theorem polarization_linear_field {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : V →ₗ[ℝ] JointVectorL2) (x y : JointL2) (f g P M : V)
    (hp : L P =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
      (2*(x+y) ω) • L (f+g) ω)
    (hm : L M =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
      (2*(x-y) ω) • L (f-g) ω) :
    L ((1/4 : ℝ) • (P-M)) =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
      x ω • L g ω+y ω • L f ω := by
  have hplus : L (f+g) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => L f ω + L g ω := by
    have he : L (f+g) = L f+L g := L.map_add f g
    exact he.symm ▸ Lp.coeFn_add _ _
  have hminus : L (f-g) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => L f ω - L g ω := by
    have he : L (f-g) = L f-L g := L.map_sub f g
    exact he.symm ▸ Lp.coeFn_sub _ _
  have hout : L ((1/4 : ℝ) • (P-M)) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => (1/4 : ℝ) • (L P ω-L M ω) := by
    have he : L ((1/4 : ℝ) • (P-M)) =
        (1/4 : ℝ) • (L P-L M) := linear_quarter_sub L P M
    exact he.symm ▸ lp_quarter_sub_ae _ _
  filter_upwards [hout,hp,hm,hplus,hminus,
    Lp.coeFn_add x y,
    Lp.coeFn_sub x y]
    with ω hout hp hm hplus hminus ha hs
  rw [hout,hp,hm,hplus,hminus,ha,hs,Pi.add_apply,Pi.sub_apply]
  exact vector_polarization _ _ _ _

theorem polarization_field (L : JointFieldSpace →ₗ[ℝ] JointVectorL2)
    (f g P M : jointDerivative.domain)
    (hp : L (jointDerivative P) =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
      (2*((((f+g : jointDerivative.domain) : IntrinsicSpace) : JointL2) ω)) •
        L (jointDerivative (f+g)) ω)
    (hm : L (jointDerivative M) =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
      (2*((((f-g : jointDerivative.domain) : IntrinsicSpace) : JointL2) ω)) •
        L (jointDerivative (f-g)) ω) :
    L (jointDerivative ((1/4 : ℝ) • (P-M))) =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
      (((f : IntrinsicSpace) : JointL2) ω) • L (jointDerivative g) ω +
      (((g : IntrinsicSpace) : JointL2) ω) • L (jointDerivative f) ω := by
  let LD : jointDerivative.domain →ₗ[ℝ] JointVectorL2 := L.comp jointDerivative.toFun
  exact polarization_linear_field LD ((f : IntrinsicSpace) : JointL2)
    ((g : IntrinsicSpace) : JointL2) f g P M hp hm

def ProductResult (f g : jointDerivative.domain) : Prop :=
  ∃ F : jointDerivative.domain,
    ((F : IntrinsicSpace) : JointL2) =ᵐ[IBMSourceLaws.jointMeasure] (fun ω =>
      (((f : IntrinsicSpace) : JointL2) ω)*(((g : IntrinsicSpace) : JointL2) ω)) ∧
    uncurryField (jointDerivative F 1) =ᵐ[IBMSourceLaws.jointMeasure] (fun ω =>
      (((f : IntrinsicSpace) : JointL2) ω) • uncurryField (jointDerivative g 1) ω +
      (((g : IntrinsicSpace) : JointL2) ω) • uncurryField (jointDerivative f 1) ω) ∧
    sourceField (jointDerivative F 0) =ᵐ[IBMSourceLaws.jointMeasure] (fun ω =>
      (((f : IntrinsicSpace) : JointL2) ω) • sourceField (jointDerivative g 0) ω +
      (((g : IntrinsicSpace) : JointL2) ω) • sourceField (jointDerivative f 0) ω)

theorem bounded_product (f g : jointDerivative.domain) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((f : IntrinsicSpace) : JointL2) ω)| ≤ C)
    (hg : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, |(((g : IntrinsicSpace) : JointL2) ω)| ≤ D) :
    ProductResult f g := by
  obtain ⟨P,hP,hPc,hPs,_⟩ := bounded_square (f+g) (C+D) (add_nonneg hC hD) (sum_bound f g C D hf hg)
  obtain ⟨M,hM,hMc,hMs,_⟩ := bounded_square (f-g) (C+D) (add_nonneg hC hD) (difference_bound f g C D hf hg)
  refine ⟨(1/4 : ℝ) • (P-M),polarization_value f g P M hP hM,?_,?_⟩
  · exact polarization_field (sectionMap 1) f g P M hPc hMc
  · exact polarization_field originalSourceMap f g P M hPs hMs

end OperatorDerivativeRewrite.Foundation.IBMIntrinsicProductCalculus
