import Foundation.GaussianDerivativeReflection
import Foundation.IBMNativeClockDirection

/-! Reflection parity of the full original native IBM clock derivative. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockDerivativeReflection
open InfiniteGaussian GaussianSampleReflection GaussianDerivativeReflection
open IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative IBMIntrinsicChainRule
open IBMClockSignSymmetry IBMClockInnovationObstruction IBMFiniteAverageCore
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
set_option backward.isDefEq.respectTransparency false

theorem curry_reflection {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [SecondCountableTopology (Lp E 2 gaussianProduct)]
    (R : Lp E 2 gaussianProduct →L[ℝ] Lp E 2 gaussianProduct)
    (J : Lp E 2 IBMSourceLaws.jointMeasure → Lp E 2 IBMSourceLaws.jointMeasure)
    (hR : ∀ v, R v =ᵐ[gaussianProduct] fun y => v (reflect y))
    (hJ : ∀ v, J v =ᵐ[IBMSourceLaws.jointMeasure] fun ω => v (ω.1,reflect ω.2))
    (f : Lp E 2 IBMSourceLaws.jointMeasure) :
    ProductL2Curry.curry gaussianProduct gaussianProduct (J f) =
      R.compLpL 2 gaussianProduct (ProductL2Curry.curry gaussianProduct gaussianProduct f) := by
  apply Lp.ext
  filter_upwards [ProductL2Curry.curry_coeFn gaussianProduct gaussianProduct (J f),
    ae_ae_of_ae_prod (hJ f),R.coeFn_compLpL (ProductL2Curry.curry gaussianProduct gaussianProduct f),
    ProductL2Curry.curry_coeFn gaussianProduct gaussianProduct f]
    with x hleft hj hr hright
  apply Lp.ext
  have ht := reflect_preserving.quasiMeasurePreserving.ae_eq_comp hright
  have he : R (ProductL2Curry.curry gaussianProduct gaussianProduct f x)
      =ᵐ[gaussianProduct] fun y => f (x,reflect y) := (hR _).trans ht
  rw [hr]
  exact (hleft.trans hj).trans he.symm

def fiberScalar : ScalarFieldSpace →L[ℝ] ScalarFieldSpace :=
  reflection.toContinuousLinearMap.compLpL 2 gaussianProduct

def fiberVector : FieldSpace →L[ℝ] FieldSpace :=
  vectorReflection.toContinuousLinearMap.compLpL 2 gaussianProduct

def jointVectorReflection : JointVectorL2 →ₗᵢ[ℝ] JointVectorL2 :=
  Lp.compMeasurePreservingₗᵢ ℝ reflectClock reflectClock_preserving

theorem jointVectorReflection_ae (g : JointVectorL2) :
    jointVectorReflection g =ᵐ[IBMSourceLaws.jointMeasure] fun ω => g (reflectClock ω) :=
  Lp.coeFn_compMeasurePreserving g reflectClock_preserving

theorem scalar_compat (f : JointL2) :
    clockUnitary (jointReflection f) = fiberScalar (clockUnitary f) :=
  curry_reflection reflection.toContinuousLinearMap jointReflection reflection_ae jointReflection_ae f

theorem vector_compat (g : FieldSpace) :
    uncurryField (fiberVector g) = jointVectorReflection (uncurryField g) := by
  apply (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).injective
  have ht := curry_reflection vectorReflection.toContinuousLinearMap jointVectorReflection
    vectorReflection_ae jointVectorReflection_ae (uncurryField g)
  change (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct)
      (jointVectorReflection (uncurryField g)) =
    fiberVector ((ProductL2Curry.curryEquiv gaussianProduct gaussianProduct) (uncurryField g)) at ht
  simp only [uncurryField,LinearIsometryEquiv.apply_symm_apply] at ht ⊢
  exact ht.symm

theorem partial_graph {f : ScalarFieldSpace} {g : FieldSpace}
    (h : (f,g) ∈ partialDerivative.graph) :
    (fiberScalar f,-fiberVector g) ∈ partialDerivative.graph := by
  rw [BochnerClosedOperator.mem_lift_graph_iff] at h ⊢
  filter_upwards [h,reflection.toContinuousLinearMap.coeFn_compLpL f,
    vectorReflection.toContinuousLinearMap.coeFn_compLpL g,Lp.coeFn_neg (fiberVector g)]
    with x h hs hv hn
  change fiberScalar f x = reflection (f x) at hs
  change fiberVector g x = vectorReflection (g x) at hv
  change (fiberScalar f x,(-fiberVector g) x) ∈ closedCylindricalDerivative.graph
  rw [hs,hn,Pi.neg_apply,hv]
  exact GaussianDerivativeReflection.closed_graph h

theorem observable_clock_odd (f : jointDerivative.domain) :
    jointVectorReflection (uncurryField (jointDerivative f 1)) =
      -uncurryField (jointDerivative f 1) := by
  have hr := partial_graph (clock_partial_graph f)
  have hf : fiberScalar (clockUnitary ((f : IntrinsicSpace) : JointL2)) =
      clockUnitary ((f : IntrinsicSpace) : JointL2) :=
    (scalar_compat _).symm.trans (congrArg clockUnitary
      (observable_fixed ((f : IntrinsicSpace) : JointL2) (f : IntrinsicSpace).property))
  rw [hf] at hr
  have hg : jointDerivative f 1 = -fiberVector (jointDerivative f 1) :=
    partialDerivative.mem_graph_snd_inj (clock_partial_graph f) hr rfl
  have he : uncurryField (jointDerivative f 1) =
      -jointVectorReflection (uncurryField (jointDerivative f 1)) := by
    calc
      _ = uncurryField (-fiberVector (jointDerivative f 1)) := congrArg uncurryField hg
      _ = -uncurryField (fiberVector (jointDerivative f 1)) :=
        (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm.map_neg _
      _ = _ := congrArg Neg.neg (vector_compat _)
  have ht := congrArg Neg.neg he
  simpa only [neg_neg] using ht.symm

end OperatorDerivativeRewrite.Foundation.IBMClockDerivativeReflection
