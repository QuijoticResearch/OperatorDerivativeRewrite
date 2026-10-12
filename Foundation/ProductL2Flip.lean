import Foundation.ProductL2Equivalence
import Foundation.BochnerLinearIsometry

/-! Interchanging two actual scalar L2 parameters and compatibility with tensors. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.ProductL2Curry
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]

def swap : Lp ℝ 2 (μ.prod ν) →ₗᵢ[ℝ] Lp ℝ 2 (ν.prod μ) :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.swap measurePreserving_swap

theorem swap_coeFn (f : Lp ℝ 2 (μ.prod ν)) :
    swap μ ν f =ᵐ[ν.prod μ] fun z => f (z.2, z.1) :=
  Lp.coeFn_compMeasurePreserving f measurePreserving_swap

theorem swap_productTensor (a : Lp ℝ 2 μ) (v : Lp ℝ 2 ν) :
    swap μ ν (productTensor μ ν a v) = productTensor ν μ v a := by
  apply Lp.ext
  have ht := measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp
    (productTensor_coeFn μ ν a v)
  filter_upwards [swap_coeFn μ ν (productTensor μ ν a v), ht,
    productTensor_coeFn ν μ v a] with z hs ht hv
  rw [hs, hv]
  change productTensor μ ν a v (z.2, z.1) = _ at ht
  rw [ht]
  exact mul_comm _ _

variable [SecondCountableTopology (Lp ℝ 2 μ)] [SecondCountableTopology (Lp ℝ 2 ν)]

def flip : Lp (Lp ℝ 2 ν) 2 μ →ₗᵢ[ℝ] Lp (Lp ℝ 2 μ) 2 ν :=
  (curryEquiv ν μ).toLinearIsometry.comp
    ((swap μ ν).comp (curryEquiv μ ν).symm.toLinearIsometry)

theorem flip_tensor (a : Lp ℝ 2 μ) (v : Lp ℝ 2 ν) :
    flip μ ν (BochnerClosedOperator.tensor μ a v) = BochnerClosedOperator.tensor ν v a := by
  have ht : (curryEquiv μ ν).symm (BochnerClosedOperator.tensor μ a v) =
      productTensor μ ν a v := by
    apply (curryEquiv μ ν).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact (curry_productTensor μ ν a v).symm
  change curry ν μ (swap μ ν ((curryEquiv μ ν).symm
    (BochnerClosedOperator.tensor μ a v))) = _
  rw [ht, swap_productTensor, curry_productTensor]

end OperatorDerivativeRewrite.Foundation.ProductL2Curry

namespace OperatorDerivativeRewrite.Foundation.BochnerLinearIsometry
variable {X E F : Type*} [MeasurableSpace X] (μ : Measure X)
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem lift_tensor (J : E →ₗᵢ[ℝ] F) (a : Lp ℝ 2 μ) (v : E) :
    lift μ J (BochnerClosedOperator.tensor μ a v) =
      BochnerClosedOperator.tensor μ a (J v) := by
  apply Lp.ext
  filter_upwards [lift_coeFn μ J (BochnerClosedOperator.tensor μ a v),
    BochnerClosedOperator.tensor_coeFn μ a v,
    BochnerClosedOperator.tensor_coeFn μ a (J v)] with x hl hv ht
  rw [hl, hv, ht, map_smul]

end OperatorDerivativeRewrite.Foundation.BochnerLinearIsometry
