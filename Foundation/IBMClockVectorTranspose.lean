import Foundation.IBMNonlinearClockField
import Foundation.IBMIntrinsicChainRule

/-! Restore source/clock order for genuine coefficient-valued fields.
The two nested L2 types coincide, but their parameter interpretations do not. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMClockVectorTranspose
open InfiniteGaussian
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : MeasurableSpace CoefficientSpace := borel CoefficientSpace
local instance : BorelSpace CoefficientSpace := ⟨rfl⟩

abbrev Flat := Lp CoefficientSpace 2 IBMSourceLaws.jointMeasure
abbrev Nested := Lp GaussianVectorL2 2 gaussianProduct

def swap : Flat →ₗᵢ[ℝ] Flat :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.swap Measure.measurePreserving_swap

theorem swap_ae (f : Flat) :
    swap f =ᵐ[IBMSourceLaws.jointMeasure] fun p => f (p.2, p.1) :=
  Lp.coeFn_compMeasurePreserving f Measure.measurePreserving_swap

def realize : Nested →ₗᵢ[ℝ] Flat :=
  swap.comp (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm.toLinearIsometry

def clockField : Nested →ₗᵢ[ℝ] Nested :=
  (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).toLinearIsometry.comp realize

theorem realize_ae_of_sections (u : Nested)
    (f : IBMSourceLaws.JointSample → CoefficientSpace) (hm : Measurable f)
    (hf : ∀ᵐ Y ∂gaussianProduct, u Y =ᵐ[gaussianProduct] fun X => f (X, Y)) :
    realize u =ᵐ[IBMSourceLaws.jointMeasure] f := by
  let v := (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm u
  have hp : v =ᵐ[gaussianProduct.prod gaussianProduct] fun p => f (p.2, p.1) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (Lp.stronglyMeasurable v).measurable
      (hm.comp measurable_swap))).mpr
    filter_upwards [ProductL2Curry.curryEquiv_symm_coeFn gaussianProduct gaussianProduct u, hf]
      with Y hc ha
    exact hc.symm.trans ha
  have hs := Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp hp
  filter_upwards [swap_ae v, hs] with p hv hp
  exact hv.trans hp

theorem clockField_sections (u : Nested)
    (f : IBMSourceLaws.JointSample → CoefficientSpace) (hm : Measurable f)
    (hf : ∀ᵐ Y ∂gaussianProduct, u Y =ᵐ[gaussianProduct] fun X => f (X, Y)) :
    ∀ᵐ X ∂gaussianProduct, clockField u X =ᵐ[gaussianProduct] fun Y => f (X, Y) := by
  have ha := Measure.ae_ae_of_ae_prod (realize_ae_of_sections u f hm hf)
  filter_upwards [ProductL2Curry.curryEquiv_coeFn gaussianProduct gaussianProduct (realize u), ha]
    with X hc ha
  exact hc.trans ha

theorem uncurry_clockField (u : Nested) :
    IBMIntrinsicChainRule.uncurryField (clockField u) = realize u := by
  exact (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm_apply_apply _

theorem clockField_norm (u : Nested) : ‖clockField u‖ = ‖u‖ := clockField.norm_map u

theorem clockField_integral {μ : Measure ℝ} (u : ℝ → Nested) (hu : Integrable u μ) :
    clockField (∫ t, u t ∂μ) = ∫ t, clockField (u t) ∂μ :=
  (clockField.toContinuousLinearMap.integral_comp_comm hu).symm

end OperatorDerivativeRewrite.Foundation.IBMClockVectorTranspose
