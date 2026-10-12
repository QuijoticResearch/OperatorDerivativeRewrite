import Foundation.ProductL2Equivalence
import Foundation.GaussianBochnerDerivative
import Foundation.GaussianPredictableFull
import Foundation.AdjointUnitaryTransport

/-! The closed field derivative on the actual time-probability L2 space.
The derivative value is coefficient-Hilbert-space valued. Identification with
a second Brownian time variable still requires the appropriate range theorem. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianProductDerivative
open InfiniteGaussian GaussianTimeProductL2 GaussianBochnerDerivative
open GaussianTimeHilbert
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

/-- Separability follows from the already constructed isometric first-chaos embedding. -/
theorem coefficientSpace_secondCountable : SecondCountableTopology CoefficientSpace :=
  firstChaosEmbedding.isometry.isEmbedding.secondCountableTopology

local instance : SecondCountableTopology CoefficientSpace := coefficientSpace_secondCountable

def scalarCurry : TimeProbabilityL2 ≃ₗᵢ[ℝ] TimeScalarL2 :=
  ProductL2Curry.curryEquiv volume gaussianProduct

abbrev ProductDerivativeL2 := Lp CoefficientSpace 2 timeProbability

def vectorCurry : ProductDerivativeL2 ≃ₗᵢ[ℝ] TimeDerivativeL2 :=
  ProductL2Curry.curryEquiv volume gaussianProduct

theorem scalarCurry_coeFn (u : TimeProbabilityL2) :
    ∀ᵐ t ∂(volume : Measure ℝ), scalarCurry u t =ᵐ[gaussianProduct] fun ω => u (t, ω) :=
  ProductL2Curry.curryEquiv_coeFn _ _ u

theorem vectorCurry_coeFn (v : ProductDerivativeL2) :
    ∀ᵐ t ∂(volume : Measure ℝ), vectorCurry v t =ᵐ[gaussianProduct] fun ω => v (t, ω) :=
  ProductL2Curry.curryEquiv_coeFn _ _ v

theorem scalarCurry_productTensor (a : TimeHilbert) (f : GaussianL2) :
    scalarCurry (GaussianTimeProductL2.productTensor a f) =
      BochnerClosedOperator.tensor volume a f := by
  have he : GaussianTimeProductL2.productTensor a f =
      ProductL2Curry.productTensor volume gaussianProduct a f := by
    apply Lp.ext
    filter_upwards [GaussianTimeProductL2.productTensor_coeFn a f,
      ProductL2Curry.productTensor_coeFn volume gaussianProduct a f] with z ht hp
    simp only [ht, hp, smul_eq_mul]
  rw [he]
  exact ProductL2Curry.curry_productTensor _ _ a f

def derivative : TimeProbabilityL2 →ₗ.[ℝ] ProductDerivativeL2 :=
  vectorCurry.symm.toLinearEquiv.toLinearMap.compPMap
    (AdjointUnitaryTransport.pullback scalarCurry fieldDerivative)

theorem derivative_domain_iff (u : TimeProbabilityL2) :
    u ∈ derivative.domain ↔ scalarCurry u ∈ fieldDerivative.domain := Iff.rfl

theorem derivative_graph_iff (u : TimeProbabilityL2) (v : ProductDerivativeL2) :
    (u, v) ∈ derivative.graph ↔ (scalarCurry u, vectorCurry v) ∈ fieldDerivative.graph := by
  constructor
  · intro h
    obtain ⟨w, hw, hv⟩ := derivative.mem_graph_iff.mp h
    change (w : TimeProbabilityL2) = u at hw
    have hg := (AdjointUnitaryTransport.pullback scalarCurry fieldDerivative).mem_graph w
    rw [AdjointUnitaryTransport.mem_pullback_graph] at hg
    change vectorCurry.symm (fieldDerivative ⟨scalarCurry w, w.property⟩) = v at hv
    have he := congrArg vectorCurry hv
    simp only [vectorCurry.apply_symm_apply] at he
    convert hg using 1
    exact Prod.ext (congrArg scalarCurry hw.symm) he.symm
  · intro h
    have hg := (AdjointUnitaryTransport.mem_pullback_graph scalarCurry fieldDerivative
      u (vectorCurry v)).mpr h
    obtain ⟨w, hw, hv⟩ :=
      (AdjointUnitaryTransport.pullback scalarCurry fieldDerivative).mem_graph_iff.mp hg
    refine derivative.mem_graph_iff.mpr ⟨w, hw, ?_⟩
    change vectorCurry.symm ((AdjointUnitaryTransport.pullback scalarCurry fieldDerivative) w) = v
    rw [hv, vectorCurry.symm_apply_apply]

theorem derivative_isClosed : derivative.IsClosed := by
  have he : (derivative.graph : Set (TimeProbabilityL2 × ProductDerivativeL2)) =
      (fun z => (scalarCurry z.1, vectorCurry z.2)) ⁻¹'
        (fieldDerivative.graph : Set (TimeScalarL2 × TimeDerivativeL2)) := by
    ext z
    exact derivative_graph_iff z.1 z.2
  change IsClosed (derivative.graph : Set (TimeProbabilityL2 × ProductDerivativeL2))
  rw [he]
  exact fieldDerivative_isClosed.preimage
    ((scalarCurry.continuous.comp continuous_fst).prodMk
      (vectorCurry.continuous.comp continuous_snd))

theorem derivative_dense_domain : Dense (derivative.domain : Set TimeProbabilityL2) :=
  AdjointUnitaryTransport.pullback_dense_domain scalarCurry fieldDerivative
    fieldDerivative_dense_domain

/-- Both original product representatives are transported to their actual L2 slices. -/
theorem derivative_fiber_graph_iff (u : TimeProbabilityL2) (v : ProductDerivativeL2) :
    (u, v) ∈ derivative.graph ↔ ∀ᵐ t ∂(volume : Measure ℝ),
      (scalarCurry u t, vectorCurry v t) ∈ closedCylindricalDerivative.graph := by
  rw [derivative_graph_iff, fieldDerivative_graph_iff]

/-- An independent predictable Sobolev domain; no core-closure density is asserted. -/
def predictableSobolev : Submodule ℝ TimeProbabilityL2 :=
  GaussianPredictableFull.fullPredictable ⊓ derivative.domain

theorem polynomial_tensor_graph (a : TimeHilbert) (f : polynomialCylindricalDomain) :
    (GaussianTimeProductL2.productTensor a f,
      ProductL2Curry.productTensor volume gaussianProduct a (polynomialDerivative f)) ∈
        derivative.graph := by
  rw [derivative_graph_iff, scalarCurry_productTensor]
  change (_, ProductL2Curry.curry volume gaussianProduct
    (ProductL2Curry.productTensor volume gaussianProduct a (polynomialDerivative f))) ∈ _
  rw [ProductL2Curry.curry_productTensor]
  exact GaussianBochnerDerivative.polynomial_tensor_graph a f

theorem past_polynomial_step_mem_predictableSobolev {n : ℕ}
    (s t : ℝ≥0) (r : Fin n → ℝ≥0) (hrs : ∀ i, r i ≤ s)
    (p : MvPolynomial (Fin n) ℝ) :
    GaussianTimeProductL2.productTensor (intervalVector s t)
      (GaussianTimeDivergence.pastCoefficient r p) ∈ predictableSobolev := by
  constructor
  · exact GaussianPredictableFull.past_step_mem_fullPredictable s t _
      (GaussianPastStepCompletion.past_polynomial_measurable s r hrs p)
  · exact LinearPMap.mem_domain_iff.mpr ⟨_, polynomial_tensor_graph _ _⟩

/-- Determinism is an actual separated-variable product class with one L2 time profile. -/
theorem derivative_zero_iff_deterministic (u : TimeProbabilityL2) :
    (u, (0 : ProductDerivativeL2)) ∈ derivative.graph ↔
      ∃ a : TimeHilbert, u = GaussianTimeProductL2.productTensor a gaussianOne := by
  rw [derivative_graph_iff, map_zero, fieldDerivative_zero_iff_deterministic]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, scalarCurry.injective ?_⟩
    rw [scalarCurry_productTensor]
    exact ha
  · rintro ⟨a, rfl⟩
    exact ⟨a, scalarCurry_productTensor a gaussianOne⟩

end OperatorDerivativeRewrite.Foundation.GaussianProductDerivative
