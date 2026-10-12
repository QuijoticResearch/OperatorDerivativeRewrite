import Foundation.GaussianBrownianBracket

/-! Gaussian-mean projection gives genuine graph approximation of every
deterministic predictable L2 field. No full adapted Sobolev density is asserted. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianDeterministicGraphCore
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProductL2 GaussianProductDerivative
open GaussianPredictableFull GaussianAdaptedGraphCore GaussianContinuousRigidity
open GaussianTimeDivergence GaussianPredictableL2Completion
attribute [local instance] timeHilbert_secondCountable coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def vacuumProjection : GaussianL2 →L[ℝ] GaussianL2 :=
  (ContinuousLinearMap.toSpanSingleton ℝ gaussianOne).comp (innerSL ℝ gaussianOne)

theorem gaussianOne_inner_self : inner ℝ gaussianOne gaussianOne = 1 := by
  rw [gaussianOne_inner_eq_integral, integral_congr_ae gaussianOne_coeFn]
  simp

def meanProjection : TimeProbabilityL2 →L[ℝ] TimeProbabilityL2 :=
  scalarCurry.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((vacuumProjection.compLpL 2 volume).comp scalarCurry.toLinearIsometry.toContinuousLinearMap)

theorem meanProjection_tensor (a : TimeHilbert) (f : GaussianL2) :
    meanProjection (productTensor a f) = productTensor a (inner ℝ gaussianOne f • gaussianOne) := by
  apply scalarCurry.injective
  change scalarCurry (scalarCurry.symm (vacuumProjection.compLp (scalarCurry _))) = _
  rw [scalarCurry.apply_symm_apply, scalarCurry_productTensor, scalarCurry_productTensor]
  apply Lp.ext
  filter_upwards [vacuumProjection.coeFn_compLp (BochnerClosedOperator.tensor volume a f),
    BochnerClosedOperator.tensor_coeFn volume a f,
    BochnerClosedOperator.tensor_coeFn volume a (inner ℝ gaussianOne f • gaussianOne)]
    with t hp ht hv
  rw [hp, ht, map_smul, hv]
  rfl

theorem meanProjection_deterministic (a : TimeHilbert) :
    meanProjection (productTensor a gaussianOne) = productTensor a gaussianOne := by
  rw [meanProjection_tensor, gaussianOne_inner_self, one_smul]

theorem constant_pastCoefficient (c : ℝ) :
    (pastCoefficient (fun _ : Fin 0 => (0 : ℝ≥0)) (MvPolynomial.C c) : GaussianL2) =
      c • gaussianOne := by
  apply Lp.ext
  filter_upwards [pastCoefficient_coeFn (fun _ : Fin 0 => (0 : ℝ≥0)) (MvPolynomial.C c),
    Lp.coeFn_smul c gaussianOne, gaussianOne_coeFn] with ω hp hs h1
  simp only [hp, MvPolynomial.eval_C, hs, Pi.smul_apply, h1, smul_eq_mul, mul_one]

theorem constant_step_graph (s t : ℝ≥0) (hst : s ≤ t) (c : ℝ) :
    (productTensor (intervalVector s t) (c • gaussianOne), (0 : ProductDerivativeL2)) ∈
      completedGraph := by
  let p : MvPolynomial (Fin 0) ℝ := MvPolynomial.C c
  let r : Fin 0 → ℝ≥0 := fun _ => 0
  have hg : (productTensor (intervalVector s t) (pastCoefficient r p), stepGradient s t r p) ∈
      completedGraph := polynomialGraph.le_topologicalClosure
        (Submodule.subset_span ⟨0, s, t, r, p, (by intro i; exact Fin.elim0 i), hst, rfl⟩)
  have hc : (pastCoefficient r p : GaussianL2) = c • gaussianOne := constant_pastCoefficient c
  have hz : polynomialDerivative (pastCoefficient r p) = 0 := by
    have hd := closedCylindricalDerivative_core_graph (pastCoefficient r p)
    rw [hc] at hd
    exact closedCylindricalDerivative.mem_graph_snd_inj hd (closedDerivative_constant_graph c) rfl
  have hs : stepGradient s t r p = 0 := by
    apply vectorCurry.injective
    change ProductL2Curry.curry volume gaussianProduct
      (ProductL2Curry.productTensor volume gaussianProduct (intervalVector s t)
        (polynomialDerivative (pastCoefficient r p))) = vectorCurry 0
    rw [ProductL2Curry.curry_productTensor, hz, map_zero]
    apply Lp.ext
    filter_upwards [BochnerClosedOperator.tensor_coeFn volume (intervalVector s t)
      (0 : GaussianVectorL2), Lp.coeFn_zero GaussianVectorL2 2 (volume : Measure ℝ)] with x hx h0
    simp [hx, h0]
  rwa [hc, hs] at hg

def meanGraph : TimeProbabilityL2 →L[ℝ] (TimeProbabilityL2 × ProductDerivativeL2) :=
  meanProjection.prod 0

/-- Mean projection turns ambient predictable approximation into graph
approximation because the projected derivative is proved to be zero. -/
theorem meanProjection_graph (u : fullPredictable) :
    (meanProjection u, (0 : ProductDerivativeL2)) ∈ completedGraph := by
  have h : closedProductSteps ≤ completedGraph.comap meanGraph.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro v ⟨z, hz, rfl⟩
      have hh : transportRelation ≤ (completedGraph.comap meanGraph.toLinearMap).comap
          (LinearMap.fst ℝ TimeProbabilityL2 GaussianVectorL2) := by
        apply Submodule.span_le.mpr
        rintro z ⟨n, r, p, s, t, hrs, hst, rfl⟩
        change (meanProjection (productTensor (intervalVector s t) (pastCoefficient r p)),
          (0 : ProductDerivativeL2)) ∈ completedGraph
        rw [meanProjection_tensor]
        exact constant_step_graph s t hst _
      exact hh hz
    · exact polynomialGraph.isClosed_topologicalClosure.preimage meanGraph.continuous
  exact h (closedProductSteps_eq_fullPredictable.symm ▸ u.property)

/-- This subclass is specified by predictability and an actual deterministic
representative, independently of the polynomial graph completion. -/
theorem deterministic_mem_completedGraph (a : TimeHilbert)
    (ha : productTensor a gaussianOne ∈ fullPredictable) :
    (productTensor a gaussianOne, (0 : ProductDerivativeL2)) ∈ completedGraph := by
  simpa only [meanProjection_deterministic] using
    meanProjection_graph ⟨productTensor a gaussianOne, ha⟩

theorem independent_zero_graph_mem_completedGraph (u : TimeProbabilityL2)
    (hu : u ∈ fullPredictable) (hd : (u, (0 : ProductDerivativeL2)) ∈ derivative.graph) :
    (u, (0 : ProductDerivativeL2)) ∈ completedGraph := by
  obtain ⟨a, rfl⟩ := (derivative_zero_iff_deterministic u).mp hd
  exact deterministic_mem_completedGraph a hu

theorem deterministic_integral_derivative (a : TimeHilbert)
    (ha : productTensor a gaussianOne ∈ fullPredictable) :
    (itoIntegral ⟨productTensor a gaussianOne, ha⟩,
      fieldEmbedding (productTensor a gaussianOne)) ∈ closedCylindricalDerivative.graph := by
  simpa only [map_zero, add_zero] using
    completedGraph_sensitivity (deterministic_mem_completedGraph a ha)

end OperatorDerivativeRewrite.Foundation.GaussianDeterministicGraphCore
