import Foundation.GaussianDeterministicGraphCore

/-! Identification of the actual predictable integral on deterministic profiles,
and its full closed derivative. This is first-chaos representation, not full PRP. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianDeterministicIntegral
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProductL2 GaussianPredictableFull
open GaussianContinuousRigidity GaussianDeterministicGraphCore GaussianTimePolynomialPairing
open SeparableHilbertEmbedding GaussianPredictableAdjoint
attribute [local instance] timeHilbert_secondCountable

theorem firstChaos_closedDerivative_graph (a : TimeHilbert) :
    (GaussianHilbertProcess.isonormalEmbedding TimeHilbert a,
      fieldEmbedding (productTensor a gaussianOne)) ∈ closedCylindricalDerivative.graph := by
  have h := closedCylindricalDerivative_core_graph
    (firstChaosPolynomial (hilbertEmbedding TimeHilbert a))
  have hf : (firstChaosPolynomial (hilbertEmbedding TimeHilbert a) : GaussianL2) =
      GaussianHilbertProcess.isonormalEmbedding TimeHilbert a :=
    Lp.ext (firstChaosPolynomial_coeFn _)
  have hd : polynomialDerivative (firstChaosPolynomial (hilbertEmbedding TimeHilbert a)) =
      fieldEmbedding (productTensor a gaussianOne) := by
    rw [fieldEmbedding_tensor]
    apply Lp.ext
    filter_upwards [firstChaosPolynomial_derivative_coeFn (hilbertEmbedding TimeHilbert a),
      scalarTensor_coeFn (hilbertEmbedding TimeHilbert a) gaussianOne, gaussianOne_coeFn]
      with ω hd hs h1
    rw [hd, hs, h1, one_smul]
  rwa [hf, hd] at h

/-- Equal full derivatives and equal means determine a Gaussian L2 class. -/
theorem eq_of_same_derivative_mean (f g : GaussianL2) (v : GaussianVectorL2)
    (hf : (f, v) ∈ closedCylindricalDerivative.graph)
    (hg : (g, v) ∈ closedCylindricalDerivative.graph)
    (hm : inner ℝ gaussianOne f = inner ℝ gaussianOne g) : f = g := by
  have hz : (f-g, (0 : GaussianVectorL2)) ∈ closedCylindricalDerivative.graph := by
    simpa only [Prod.mk_sub_mk, sub_self] using closedCylindricalDerivative.graph.sub_mem hf hg
  have he := (closedDerivative_zero_iff_vacuum (f-g)).mp hz
  rw [inner_sub_right, hm, sub_self, zero_smul] at he
  exact sub_eq_zero.mp he

/-- The constructed stochastic integral equals the pre-existing isonormal
Gaussian variable, for every deterministic profile in its genuine predictable domain. -/
theorem itoIntegral_deterministic (a : TimeHilbert)
    (ha : productTensor a gaussianOne ∈ fullPredictable) :
    itoIntegral ⟨productTensor a gaussianOne, ha⟩ =
      GaussianHilbertProcess.isonormalEmbedding TimeHilbert a := by
  apply eq_of_same_derivative_mean _ _ _ (deterministic_integral_derivative a ha)
    (firstChaos_closedDerivative_graph a)
  rw [gaussianOne_inner_eq_integral, gaussianOne_inner_eq_integral,
    itoIntegral_centered]
  exact (GaussianHilbertProcess.isonormal_integral a).symm

theorem predictableAdjoint_deterministic_firstChaos (a : TimeHilbert)
    (ha : productTensor a gaussianOne ∈ fullPredictable) :
    predictableAdjoint (GaussianHilbertProcess.isonormalEmbedding TimeHilbert a) =
      ⟨productTensor a gaussianOne, ha⟩ := by
  rw [← itoIntegral_deterministic a ha, predictableAdjoint_integral]

/-- Actual first-chaos Clark--Ocone on the stated deterministic predictable range. -/
theorem firstChaos_reconstruction (a : TimeHilbert)
    (ha : productTensor a gaussianOne ∈ fullPredictable) :
    itoIntegral (predictableProjection (fieldEmbedding (productTensor a gaussianOne))) =
      GaussianHilbertProcess.isonormalEmbedding TimeHilbert a := by
  let F : closedCylindricalDerivative.domain :=
    ⟨GaussianHilbertProcess.isonormalEmbedding TimeHilbert a,
      LinearPMap.mem_domain_iff.mpr ⟨_, firstChaos_closedDerivative_graph a⟩⟩
  have hv : closedCylindricalDerivative F = fieldEmbedding (productTensor a gaussianOne) :=
    closedCylindricalDerivative.mem_graph_snd_inj (closedCylindricalDerivative.mem_graph F)
      (firstChaos_closedDerivative_graph a) rfl
  have hp := predictableAdjoint_eq_projected_derivative F
  rw [hv] at hp
  rw [← hp, predictableAdjoint_deterministic_firstChaos a ha, itoIntegral_deterministic]

end OperatorDerivativeRewrite.Foundation.GaussianDeterministicIntegral
