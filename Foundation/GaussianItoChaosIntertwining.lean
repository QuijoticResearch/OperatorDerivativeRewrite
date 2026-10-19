import Foundation.GaussianPredictableChaosCore
import Foundation.GaussianChaosLowering
import Foundation.GaussianItoAlternatingProjection

/-! The actual predictable Itô integral raises the Gaussian chaos degree by one.
The proof uses the original closed derivative and adjoint divergence graphs. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianItoChaosIntertwining
open InfiniteGaussian GaussianNumberSectors GaussianChaosLowering
open GaussianTimeProductL2 GaussianTimeHilbert
open GaussianPredictableFull GaussianPredictableAdjoint GaussianPredictableL2Completion
open GaussianPredictableChaosCore GaussianTimeDivergence GaussianContinuousRigidity
open GaussianSensitivityCore
attribute [local instance] timeHilbert_secondCountable
set_option backward.isDefEq.respectTransparency false

theorem projection_pairing (n : ℕ) (f g : GaussianL2) :
    inner ℝ (projection n f) g = inner ℝ f (projection n g) :=
  (sector n).inner_starProjection_left_eq_right f g

/-- No polynomial or finite-coordinate restriction on the input rank-one field. -/
theorem rank_projection_divergence_graph (n : ℕ) (v : CoefficientSpace)
    {f g : GaussianL2} (hg : (scalarTensor v f, g) ∈ hilbertDivergence.graph) :
    (scalarTensor v (projection n f), projection (n + 1) g) ∈ hilbertDivergence.graph := by
  change _ ∈ closedCylindricalDerivative.adjoint.graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint closedCylindricalDerivative_dense_domain]
  apply (Submodule.mem_adjoint_iff _ _).mpr
  intro a b hab
  have hi := graph_duality (projectedGradient_graph (n + 1) a).1 hg
  have hb := component_derivative_intertwining n v hab
  change inner ℝ b (scalarTensor v (projection n f)) - inner ℝ a (projection (n + 1) g) = 0
  apply sub_eq_zero.mpr
  calc
    _ = inner ℝ (projection n f) (component v b) := by
      rw [real_inner_comm, scalarTensor_inner]; rfl
    _ = inner ℝ f (component v (projectedGradient (n + 1) a)) := by
      rw [projection_pairing, ← hb]
    _ = inner ℝ (projectedGradient (n + 1) a) (scalarTensor v f) := by
      exact (scalarTensor_inner v f (projectedGradient (n + 1) a)).symm.trans
        (real_inner_comm _ _)
    _ = inner ℝ (projection (n + 1) a) g := hi
    _ = _ := projection_pairing (n + 1) a g

theorem scalarLift_projection_predictable (n : ℕ) (u : fullPredictable) :
    scalarLift (projection n) u ∈ fullPredictable := by
  have h : closedProductSteps ≤ fullPredictable.comap (scalarLift (projection n)).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rw [productStepSpan, Submodule.map_le_iff_le_comap]
      apply Submodule.span_le.mpr
      rintro z ⟨m, r, p, s, t, hrs, hst, rfl⟩
      change scalarLift (projection n) (productTensor (intervalVector s t) (pastCoefficient r p)) ∈ fullPredictable
      rw [scalarLift_tensor]
      exact past_step_mem_fullPredictable s t _
        (projection_pastPolynomial_measurable n s r hrs p)
    · exact fullPredictable_isClosed.preimage (scalarLift (projection n)).continuous
  have hu : (u : TimeProbabilityL2) ∈ closedProductSteps := by
    rw [closedProductSteps_eq_fullPredictable]
    exact u.property
  exact h hu

def projectedPredictable (n : ℕ) (u : fullPredictable) : fullPredictable :=
  ⟨scalarLift (projection n) u, scalarLift_projection_predictable n u⟩

def projectedDivergenceMap (n : ℕ) : TimeProbabilityL2 →L[ℝ] (GaussianVectorL2 × GaussianL2) :=
  (fieldEmbedding.toContinuousLinearMap.comp (scalarLift (projection n))).prod
    ((projection (n + 1)).comp integralExtension)

theorem projected_divergence_graph (n : ℕ) (u : fullPredictable) :
    (predictableField (projectedPredictable n u), projection (n + 1) (itoIntegral u)) ∈
      hilbertDivergence.graph := by
  have h : closedProductSteps ≤ hilbertDivergence.graph.comap (projectedDivergenceMap n).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rw [productStepSpan, Submodule.map_le_iff_le_comap]
      apply Submodule.span_le.mpr
      rintro z ⟨m, r, p, s, t, hrs, hst, rfl⟩
      change (fieldEmbedding (scalarLift (projection n)
        (productTensor (intervalVector s t) (pastCoefficient r p))),
        projection (n + 1) (integralExtension (pastStep s t r hrs p))) ∈ hilbertDivergence.graph
      rw [scalarLift_tensor, fieldEmbedding_tensor, integralExtension_eq,
        ito_pastStep s t hst]
      exact rank_projection_divergence_graph n _
        (pastCoefficient_hilbertDivergence_graph r p s t hrs hst)
    · exact hilbertDivergence_isClosed.preimage (projectedDivergenceMap n).continuous
  have hu : (u : TimeProbabilityL2) ∈ closedProductSteps := by
    rw [closedProductSteps_eq_fullPredictable]
    exact u.property
  have hg := h hu
  change (fieldEmbedding (scalarLift (projection n) u), projection (n + 1) (integralExtension u)) ∈ hilbertDivergence.graph at hg
  rw [integralExtension_eq] at hg
  exact hg

/-- An equality for the genuine Itô integral on its full predictable L2 domain. -/
theorem integral_projection (n : ℕ) (u : fullPredictable) :
    itoIntegral (projectedPredictable n u) = projection (n + 1) (itoIntegral u) :=
  hilbertDivergence.mem_graph_snd_inj
    (predictableField_divergence_graph (projectedPredictable n u))
    (projected_divergence_graph n u) rfl

/-- The existing causal Hodge operator has the shifted number weights on
integrands, rather than the unshifted output weights. -/
theorem alternating_projection (n : ℕ) (u : fullPredictable) :
    projectedPredictable n (GaussianItoAlternatingProjection.alternatingOperator u) =
      (n + 1 : ℝ)⁻¹ • projectedPredictable n u := by
  apply itoIntegral.injective
  rw [integral_projection, GaussianItoAlternatingProjection.integral_alternating,
    GaussianPotentialIteration.projection_potential, map_smul, integral_projection]
  simp only [Nat.cast_add, Nat.cast_one]

/-- An unconditional full predictable-L2 expansion of the actual regularized
integrand. This is not a fixed-chaos or finite-grid approximation assertion. -/
theorem alternating_hasSum (u : fullPredictable) :
    HasSum (fun n : ℕ => (n + 1 : ℝ)⁻¹ • projectedPredictable n u)
      (GaussianItoAlternatingProjection.alternatingOperator u) := by
  have hs := (GaussianInverseNumberPotential.potential_hasSum (itoIntegral u)).map
    predictableAdjoint.toAddMonoidHom predictableAdjoint.continuous
  change HasSum (fun n : ℕ => predictableAdjoint
    ((n : ℝ)⁻¹ • projection n (itoIntegral u)))
      (predictableAdjoint (GaussianInverseNumberPotential.potentialOperator (itoIntegral u))) at hs
  have ht := (hasSum_nat_add_iff' 1).mpr hs
  simp only [Finset.sum_range_one, Nat.cast_zero, inv_zero, zero_smul, map_zero,
    sub_zero] at ht
  have he (n : ℕ) : predictableAdjoint
      (((n + 1 : ℕ) : ℝ)⁻¹ • projection (n + 1) (itoIntegral u)) =
      (n + 1 : ℝ)⁻¹ • projectedPredictable n u := by
    rw [map_smul, ← integral_projection, predictableAdjoint_integral]
    simp only [Nat.cast_add, Nat.cast_one]
  simpa only [he, ← GaussianItoAlternatingProjection.alternating_apply] using ht

end OperatorDerivativeRewrite.Foundation.GaussianItoChaosIntertwining
