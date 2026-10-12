import Foundation.GaussianPastFirstChaos

/-! Independent predictable first-chaos fields lie in the actual adapted
polynomial graph completion. Bounded projection controls BOTH graph coordinates;
ambient predictable density alone is not asserted to imply full graph density. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianFirstChaosGraphCore
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProcess GaussianTimeDivergence
open GaussianTimeProductL2 GaussianProductDerivative GaussianPredictableFull
open GaussianAdaptedGraphCore GaussianContinuousRigidity GaussianPredictableL2Completion
open GaussianBrownianSobolevField GaussianPastFirstChaos
attribute [local instance] timeHilbert_secondCountable coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def fieldProjection : TimeProbabilityL2 →L[ℝ] TimeProbabilityL2 :=
  scalarCurry.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((projection.compLpL 2 volume).comp scalarCurry.toLinearIsometry.toContinuousLinearMap)

theorem fieldProjection_tensor (a : TimeHilbert) (f : GaussianL2) :
    fieldProjection (productTensor a f) = productTensor a (projection f) := by
  apply scalarCurry.injective
  change scalarCurry (scalarCurry.symm (projection.compLp (scalarCurry _))) = _
  rw [scalarCurry.apply_symm_apply, scalarCurry_productTensor, scalarCurry_productTensor]
  apply Lp.ext
  filter_upwards [projection.coeFn_compLp (BochnerClosedOperator.tensor volume a f),
    BochnerClosedOperator.tensor_coeFn volume a f,
    BochnerClosedOperator.tensor_coeFn volume a (projection f)] with t hp ht hv
  rw [hp, ht, map_smul, hv]

theorem productTensor_sum_smul {ι : Type*} [Fintype ι]
    (a : TimeHilbert) (c : ι → ℝ) (f : ι → GaussianL2) :
    productTensor a (∑ i, c i • f i) = ∑ i, c i • productTensor a (f i) := by
  apply scalarCurry.injective
  simp only [map_sum, map_smul, scalarCurry_productTensor]
  apply Lp.ext
  filter_upwards [BochnerClosedOperator.tensor_coeFn volume a (∑ i, c i • f i),
    Lp.coeFn_finsetSum Finset.univ (fun i => c i • BochnerClosedOperator.tensor volume a (f i)),
    ae_all_iff.mpr (fun i => Lp.coeFn_smul (c i) (BochnerClosedOperator.tensor volume a (f i))),
    ae_all_iff.mpr (fun i => BochnerClosedOperator.tensor_coeFn volume a (f i))]
    with t ht hs hsm hf
  rw [ht, hs, Finset.smul_sum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hsm i, Pi.smul_apply, hf i, smul_smul, smul_smul, mul_comm]

theorem wiener_step_graph (r s t : ℝ≥0) (hrs : r ≤ s) (hst : s ≤ t) :
    (productTensor (intervalVector s t) (wienerL2 r),
      fieldFirstChaosGradient (productTensor (intervalVector s t) (wienerL2 r))) ∈
        completedGraph := by
  have he : (pastCoefficient (fun _ : Fin 1 => r) (MvPolynomial.X 0) : GaussianL2) =
      wienerL2 r := by
    apply Lp.ext
    filter_upwards [pastCoefficient_coeFn (fun _ : Fin 1 => r) (MvPolynomial.X 0)] with ω hω
    calc
      _ = process r ω := by simpa only [MvPolynomial.eval_X] using hω
      _ = _ := rfl
  simpa only [he] using linear_past_step_graph r s t hrs hst

theorem projected_past_step_graph {n : ℕ} (s t : ℝ≥0) (r : Fin n → ℝ≥0)
    (hrs : ∀ i, r i ≤ s) (hst : s ≤ t) (p : MvPolynomial (Fin n) ℝ) :
    (fieldProjection (productTensor (intervalVector s t) (pastCoefficient r p)),
      fieldFirstChaosGradient
        (fieldProjection (productTensor (intervalVector s t) (pastCoefficient r p)))) ∈
          completedGraph := by
  rw [fieldProjection_tensor, projection_pastPolynomial, productTensor_sum_smul]
  simp only [map_sum, map_smul, prod_mk_sum]
  exact completedGraph.sum_mem (fun i _ => completedGraph.smul_mem _
    (wiener_step_graph (r i) s t (hrs i) hst))

def projectedGraph : TimeProbabilityL2 →L[ℝ] (TimeProbabilityL2 × ProductDerivativeL2) :=
  fieldProjection.prod (fieldFirstChaosGradient.comp fieldProjection)

/-- The bounded first-chaos projection sends every independently predictable
field to a genuine adapted graph pair. Both limits use the same approximants. -/
theorem fieldProjection_graph (u : fullPredictable) :
    (fieldProjection u, fieldFirstChaosGradient (fieldProjection u)) ∈ completedGraph := by
  have h : closedProductSteps ≤ completedGraph.comap projectedGraph.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro v ⟨z, hz, rfl⟩
      have hh : transportRelation ≤ (completedGraph.comap projectedGraph.toLinearMap).comap
          (LinearMap.fst ℝ TimeProbabilityL2 GaussianVectorL2) := by
        apply Submodule.span_le.mpr
        rintro z ⟨n, r, p, s, t, hrs, hst, rfl⟩
        exact projected_past_step_graph s t r hrs hst p
      exact hh hz
    · exact polynomialGraph.isClosed_topologicalClosure.preimage projectedGraph.continuous
  exact h (closedProductSteps_eq_fullPredictable.symm ▸ u.property)

/-- Slice membership in the actual first-chaos range is an independent
condition; it does not mention a derivative or adapted graph approximation. -/
theorem fieldProjection_eq_of_firstChaos_slices (u : TimeProbabilityL2)
    (hu : ∀ᵐ t ∂volume, scalarCurry u t ∈ firstChaosEmbedding.toLinearMap.range) :
    fieldProjection u = u := by
  apply scalarCurry.injective
  change scalarCurry (scalarCurry.symm (projection.compLp (scalarCurry u))) = scalarCurry u
  rw [scalarCurry.apply_symm_apply]
  apply Lp.ext
  filter_upwards [projection.coeFn_compLp (scalarCurry u), hu] with t hp ht
  rw [hp]
  exact (HilbertRepresentation.representationProjection_eq_self_iff firstChaosEmbedding _).mpr ht

theorem firstChaos_slices_mem_completedGraph (u : fullPredictable)
    (hu : ∀ᵐ t ∂volume, scalarCurry (u : TimeProbabilityL2) t ∈
      firstChaosEmbedding.toLinearMap.range) :
    ((u : TimeProbabilityL2), fieldFirstChaosGradient u) ∈ completedGraph := by
  simpa only [fieldProjection_eq_of_firstChaos_slices u hu] using fieldProjection_graph u

theorem firstChaos_slices_mem_independentSobolev (u : fullPredictable)
    (hu : ∀ᵐ t ∂volume, scalarCurry (u : TimeProbabilityL2) t ∈
      firstChaosEmbedding.toLinearMap.range) :
    (u : TimeProbabilityL2) ∈ predictableSobolev :=
  completedGraph_mem_predictableSobolev (firstChaos_slices_mem_completedGraph u hu)

theorem firstChaos_slices_sensitivity (u : fullPredictable)
    (hu : ∀ᵐ t ∂volume, scalarCurry (u : TimeProbabilityL2) t ∈
      firstChaosEmbedding.toLinearMap.range) :
    (itoIntegral u, fieldEmbedding u + GaussianSensitivityIntegral.correction
      (fieldFirstChaosGradient u)) ∈ closedCylindricalDerivative.graph :=
  completedGraph_sensitivity (firstChaos_slices_mem_completedGraph u hu)

theorem firstChaos_slices_rigidity (u : fullPredictable)
    (hu : ∀ᵐ t ∂volume, scalarCurry (u : TimeProbabilityL2) t ∈
      firstChaosEmbedding.toLinearMap.range) :
    (itoIntegral u, fieldEmbedding u) ∈ closedCylindricalDerivative.graph ↔
      ∃ a : TimeHilbert, (u : TimeProbabilityL2) = productTensor a gaussianOne :=
  rigidity_graph (firstChaos_slices_mem_completedGraph u hu)

theorem firstChaos_slices_gradient_norm (u : TimeProbabilityL2)
    (hu : ∀ᵐ t ∂volume, scalarCurry u t ∈ firstChaosEmbedding.toLinearMap.range) :
    ‖fieldFirstChaosGradient u‖ = ‖u‖ := by
  have he : vectorCurry (fieldFirstChaosGradient u) =
      firstChaosGradient.compLp (scalarCurry u) := vectorCurry.apply_symm_apply _
  rw [← vectorCurry.norm_map, he, ← scalarCurry.norm_map u, Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [firstChaosGradient.coeFn_compLp (scalarCurry u), hu] with t ht hu
  rw [ht]
  obtain ⟨h, hh⟩ := hu
  rw [← hh]
  exact firstChaosGradient_norm h

theorem firstChaos_slices_correction_norm (u : fullPredictable)
    (hu : ∀ᵐ t ∂volume, scalarCurry (u : TimeProbabilityL2) t ∈
      firstChaosEmbedding.toLinearMap.range) :
    ‖GaussianSensitivityIntegral.correction (fieldFirstChaosGradient u)‖ = ‖u‖ := by
  rw [GaussianSensitivityCore.completedGraph_correction_norm
    (z := ((u : TimeProbabilityL2), fieldFirstChaosGradient u))
    (firstChaos_slices_mem_completedGraph u hu), firstChaos_slices_gradient_norm u hu]
  rfl

/-- A centered first-chaos predictable field is deterministic precisely when
it vanishes. Here this follows quantitatively from the actual sensitivity. -/
theorem firstChaos_slices_rigidity_zero (u : fullPredictable)
    (hu : ∀ᵐ t ∂volume, scalarCurry (u : TimeProbabilityL2) t ∈
      firstChaosEmbedding.toLinearMap.range) :
    (itoIntegral u, fieldEmbedding u) ∈ closedCylindricalDerivative.graph ↔ u = 0 := by
  constructor
  · intro hg
    have he := closedCylindricalDerivative.mem_graph_snd_inj
      (firstChaos_slices_sensitivity u hu) hg rfl
    have hz : GaussianSensitivityIntegral.correction (fieldFirstChaosGradient u) = 0 :=
      add_left_cancel (he.trans (add_zero _).symm)
    have hn := firstChaos_slices_correction_norm u hu
    rw [hz, norm_zero] at hn
    exact norm_eq_zero.mp hn.symm
  · rintro rfl
    simp only [Submodule.coe_zero, map_zero]
    exact closedCylindricalDerivative.graph.zero_mem

end OperatorDerivativeRewrite.Foundation.GaussianFirstChaosGraphCore
