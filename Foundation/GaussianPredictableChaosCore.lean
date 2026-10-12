import Foundation.GaussianChaosCylinders
import Foundation.BochnerL2Dominated

/-! All-order chaos approximation in the independently defined predictable
Sobolev graph. No predictability or derivative convergence is assumed for the approximants. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianPredictableChaosCore
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProductL2 GaussianProductDerivative
open GaussianPredictableFull GaussianAdaptedGraphCore GaussianTimeDivergence
open GaussianPredictableL2Completion GaussianNumberSectors
attribute [local instance] timeHilbert_secondCountable coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def scalarLift (L : GaussianL2 →L[ℝ] GaussianL2) : TimeProbabilityL2 →L[ℝ] TimeProbabilityL2 :=
  scalarCurry.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((L.compLpL 2 volume).comp scalarCurry.toLinearIsometry.toContinuousLinearMap)

def gradientLift (L : GaussianL2 →L[ℝ] GaussianVectorL2) :
    TimeProbabilityL2 →L[ℝ] ProductDerivativeL2 :=
  vectorCurry.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((L.compLpL 2 volume).comp scalarCurry.toLinearIsometry.toContinuousLinearMap)

theorem scalarLift_tensor (L : GaussianL2 →L[ℝ] GaussianL2) (a : TimeHilbert) (f : GaussianL2) :
    scalarLift L (productTensor a f) = productTensor a (L f) := by
  apply scalarCurry.injective
  change scalarCurry (scalarCurry.symm (L.compLp (scalarCurry _))) = _
  rw [scalarCurry.apply_symm_apply, scalarCurry_productTensor, scalarCurry_productTensor]
  apply Lp.ext
  filter_upwards [L.coeFn_compLp (BochnerClosedOperator.tensor volume a f),
    BochnerClosedOperator.tensor_coeFn volume a f,
    BochnerClosedOperator.tensor_coeFn volume a (L f)] with t hp ht hv
  rw [hp, ht, map_smul, hv]

theorem gradientLift_tensor (L : GaussianL2 →L[ℝ] GaussianVectorL2)
    (a : TimeHilbert) (f : GaussianL2) :
    gradientLift L (productTensor a f) = ProductL2Curry.productTensor volume gaussianProduct a (L f) := by
  apply vectorCurry.injective
  change vectorCurry (vectorCurry.symm (L.compLp (scalarCurry _))) =
    ProductL2Curry.curry volume gaussianProduct _
  rw [vectorCurry.apply_symm_apply, scalarCurry_productTensor, ProductL2Curry.curry_productTensor]
  apply Lp.ext
  filter_upwards [L.coeFn_compLp (BochnerClosedOperator.tensor volume a f),
    BochnerClosedOperator.tensor_coeFn volume a f,
    BochnerClosedOperator.tensor_coeFn volume a (L f)] with t hp ht hv
  rw [hp, ht, map_smul, hv]

theorem projected_step_graph (n : ℕ) {m : ℕ} (s t : ℝ≥0) (r : Fin m → ℝ≥0)
    (hrs : ∀ i, r i ≤ s) (hst : s ≤ t) (p : MvPolynomial (Fin m) ℝ) :
    (scalarLift (projection n) (productTensor (intervalVector s t) (pastCoefficient r p)),
      gradientLift (projectedGradient n) (productTensor (intervalVector s t) (pastCoefficient r p))) ∈
        completedGraph := by
  obtain ⟨q, hq⟩ := projection_polynomial n
    (fun i => SeparableHilbertEmbedding.hilbertEmbedding TimeHilbert (timeVector (r i))) p
  change projection n (pastCoefficient r p) = (pastCoefficient r q : GaussianL2) at hq
  have hd : projectedGradient n (pastCoefficient r p) = polynomialDerivative (pastCoefficient r q) := by
    have hg := (projectedGradient_graph n (pastCoefficient r p)).1
    rw [hq] at hg
    exact closedCylindricalDerivative.mem_graph_snd_inj hg
      (closedCylindricalDerivative_core_graph (pastCoefficient r q)) rfl
  rw [scalarLift_tensor, gradientLift_tensor, hq, hd]
  exact polynomialGraph.le_topologicalClosure
    (Submodule.subset_span ⟨m, s, t, r, q, hrs, hst, rfl⟩)

def projectedGraph (n : ℕ) : TimeProbabilityL2 →L[ℝ] (TimeProbabilityL2 × ProductDerivativeL2) :=
  (scalarLift (projection n)).prod (gradientLift (projectedGradient n))

theorem projected_field_graph (n : ℕ) (u : fullPredictable) :
    (scalarLift (projection n) u, gradientLift (projectedGradient n) u) ∈ completedGraph := by
  have h : closedProductSteps ≤ completedGraph.comap (projectedGraph n).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro v ⟨z, hz, rfl⟩
      have hh : transportRelation ≤ (completedGraph.comap (projectedGraph n).toLinearMap).comap
          (LinearMap.fst ℝ TimeProbabilityL2 GaussianVectorL2) := by
        apply Submodule.span_le.mpr
        rintro z ⟨m, r, p, s, t, hrs, hst, rfl⟩
        exact projected_step_graph n s t r hrs hst p
      exact hh hz
    · exact polynomialGraph.isClosed_topologicalClosure.preimage (projectedGraph n).continuous
  exact h (closedProductSteps_eq_fullPredictable.symm ▸ u.property)

private theorem compLp_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ℕ) (L : ℕ → GaussianL2 →L[ℝ] E) (u : Lp GaussianL2 2 (volume : Measure ℝ)) :
    (∑ n ∈ s, L n).compLp u = ∑ n ∈ s, (L n).compLp u := by
  apply Lp.ext
  filter_upwards [(∑ n ∈ s, L n).coeFn_compLp u,
    Lp.coeFn_finsetSum s (fun n => (L n).compLp u),
    ae_all_iff.mpr (fun n => (L n).coeFn_compLp u)] with t ht hs hn
  simp only [ht, hs, ContinuousLinearMap.sum_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun n _ => (hn n).symm)

theorem scalarLift_sum (s : Finset ℕ) (L : ℕ → GaussianL2 →L[ℝ] GaussianL2)
    (u : TimeProbabilityL2) : scalarLift (∑ n ∈ s, L n) u = ∑ n ∈ s, scalarLift (L n) u := by
  change scalarCurry.symm ((∑ n ∈ s, L n).compLp (scalarCurry u)) = _
  rw [compLp_sum, map_sum]
  rfl

theorem gradientLift_sum (s : Finset ℕ) (L : ℕ → GaussianL2 →L[ℝ] GaussianVectorL2)
    (u : TimeProbabilityL2) : gradientLift (∑ n ∈ s, L n) u = ∑ n ∈ s, gradientLift (L n) u := by
  change vectorCurry.symm ((∑ n ∈ s, L n).compLp (scalarCurry u)) = _
  rw [compLp_sum, map_sum]
  rfl

theorem truncated_field_graph (N : ℕ) (u : fullPredictable) :
    (scalarLift (truncation N) u, gradientLift (gradientTruncation N) u) ∈ completedGraph := by
  rw [truncation, gradientTruncation, scalarLift_sum, gradientLift_sum, prod_mk_sum]
  exact completedGraph.sum_mem (fun n _ => projected_field_graph n u)

theorem scalar_truncation_norm_le (N : ℕ) (f : GaussianL2) : ‖truncation N f‖ ≤ ‖f‖ := by
  have he := sector_orthogonalFamily.norm_sum
    (fun n => (sector n).orthogonalProjectionOnto f) (Finset.range (N + 1))
  have hn (n : ℕ) : ‖(sector n).orthogonalProjectionOnto f‖ = ‖projection n f‖ := rfl
  have hp (n : ℕ) : (sector n).subtypeₗᵢ ((sector n).orthogonalProjectionOnto f) =
      projection n f := rfl
  simp only [hp, hn] at he
  have hs := (projection_hasSum_norm_sq f).summable.sum_le_tsum
    (Finset.range (N + 1)) (fun n _ => sq_nonneg ‖projection n f‖)
  rw [(projection_hasSum_norm_sq f).tsum_eq, ← he] at hs
  rw [truncation, ContinuousLinearMap.sum_apply]
  nlinarith [norm_nonneg (∑ n ∈ Finset.range (N + 1), projection n f), norm_nonneg f]

theorem gradient_truncation_norm_le {f : GaussianL2} {g : GaussianVectorL2}
    (hf : (f, g) ∈ closedCylindricalDerivative.graph) (N : ℕ) :
    ‖gradientTruncation N f‖ ≤ ‖g‖ := by
  have he := projectedGradient_sum_energy f (Finset.range (N + 1))
  have hb := projectedGradient_finite_bound hf (Finset.range (N + 1))
  rw [← he] at hb
  rw [gradientTruncation, ContinuousLinearMap.sum_apply]
  nlinarith [norm_nonneg (∑ n ∈ Finset.range (N + 1), projectedGradient n f), norm_nonneg g]

theorem field_graph_truncation_tendsto {u : TimeProbabilityL2} {v : ProductDerivativeL2}
    (hu : (u, v) ∈ derivative.graph) :
    Tendsto (fun N => (scalarLift (truncation N) u, gradientLift (gradientTruncation N) u))
      atTop (𝓝 (u, v)) := by
  have hf := (derivative_fiber_graph_iff u v).mp hu
  have hs : Tendsto (fun N => (truncation N).compLp (scalarCurry u)) atTop (𝓝 (scalarCurry u)) := by
    apply BochnerL2Dominated.tendsto_of_ae_norm_bound
    · intro N
      filter_upwards [(truncation N).coeFn_compLp (scalarCurry u)] with t ht
      rw [ht]
      exact scalar_truncation_norm_le N _
    · filter_upwards [ae_all_iff.mpr (fun N => (truncation N).coeFn_compLp (scalarCurry u))]
        with t ht
      simp only [ht]
      exact truncation_tendsto _
  have hv : Tendsto (fun N => (gradientTruncation N).compLp (scalarCurry u))
      atTop (𝓝 (vectorCurry v)) := by
    apply BochnerL2Dominated.tendsto_of_ae_norm_bound
    · intro N
      filter_upwards [(gradientTruncation N).coeFn_compLp (scalarCurry u), hf] with t ht hf
      rw [ht]
      exact gradient_truncation_norm_le hf N
    · filter_upwards [ae_all_iff.mpr (fun N => (gradientTruncation N).coeFn_compLp (scalarCurry u)), hf]
        with t ht hf
      simp only [ht]
      exact (simultaneous_graph_tendsto hf).snd_nhds
  have hs' := scalarCurry.symm.continuous.continuousAt.tendsto.comp hs
  have hv' := vectorCurry.symm.continuous.continuousAt.tendsto.comp hv
  change Tendsto (fun N => (scalarCurry.symm ((truncation N).compLp (scalarCurry u)),
    vectorCurry.symm ((gradientTruncation N).compLp (scalarCurry u)))) atTop (𝓝 (u, v))
  simpa only [Function.comp_def, scalarCurry.symm_apply_apply, vectorCurry.symm_apply_apply] using
    hs'.prodMk_nhds hv'

/-- The previously missing inclusion, under the ORIGINAL independent graph
and predictability hypotheses. No chaos cutoff or approximation is assumed. -/
theorem independent_graph_mem_completed {u : TimeProbabilityL2} {v : ProductDerivativeL2}
    (hu : u ∈ fullPredictable) (hd : (u, v) ∈ derivative.graph) :
    (u, v) ∈ completedGraph :=
  polynomialGraph.isClosed_topologicalClosure.mem_of_tendsto (field_graph_truncation_tendsto hd)
    (Eventually.of_forall (fun N => truncated_field_graph N ⟨u, hu⟩))

theorem completedGraph_iff_independent (u : TimeProbabilityL2) (v : ProductDerivativeL2) :
    (u, v) ∈ completedGraph ↔ u ∈ fullPredictable ∧ (u, v) ∈ derivative.graph :=
  ⟨fun h => ⟨completedGraph_predictable h, completedGraph_le_derivative h⟩,
    fun h => independent_graph_mem_completed h.1 h.2⟩

theorem independent_derivative_causal {u : TimeProbabilityL2} {v : ProductDerivativeL2}
    (hu : u ∈ fullPredictable) (hd : (u, v) ∈ derivative.graph) : v ∈ causalValues :=
  completedGraph_causal (independent_graph_mem_completed hu hd)

theorem completedGraph_eq_independent : completedGraph =
    derivative.graph ⊓ fullPredictable.comap
      (LinearMap.fst ℝ TimeProbabilityL2 ProductDerivativeL2) := by
  ext z
  exact (completedGraph_iff_independent z.1 z.2).trans and_comm

theorem exists_polynomial_graph_sequence {u : TimeProbabilityL2} {v : ProductDerivativeL2}
    (hu : u ∈ fullPredictable) (hd : (u, v) ∈ derivative.graph) :
    ∃ z : ℕ → TimeProbabilityL2 × ProductDerivativeL2,
      (∀ n, z n ∈ polynomialGraph) ∧ Tendsto z atTop (𝓝 (u, v)) :=
  mem_closure_iff_seq_limit.mp (independent_graph_mem_completed hu hd)

theorem independent_sensitivity_graph (u : fullPredictable) (v : ProductDerivativeL2)
    (hd : ((u : TimeProbabilityL2), v) ∈ derivative.graph) :
    (itoIntegral u, GaussianContinuousRigidity.fieldEmbedding u +
      GaussianSensitivityIntegral.correction v) ∈ closedCylindricalDerivative.graph :=
  GaussianContinuousRigidity.completedGraph_sensitivity
    (independent_graph_mem_completed u.property hd)

def independentIntegralDomain (u : fullPredictable) (v : ProductDerivativeL2)
    (hd : ((u : TimeProbabilityL2), v) ∈ derivative.graph) : closedCylindricalDerivative.domain :=
  ⟨itoIntegral u, LinearPMap.mem_domain_iff.mpr ⟨_, independent_sensitivity_graph u v hd⟩⟩

theorem independent_sensitivity_value (u : fullPredictable) (v : ProductDerivativeL2)
    (hd : ((u : TimeProbabilityL2), v) ∈ derivative.graph) :
    closedCylindricalDerivative (independentIntegralDomain u v hd) =
      GaussianContinuousRigidity.fieldEmbedding u + GaussianSensitivityIntegral.correction v :=
  closedCylindricalDerivative.mem_graph_snd_inj
    (closedCylindricalDerivative.mem_graph (independentIntegralDomain u v hd))
    (independent_sensitivity_graph u v hd) rfl

theorem independent_sensitivity_norm (u : fullPredictable) (v : ProductDerivativeL2)
    (hd : ((u : TimeProbabilityL2), v) ∈ derivative.graph) :
    ‖closedCylindricalDerivative (independentIntegralDomain u v hd) -
      GaussianContinuousRigidity.fieldEmbedding u‖ = ‖v‖ := by
  rw [independent_sensitivity_value, add_sub_cancel_left]
  exact GaussianSensitivityCore.completedGraph_correction_norm
    (z := ((u : TimeProbabilityL2), v)) (independent_graph_mem_completed u.property hd)

theorem independent_rigidity (u : fullPredictable) (v : ProductDerivativeL2)
    (hd : ((u : TimeProbabilityL2), v) ∈ derivative.graph) :
    closedCylindricalDerivative (independentIntegralDomain u v hd) =
      GaussianContinuousRigidity.fieldEmbedding u ↔
        ∃ a : TimeHilbert, (u : TimeProbabilityL2) = productTensor a gaussianOne :=
  GaussianContinuousRigidity.rigidity_value (independent_graph_mem_completed u.property hd)

end OperatorDerivativeRewrite.Foundation.GaussianPredictableChaosCore
