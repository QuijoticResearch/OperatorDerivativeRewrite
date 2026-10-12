import Foundation.GaussianTimePolynomialPairing
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Isometric completion of actual polynomial predictable time integrals

The domain is explicitly the closed span of the constructed elementary time
fields. It is not assumed to equal the entire predictable L² space. The
extension is constructed by a proved isometry and remains in the existing
closed divergence graph.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OperatorDerivativeRewrite.Foundation.GaussianPolynomialStepCompletion

open InfiniteGaussian GaussianTimePolynomialPairing

/-- The field components of the actual finite polynomial time-step graph. -/
def elementaryFields : Submodule ℝ GaussianVectorL2 :=
  elementaryTimeGraph.map (LinearMap.fst ℝ GaussianVectorL2 GaussianL2)

/-- The closed polynomial time-field span, with its actual ambient L² norm. -/
def completedFields : Submodule ℝ GaussianVectorL2 := elementaryFields.topologicalClosure

/-- Field assembly into its closed span; no decomposition is chosen. -/
def fieldAssembly : elementaryTimeGraph →ₗ[ℝ] completedFields where
  toFun z := ⟨z.val.1, elementaryFields.le_topologicalClosure
    (Submodule.mem_map.mpr ⟨z.val, z.property, rfl⟩)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Integral assembly is the actual value component of the elementary graph. -/
def integralAssembly : elementaryTimeGraph →ₗ[ℝ] GaussianL2 :=
  (LinearMap.snd ℝ GaussianVectorL2 GaussianL2).comp elementaryTimeGraph.subtype

theorem fieldAssembly_dense : DenseRange fieldAssembly := by
  have hd : DenseRange (Submodule.inclusion elementaryFields.le_topologicalClosure) :=
    (denseRange_inclusion_iff elementaryFields.le_topologicalClosure).2 (by
      intro x hx
      exact hx)
  apply hd.mono
  rintro x ⟨u, rfl⟩
  obtain ⟨z, hz, he⟩ := Submodule.mem_map.mp u.property
  exact ⟨⟨z, hz⟩, Subtype.ext he⟩

theorem integralAssembly_norm (z : elementaryTimeGraph) :
    ‖integralAssembly z‖ = ‖fieldAssembly z‖ :=
  elementaryTimeGraph_norm z.val z.property

/-- Constructed isometric integral on the closed polynomial time-field span. -/
def completedIntegral : completedFields →ₗᵢ[ℝ] GaussianL2 :=
  integralAssembly.extendOfIsometry fieldAssembly_dense integralAssembly_norm

theorem completedIntegral_assembly (z : elementaryTimeGraph) :
    completedIntegral (fieldAssembly z) = integralAssembly z :=
  integralAssembly.extendOfIsometry_eq fieldAssembly_dense integralAssembly_norm z

theorem completedIntegral_norm (u : completedFields) : ‖completedIntegral u‖ = ‖u‖ :=
  completedIntegral.norm_map u

/-- The completion is a genuine graph limit of elementary stochastic integrals. -/
theorem completedIntegral_graphClosure (u : completedFields) :
    ((u : GaussianVectorL2), completedIntegral u) ∈ elementaryTimeGraph.topologicalClosure := by
  have hc : IsClosed {v : completedFields |
      ((v : GaussianVectorL2), completedIntegral v) ∈ elementaryTimeGraph.topologicalClosure} :=
    elementaryTimeGraph.isClosed_topologicalClosure.preimage
      (continuous_subtype_val.prodMk completedIntegral.continuous)
  exact fieldAssembly_dense.induction_on u hc (fun z => by
    rw [completedIntegral_assembly]
    exact elementaryTimeGraph.le_topologicalClosure z.property)

theorem elementaryTimeGraph_closure_le_divergence :
    elementaryTimeGraph.topologicalClosure ≤ hilbertDivergence.graph :=
  elementaryTimeGraph.topologicalClosure_minimal elementaryTimeGraph_le_hilbertDivergence_graph
    hilbertDivergence_isClosed

/-- Domain membership and value in the pre-existing full Gaussian adjoint. -/
theorem completedIntegral_hilbertDivergence_graph (u : completedFields) :
    ((u : GaussianVectorL2), completedIntegral u) ∈ hilbertDivergence.graph :=
  elementaryTimeGraph_closure_le_divergence (completedIntegral_graphClosure u)

theorem completedFields_le_divergence_domain : completedFields ≤ hilbertDivergence.domain := by
  intro u hu
  exact LinearPMap.mem_domain_iff.mpr ⟨completedIntegral ⟨u, hu⟩,
    completedIntegral_hilbertDivergence_graph ⟨u, hu⟩⟩

theorem completedIntegral_eq_divergence (u : completedFields)
    (hu : (u : GaussianVectorL2) ∈ hilbertDivergence.domain) :
    completedIntegral u = hilbertDivergence ⟨u, hu⟩ :=
  hilbertDivergence.mem_graph_snd_inj (completedIntegral_hilbertDivergence_graph u)
    (hilbertDivergence.mem_graph _) rfl

/-- The completed integral as an actual partial operator on the ambient field space. -/
def completedOperator : GaussianVectorL2 →ₗ.[ℝ] GaussianL2 where
  domain := completedFields
  toFun := completedIntegral.toLinearMap

/-- Both directions: the completed operator graph is exactly the elementary graph closure. -/
theorem completedOperator_graph :
    completedOperator.graph = elementaryTimeGraph.topologicalClosure := by
  apply le_antisymm
  · rintro z hz
    obtain ⟨u, rfl⟩ := completedOperator.mem_graph_iff'.mp hz
    exact completedIntegral_graphClosure u
  · intro z hz
    have hf : elementaryTimeGraph.topologicalClosure ≤
        completedFields.comap (LinearMap.fst ℝ GaussianVectorL2 GaussianL2) := by
      apply elementaryTimeGraph.topologicalClosure_minimal
      · intro w hw
        exact elementaryFields.le_topologicalClosure (Submodule.mem_map.mpr ⟨w, hw, rfl⟩)
      · exact elementaryFields.isClosed_topologicalClosure.preimage continuous_fst
    have hu : z.1 ∈ completedFields := hf hz
    have he : completedIntegral ⟨z.1, hu⟩ = z.2 :=
      hilbertDivergence.mem_graph_snd_inj
        (completedIntegral_hilbertDivergence_graph ⟨z.1, hu⟩)
        (elementaryTimeGraph_closure_le_divergence hz) rfl
    have hg := completedOperator.mem_graph ⟨z.1, hu⟩
    simpa only [show completedOperator ⟨z.1, hu⟩ = z.2 from he] using hg

theorem completedOperator_isClosed : completedOperator.IsClosed := by
  change IsClosed (completedOperator.graph : Set (GaussianVectorL2 × GaussianL2))
  rw [completedOperator_graph]
  exact elementaryTimeGraph.isClosed_topologicalClosure

theorem completedOperator_le_divergence : completedOperator ≤ hilbertDivergence := by
  apply LinearPMap.le_of_le_graph
  rw [completedOperator_graph]
  exact elementaryTimeGraph_closure_le_divergence

/-- The same elementary sequence approximates both the field and its actual
integral. This is graph approximation on the specified closed polynomial span. -/
theorem exists_elementary_graph_approx (u : completedFields) :
    ∃ z : ℕ → GaussianVectorL2 × GaussianL2,
      (∀ n, z n ∈ elementaryTimeGraph) ∧
      Tendsto (fun n => (z n).1) atTop (𝓝 (u : GaussianVectorL2)) ∧
      Tendsto (fun n => (z n).2) atTop (𝓝 (completedIntegral u)) := by
  obtain ⟨z, hz, hlim⟩ := mem_closure_iff_seq_limit.mp (completedIntegral_graphClosure u)
  exact ⟨z, hz, continuous_fst.continuousAt.tendsto.comp hlim,
    continuous_snd.continuousAt.tendsto.comp hlim⟩

end OperatorDerivativeRewrite.Foundation.GaussianPolynomialStepCompletion
