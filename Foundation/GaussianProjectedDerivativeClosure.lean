import Foundation.GaussianPredictableDomainGap

/-! The projected full derivative is closable and closes to the bounded predictable adjoint. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianProjectedDerivativeClosure
open InfiniteGaussian GaussianNumberSectors GaussianPredictableFull GaussianPredictableAdjoint
open GaussianPredictableDomainGap
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe

def graphProjection : GaussianL2 × GaussianVectorL2 →L[ℝ] GaussianL2 × fullPredictable :=
  (ContinuousLinearMap.id ℝ GaussianL2).prodMap predictableProjection

def projectedGraph : Submodule ℝ (GaussianL2 × fullPredictable) :=
  closedCylindricalDerivative.graph.map graphProjection.toLinearMap

theorem projectedGraph_le_bounded_graph : projectedGraph ≤ predictableAdjoint.toLinearMap.graph := by
  rintro _ ⟨⟨F,V⟩, hFV, rfl⟩
  change predictableProjection V = predictableAdjoint F
  let x : closedCylindricalDerivative.domain := ⟨F, LinearPMap.mem_domain_iff.mpr ⟨V,hFV⟩⟩
  have hv : closedCylindricalDerivative x = V :=
    closedCylindricalDerivative.mem_graph_snd_inj (closedCylindricalDerivative.mem_graph x) hFV rfl
  have he := predictableAdjoint_eq_projected_derivative x
  rw [hv] at he
  exact he.symm

theorem bounded_graph_isClosed :
    IsClosed (predictableAdjoint.toLinearMap.graph : Set (GaussianL2 × fullPredictable)) := by
  change IsClosed {p : GaussianL2 × fullPredictable | p.2 = predictableAdjoint p.1}
  exact isClosed_eq continuous_snd (predictableAdjoint.continuous.comp continuous_fst)

theorem projectedGraph_closure :
    projectedGraph.topologicalClosure = predictableAdjoint.toLinearMap.graph := by
  apply le_antisymm
  · exact projectedGraph.topologicalClosure_minimal projectedGraph_le_bounded_graph bounded_graph_isClosed
  · rintro ⟨F,U⟩ hFU
    change U = predictableAdjoint F at hFU
    subst U
    apply projectedGraph.isClosed_topologicalClosure.mem_of_tendsto
      (all_L2_projected_graph_approximation F).2
    apply Eventually.of_forall
    intro N
    exact projectedGraph.le_topologicalClosure
      ⟨(truncation N F, gradientTruncation N F), truncation_graph N F, rfl⟩

theorem projectedGraph_domain_iff (F : GaussianL2) :
    (∃ U : fullPredictable, (F,U) ∈ projectedGraph) ↔ F ∈ closedCylindricalDerivative.domain := by
  constructor
  · rintro ⟨U, ⟨⟨G,V⟩, hGV, he⟩⟩
    have hf := congrArg Prod.fst he
    change G = F at hf
    rw [← hf]
    exact LinearPMap.mem_domain_iff.mpr ⟨V,hGV⟩
  · intro hF
    let x : closedCylindricalDerivative.domain := ⟨F,hF⟩
    exact ⟨predictableProjection (closedCylindricalDerivative x),
      ⟨(F,closedCylindricalDerivative x), closedCylindricalDerivative.mem_graph x, rfl⟩⟩

theorem mem_projectedGraph_iff (F : GaussianL2) (U : fullPredictable) :
    (F,U) ∈ projectedGraph ↔ F ∈ closedCylindricalDerivative.domain ∧ U = predictableAdjoint F := by
  constructor
  · intro h
    exact ⟨(projectedGraph_domain_iff F).mp ⟨U,h⟩, projectedGraph_le_bounded_graph h⟩
  · rintro ⟨hF,hU⟩
    obtain ⟨V,hV⟩ := (projectedGraph_domain_iff F).mpr hF
    have hv : V = predictableAdjoint F := projectedGraph_le_bounded_graph hV
    rwa [show V = U from hv.trans hU.symm] at hV

theorem projectedGraph_not_closed : ¬IsClosed (projectedGraph : Set (GaussianL2 × fullPredictable)) := by
  intro hc
  let F := roughTerminal terminalDirection terminalDirection_unit
  have hm : (F,predictableAdjoint F) ∈ projectedGraph.topologicalClosure := by
    rw [projectedGraph_closure]
    rfl
  rw [hc.submodule_topologicalClosure_eq] at hm
  exact rough_not_in_derivative_domain terminalDirection terminalDirection_unit
    ((projectedGraph_domain_iff F).mp ⟨_,hm⟩)

theorem bounded_extension_unique (K : GaussianL2 →L[ℝ] fullPredictable)
    (hK : ∀ F : closedCylindricalDerivative.domain,
      K F = predictableProjection (closedCylindricalDerivative F)) : K = predictableAdjoint := by
  apply ContinuousLinearMap.ext
  intro F
  have he (N : ℕ) : K (truncation N F) = predictableAdjoint (truncation N F) := by
    let x : closedCylindricalDerivative.domain :=
      ⟨truncation N F, LinearPMap.mem_domain_iff.mpr ⟨gradientTruncation N F, truncation_graph N F⟩⟩
    have hx : closedCylindricalDerivative x = gradientTruncation N F :=
      closedCylindricalDerivative.mem_graph_snd_inj (closedCylindricalDerivative.mem_graph x)
        (truncation_graph N F) rfl
    have hh := hK x
    rw [hx, predictableProjection_gradientTruncation] at hh
    exact hh
  have ht := K.continuous.continuousAt.tendsto.comp (truncation_tendsto F)
  simp only [he, Function.comp_def] at ht
  exact tendsto_nhds_unique ht
    (predictableAdjoint.continuous.continuousAt.tendsto.comp (truncation_tendsto F))

theorem closure_single_valued (F : GaussianL2) (U V : fullPredictable)
    (hU : (F,U) ∈ projectedGraph.topologicalClosure)
    (hV : (F,V) ∈ projectedGraph.topologicalClosure) : U = V := by
  rw [projectedGraph_closure] at hU hV
  exact hU.trans hV.symm

theorem closed_graph_brownian_representation (F : GaussianL2)
    (hF : F ∈ GaussianBrownianGeneratedSpace.brownianL2) :
    ∃! U : fullPredictable, (F,U) ∈ projectedGraph.topologicalClosure ∧
      itoIntegral U = F - (∫ ω, F ω ∂gaussianProduct) • gaussianOne := by
  refine ⟨predictableAdjoint F, ⟨?_, GaussianBrownianPRP.brownian_representation F hF⟩, ?_⟩
  · rw [projectedGraph_closure]
    rfl
  · intro U hU
    have he : (F,predictableAdjoint F) ∈ projectedGraph.topologicalClosure := by
      rw [projectedGraph_closure]
      rfl
    exact closure_single_valued F U _ hU.1 he
end OperatorDerivativeRewrite.Foundation.GaussianProjectedDerivativeClosure
