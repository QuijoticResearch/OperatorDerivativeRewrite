import Foundation.SignedSchwartzFundamentalSymmetry
import Foundation.SignedSchwartzAdjointProbes

/-! A genuine closed signed-marginal divergence with its explicit transported adjoint domain. -/
noncomputable section
open scoped SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.SignedSchwartzKreinAdjoint
open SignedSchwartzL2Rigging SignedSchwartzClosedDerivative SignedSchwartzFundamentalSymmetry

def pairSymmetry (K : 𝓢(ℝ, ℝ)) : H K × H K →L[ℝ] H K × H K :=
  ((symmetry K).comp (ContinuousLinearMap.fst ℝ (H K) (H K))).prod
    ((symmetry K).comp (ContinuousLinearMap.snd ℝ (H K) (H K)))

def graph (K : 𝓢(ℝ, ℝ)) : Submodule ℝ (H K × H K) :=
  (closedDerivative K).adjoint.graph.comap (pairSymmetry K).toLinearMap

theorem graph_mem (K : 𝓢(ℝ, ℝ)) (v w : H K) :
    (v, w) ∈ graph K ↔ (symmetry K v, symmetry K w) ∈ (closedDerivative K).adjoint.graph := Iff.rfl

theorem graph_singleValued (K : 𝓢(ℝ, ℝ)) (p : H K × H K)
    (hp : p ∈ graph K) (hz : p.1 = 0) : p.2 = 0 := by
  have he := (graph_mem K p.1 p.2).mp hp
  have hw := (closedDerivative K).adjoint.graph_fst_eq_zero_snd he (by rw [hz, map_zero])
  apply symmetry_injective K
  simpa only [map_zero] using hw

def divergence (K : 𝓢(ℝ, ℝ)) : H K →ₗ.[ℝ] H K := (graph K).toLinearPMap

theorem divergence_graph (K : 𝓢(ℝ, ℝ)) : (divergence K).graph = graph K :=
  (graph K).toLinearPMap_graph_eq (graph_singleValued K)

theorem divergence_closed (K : 𝓢(ℝ, ℝ)) : (divergence K).IsClosed := by
  change IsClosed ((divergence K).graph : Set (H K × H K))
  rw [divergence_graph]
  exact (adjoint_closed K).preimage (pairSymmetry K).continuous

theorem divergence_domain (K : 𝓢(ℝ, ℝ)) (v : H K) :
    v ∈ (divergence K).domain ↔ symmetry K v ∈ (closedDerivative K).adjoint.domain := by
  rw [LinearPMap.mem_domain_iff, LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨w,hw⟩
    exact ⟨symmetry K w, (graph_mem K v w).mp ((divergence_graph K) ▸ hw)⟩
  · rintro ⟨w,hw⟩
    refine ⟨symmetry K w, ?_⟩
    rw [divergence_graph, graph_mem, symmetry_twice]
    exact hw

theorem divergence_pairing (K : 𝓢(ℝ, ℝ)) (v w : H K) :
    (v, w) ∈ (divergence K).graph ↔ ∀ u : (closedDerivative K).domain,
      form K (closedDerivative K u) v = form K (u : H K) w := by
  rw [divergence_graph, graph_mem,
    LinearPMap.adjoint_graph_eq_graph_adjoint (closedDerivative_dense_domain K),
    Submodule.mem_adjoint_iff]
  simp only [form_apply, symmetry_selfadjoint]
  constructor
  · intro h u
    have he := h (u : H K) (closedDerivative K u) ((closedDerivative K).mem_graph u)
    exact sub_eq_zero.mp he
  · intro h u y huy
    obtain ⟨z,hz⟩ := (closedDerivative K).mem_graph_iff'.mp huy
    have he := h z
    change inner ℝ y (symmetry K v) - inner ℝ u (symmetry K w) = 0
    have h1 : (z : H K) = u := congrArg Prod.fst hz
    have h2 : closedDerivative K z = y := congrArg Prod.snd hz
    rw [← h1, ← h2]
    exact sub_eq_zero.mpr he


theorem divergence_apply (K : 𝓢(ℝ, ℝ)) (v : (divergence K).domain) :
    divergence K v = symmetry K ((closedDerivative K).adjoint
      ⟨symmetry K (v : H K), (divergence_domain K _).mp v.property⟩) := by
  let y : (closedDerivative K).adjoint.domain :=
    ⟨symmetry K (v : H K), (divergence_domain K _).mp v.property⟩
  have hg : ((v : H K), symmetry K ((closedDerivative K).adjoint y)) ∈ (divergence K).graph := by
    rw [divergence_graph, graph_mem, symmetry_twice]
    exact (closedDerivative K).adjoint.mem_graph y
  exact (divergence K).mem_graph_snd_inj ((divergence K).mem_graph v) hg rfl

theorem divergence_dense_domain (K : 𝓢(ℝ, ℝ)) :
    Dense ((divergence K).domain : Set (H K)) := by
  have hs : Function.Surjective (symmetry K) := fun u => ⟨symmetry K u, symmetry_twice K u⟩
  have hd : DenseRange (fun u : (closedDerivative K).adjoint.domain => (u : H K)) :=
    denseRange_subtype_val.mpr (SignedSchwartzAdjointProbes.adjoint_dense_domain K)
  have he : DenseRange (fun u : (closedDerivative K).adjoint.domain => symmetry K (u : H K)) :=
    hs.denseRange.comp hd (symmetry K).continuous
  apply he.mono
  rintro u ⟨v, rfl⟩
  apply (divergence_domain K _).mpr
  simpa only [symmetry_twice] using v.property

end OperatorDerivativeRewrite.Foundation.SignedSchwartzKreinAdjoint
