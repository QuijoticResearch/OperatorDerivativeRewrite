import Foundation.SignedSchwartzWeakDerivative
import Foundation.AdjointClosure
import Foundation.WeightedFormClosability
import Foundation.NormalizedSignedScoreCounterexample

/-! Genuine dense closability and graph closure of differentiation in L2 of absolute Schwartz density. -/
noncomputable section
open MeasureTheory Filter
open scoped SchwartzMap NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.SignedSchwartzClosedDerivative
open SignedSchwartzL2Rigging SignedSchwartzWeakDerivative

def constraint (K : 𝓢(ℝ,ℝ)) : H K × H K →L[ℝ] 𝓢'(ℝ,ℂ) :=
  (embed K).comp (ContinuousLinearMap.snd ℝ (H K) (H K)) -
    (((TemperedDistribution.derivCLM ℂ).restrictScalars ℝ).comp (embed K) - driftEmbedding K).comp
      (ContinuousLinearMap.fst ℝ (H K) (H K))

def weakGraph (K : 𝓢(ℝ,ℝ)) : Submodule ℝ (H K × H K) := (constraint K).ker

theorem weakGraph_mem (K : 𝓢(ℝ,ℝ)) (u v : H K) : (u,v) ∈ weakGraph K ↔
    embed K v = TemperedDistribution.derivCLM ℂ (embed K u) - driftEmbedding K u := by
  change embed K v - (TemperedDistribution.derivCLM ℂ (embed K u) - driftEmbedding K u)=0 ↔ _
  exact sub_eq_zero

theorem weakGraph_singleValued (K : 𝓢(ℝ,ℝ)) (p : H K × H K)
    (hp : p ∈ weakGraph K) (hz : p.1=0) : p.2=0 := by
  have he := (weakGraph_mem K p.1 p.2).mp hp
  rw [hz, map_zero, map_zero, map_zero, sub_self] at he
  apply embed_injective K
  simpa only [map_zero] using he

def weakDerivative (K : 𝓢(ℝ,ℝ)) : H K →ₗ.[ℝ] H K := (weakGraph K).toLinearPMap

theorem weakDerivative_graph (K : 𝓢(ℝ,ℝ)) : (weakDerivative K).graph=weakGraph K :=
  (weakGraph K).toLinearPMap_graph_eq (weakGraph_singleValued K)

theorem weakGraph_closed (K : 𝓢(ℝ,ℝ)) : IsClosed (weakGraph K : Set (H K × H K)) :=
  (constraint K).isClosed_ker

theorem weakDerivative_closed (K : 𝓢(ℝ,ℝ)) : (weakDerivative K).IsClosed := by
  change IsClosed ((weakDerivative K).graph : Set (H K × H K))
  rw [weakDerivative_graph]
  exact weakGraph_closed K

def coreInput (K : 𝓢(ℝ,ℝ)) : 𝓢(ℝ,ℂ) →L[ℝ] H K :=
  SchwartzMap.toLpCLM ℝ ℂ 2 (SignedSchwartzL2Rigging.measure K)

def coreDerivative (K : 𝓢(ℝ,ℝ)) : 𝓢(ℝ,ℂ) →L[ℝ] H K :=
  (coreInput K).comp ((SchwartzMap.derivCLM ℂ ℂ).restrictScalars ℝ)

theorem core_mem_weakGraph (K : 𝓢(ℝ,ℝ)) (f : 𝓢(ℝ,ℂ)) :
    (coreInput K f, coreDerivative K f) ∈ weakGraph K := by
  rw [weakGraph_mem]
  exact core_identity K f

def coreGraph (K : 𝓢(ℝ,ℝ)) : Submodule ℝ (H K × H K) :=
  ((coreInput K).toLinearMap.prod (coreDerivative K).toLinearMap).range

theorem coreGraph_le_weakGraph (K : 𝓢(ℝ,ℝ)) : coreGraph K ≤ weakGraph K := by
  rintro p ⟨f, rfl⟩
  exact core_mem_weakGraph K f

def coreOperator (K : 𝓢(ℝ,ℝ)) : H K →ₗ.[ℝ] H K := (coreGraph K).toLinearPMap

theorem coreOperator_graph (K : 𝓢(ℝ,ℝ)) : (coreOperator K).graph=coreGraph K := by
  apply (coreGraph K).toLinearPMap_graph_eq
  intro p hp hz
  exact weakGraph_singleValued K p (coreGraph_le_weakGraph K hp) hz

theorem coreOperator_le_weakDerivative (K : 𝓢(ℝ,ℝ)) : coreOperator K ≤ weakDerivative K := by
  apply LinearPMap.le_of_le_graph
  rw [coreOperator_graph, weakDerivative_graph]
  exact coreGraph_le_weakGraph K

theorem coreOperator_dense_domain (K : 𝓢(ℝ,ℝ)) :
    Dense ((coreOperator K).domain : Set (H K)) := by
  have hd : Dense (Set.range (fun f : 𝓢(ℝ,ℂ) => coreInput K f)) :=
    SchwartzMap.denseRange_toLpCLM (F := ℂ) (μ := SignedSchwartzL2Rigging.measure K)
      (p := 2) (by norm_num)
  apply hd.mono
  rintro u ⟨f, rfl⟩
  apply LinearPMap.mem_domain_iff.mpr
  refine ⟨coreDerivative K f, ?_⟩
  rw [coreOperator_graph]
  exact ⟨f, rfl⟩

theorem coreOperator_closable (K : 𝓢(ℝ,ℝ)) : (coreOperator K).IsClosable :=
  (weakDerivative_closed K).isClosable.leIsClosable (coreOperator_le_weakDerivative K)

def closedDerivative (K : 𝓢(ℝ,ℝ)) : H K →ₗ.[ℝ] H K := (coreOperator K).closure

theorem closedDerivative_closed (K : 𝓢(ℝ,ℝ)) : (closedDerivative K).IsClosed :=
  (coreOperator_closable K).closure_isClosed

theorem closedDerivative_dense_domain (K : 𝓢(ℝ,ℝ)) :
    Dense ((closedDerivative K).domain : Set (H K)) :=
  operatorClosure_dense_domain (coreOperator_dense_domain K)

theorem closedDerivative_le_weakDerivative (K : 𝓢(ℝ,ℝ)) :
    closedDerivative K ≤ weakDerivative K :=
  operatorClosure_le_closed (coreOperator_closable K) (weakDerivative_closed K)
    (coreOperator_le_weakDerivative K)

theorem schwartz_mem_closed_graph (K : 𝓢(ℝ,ℝ)) (f : 𝓢(ℝ,ℂ)) :
    (coreInput K f, coreDerivative K f) ∈ (closedDerivative K).graph := by
  apply LinearPMap.le_graph_of_le (coreOperator K).le_closure
  rw [coreOperator_graph]
  exact ⟨f, rfl⟩

theorem core_seqClosable (K : 𝓢(ℝ,ℝ)) :
    WeightedFormClosability.SeqClosable (coreInput K).toLinearMap (coreDerivative K).toLinearMap := by
  intro f hf y hy
  have hlim := hf.prodMk_nhds hy
  have hm : ((0:H K),y) ∈ weakGraph K := (weakGraph_closed K).mem_of_tendsto hlim
    (Eventually.of_forall fun n => core_mem_weakGraph K (f n))
  exact weakGraph_singleValued K (0,y) hm rfl

theorem core_formClosable (K : 𝓢(ℝ,ℝ)) (κ : ℝ) (hκ : 0 ≤ κ) :
    WeightedFormClosability.FormClosable κ (coreInput K).toLinearMap (coreDerivative K).toLinearMap :=
  WeightedFormClosability.seqClosable_implies_nonnegative_form (core_seqClosable K) κ hκ

theorem adjoint_closed (K : 𝓢(ℝ,ℝ)) : (closedDerivative K).adjoint.IsClosed :=
  (closedDerivative K).adjoint_isClosed (closedDerivative_dense_domain K)

def higherHeatDerivative (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    H (HigherHeatSignedLaws.realKernel m hm t ht) →ₗ.[ℝ]
      H (HigherHeatSignedLaws.realKernel m hm t ht) :=
  closedDerivative (HigherHeatSignedLaws.realKernel m hm t ht)

theorem higherHeatDerivative_dense_closed (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    Dense ((higherHeatDerivative m hm t ht).domain :
      Set (H (HigherHeatSignedLaws.realKernel m hm t ht))) ∧
      (higherHeatDerivative m hm t ht).IsClosed :=
  ⟨closedDerivative_dense_domain _, closedDerivative_closed _⟩

theorem counterexample_still_closable :
    (coreOperator NormalizedSignedScoreCounterexample.normalized).IsClosable ∧
      ¬ MemLp (fun x : ℝ => (SignedSchwartzLogDerivative.score
        NormalizedSignedScoreCounterexample.normalized x:ℂ)) 2
        (SignedSchwartzL2Rigging.measure NormalizedSignedScoreCounterexample.normalized) := by
  refine ⟨coreOperator_closable _, ?_⟩
  apply SignedScoreSimpleZero.score_not_memLp_two _
    NormalizedSignedScoreCounterexample.normalized_zero
  rw [NormalizedSignedScoreCounterexample.normalized_derivative]
  exact inv_ne_zero (ne_of_gt NormalizedSignedScoreCounterexample.mass_positive)

end OperatorDerivativeRewrite.Foundation.SignedSchwartzClosedDerivative
