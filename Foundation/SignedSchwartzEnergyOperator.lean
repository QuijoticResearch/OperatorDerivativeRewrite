import Foundation.ClosedOperatorEnergyOperator
import Foundation.SignedSchwartzEnergyResolvent

/-! A genuine nonnegative self-adjoint derivative-energy operator on each signed Schwartz marginal. -/
noncomputable section
open MeasureTheory
open scoped SchwartzMap Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.SignedSchwartzEnergyOperator
open SignedSchwartzL2Rigging SignedSchwartzClosedDerivative

def operator (K : 𝓢(ℝ, ℝ)) : H K →ₗ.[ℝ] H K :=
  ClosedOperatorEnergyOperator.energyOperator (closedDerivative K) (closedDerivative_closed K)

theorem operator_properties (K : 𝓢(ℝ, ℝ)) :
    Dense ((operator K).domain : Set (H K)) ∧ (operator K).IsClosed ∧
      IsSelfAdjoint (operator K) ∧
      (∀ u : (operator K).domain, 0 ≤ inner ℝ (operator K u) (u:H K)) :=
  ⟨ClosedOperatorEnergyOperator.energy_dense_domain _ _ (closedDerivative_dense_domain K),
    ClosedOperatorEnergyOperator.energy_closed _ _ (closedDerivative_dense_domain K),
    ClosedOperatorEnergyOperator.energy_selfAdjoint _ _ (closedDerivative_dense_domain K),
    ClosedOperatorEnergyOperator.energy_nonnegative _ _ (closedDerivative_dense_domain K)⟩

theorem graph_factorization (K : 𝓢(ℝ, ℝ)) (u w : H K) :
    (u,w) ∈ (operator K).graph ↔
      ∃ v : H K, (u,v) ∈ (closedDerivative K).graph ∧
        (v,w) ∈ (closedDerivative K).adjoint.graph :=
  ClosedOperatorEnergyOperator.energy_graph_factorization _ _ (closedDerivative_dense_domain K) u w

theorem resolvent_domain (K : 𝓢(ℝ, ℝ)) (x : H K) :
    SignedSchwartzEnergyResolvent.resolvent K x ∈ (operator K).domain :=
  ClosedOperatorEnergyOperator.resolvent_energy_domain _ _ (closedDerivative_dense_domain K) x

theorem resolvent_value (K : 𝓢(ℝ, ℝ)) (x : H K) :
    operator K ⟨SignedSchwartzEnergyResolvent.resolvent K x, resolvent_domain K x⟩ =
      x-SignedSchwartzEnergyResolvent.resolvent K x :=
  ClosedOperatorEnergyOperator.energy_resolvent_value _ _ (closedDerivative_dense_domain K) x

theorem resolvent_surjective (K : 𝓢(ℝ, ℝ)) (x : H K) :
    ∃ u : (operator K).domain, (u:H K)+operator K u=x :=
  ClosedOperatorEnergyOperator.energy_resolvent_surjective _ _ (closedDerivative_dense_domain K) x

theorem weighted_distributional_factorization (K : 𝓢(ℝ, ℝ)) (u w : H K)
    (h : (u,w) ∈ (operator K).graph) :
    ∃ v : H K,
      embed K v = TemperedDistribution.derivCLM ℂ (embed K u) - driftEmbedding K u ∧
        (v,w) ∈ (closedDerivative K).adjoint.graph := by
  obtain ⟨v,hv,hw⟩ := (graph_factorization K u w).mp h
  refine ⟨v, ?_, hw⟩
  apply (weakGraph_mem K u v).mp
  have hh := LinearPMap.le_graph_of_le (closedDerivative_le_weakDerivative K) hv
  rwa [weakDerivative_graph] at hh

def higherHeatOperator (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    H (HigherHeatSignedLaws.realKernel m hm t ht) →ₗ.[ℝ]
      H (HigherHeatSignedLaws.realKernel m hm t ht) :=
  operator (HigherHeatSignedLaws.realKernel m hm t ht)

theorem higherHeatOperator_selfAdjoint (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    IsSelfAdjoint (higherHeatOperator m hm t ht) := (operator_properties _).2.2.1

theorem counterexample_operator :
    IsSelfAdjoint (operator NormalizedSignedScoreCounterexample.normalized) ∧
      ¬ MemLp (fun x : ℝ => (SignedSchwartzLogDerivative.score
        NormalizedSignedScoreCounterexample.normalized x:ℂ)) 2
        (measure NormalizedSignedScoreCounterexample.normalized) :=
  ⟨(operator_properties _).2.2.1, counterexample_still_closable.2⟩

end OperatorDerivativeRewrite.Foundation.SignedSchwartzEnergyOperator
