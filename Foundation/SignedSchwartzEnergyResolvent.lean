import Foundation.ClosedOperatorEnergyResolvent
import Foundation.SignedSchwartzAdjointProbes

/-! Actual energy resolvents of the closed signed-marginal derivative, with no score hypothesis. -/
noncomputable section
open MeasureTheory
open scoped SchwartzMap Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.SignedSchwartzEnergyResolvent
open SignedSchwartzL2Rigging SignedSchwartzClosedDerivative

def resolvent (K : 𝓢(ℝ, ℝ)) : H K →L[ℝ] H K :=
  ClosedOperatorEnergyResolvent.resolvent (closedDerivative K) (closedDerivative_closed K)

def gradient (K : 𝓢(ℝ, ℝ)) : H K →L[ℝ] H K :=
  ClosedOperatorEnergyResolvent.gradient (closedDerivative K) (closedDerivative_closed K)

theorem resolvent_domain (K : 𝓢(ℝ, ℝ)) (x : H K) :
    resolvent K x ∈ (closedDerivative K).domain :=
  ClosedOperatorEnergyResolvent.resolvent_mem_domain _ _ x

theorem derivative_resolvent (K : 𝓢(ℝ, ℝ)) (x : H K) :
    closedDerivative K ⟨resolvent K x, resolvent_domain K x⟩ = gradient K x :=
  ClosedOperatorEnergyResolvent.derivative_resolvent _ _ x

theorem gradient_adjoint_domain (K : 𝓢(ℝ, ℝ)) (x : H K) :
    gradient K x ∈ (closedDerivative K).adjoint.domain :=
  ClosedOperatorEnergyResolvent.gradient_mem_adjoint _ _ x

theorem resolvent_equation (K : 𝓢(ℝ, ℝ)) (x : H K) :
    resolvent K x + (closedDerivative K).adjoint
      ⟨gradient K x, gradient_adjoint_domain K x⟩ = x :=
  ClosedOperatorEnergyResolvent.resolvent_equation _ _ (closedDerivative_dense_domain K) x

theorem resolvent_properties (K : 𝓢(ℝ, ℝ)) :
    Function.Injective (resolvent K) ∧ DenseRange (resolvent K) ∧
      (∀ x, ‖resolvent K x‖ ≤ ‖x‖) ∧
      (∀ x y, inner ℝ (resolvent K x) y = inner ℝ x (resolvent K y)) ∧
      (∀ x, 0 ≤ inner ℝ x (resolvent K x)) :=
  ⟨ClosedOperatorEnergyResolvent.resolvent_injective _ _ (closedDerivative_dense_domain K),
    ClosedOperatorEnergyResolvent.resolvent_dense_range _ _ (closedDerivative_dense_domain K),
    ClosedOperatorEnergyResolvent.resolvent_contraction _ _,
    ClosedOperatorEnergyResolvent.resolvent_symmetric _ _,
    ClosedOperatorEnergyResolvent.resolvent_positive _ _⟩

theorem energy_gap (K : 𝓢(ℝ, ℝ)) (x : H K) (u : (closedDerivative K).domain) :
    ‖x - (u : H K)‖ ^ 2 + ‖closedDerivative K u‖ ^ 2 =
      ‖x - resolvent K x‖ ^ 2 + ‖gradient K x‖ ^ 2 +
        ‖(u : H K) - resolvent K x‖ ^ 2 + ‖closedDerivative K u - gradient K x‖ ^ 2 :=
  ClosedOperatorEnergyResolvent.energy_gap _ _ x u

theorem unique_energy_minimizer (K : 𝓢(ℝ, ℝ)) (x : H K) :
    (∀ u : (closedDerivative K).domain,
      ‖x - resolvent K x‖ ^ 2 + ‖gradient K x‖ ^ 2 ≤
        ‖x - (u : H K)‖ ^ 2 + ‖closedDerivative K u‖ ^ 2) ∧
    (∀ u : (closedDerivative K).domain,
      ‖x - (u : H K)‖ ^ 2 + ‖closedDerivative K u‖ ^ 2 ≤
        ‖x - resolvent K x‖ ^ 2 + ‖gradient K x‖ ^ 2 →
          (u : H K) = resolvent K x) :=
  ⟨ClosedOperatorEnergyResolvent.energy_minimum _ _ x,
    ClosedOperatorEnergyResolvent.energy_minimum_unique _ _ x⟩

theorem distributional_equation (K : 𝓢(ℝ, ℝ)) (x : H K) :
    embed K (gradient K x) =
      TemperedDistribution.derivCLM ℂ (embed K (resolvent K x)) -
        driftEmbedding K (resolvent K x) := by
  apply (weakGraph_mem K _ _).mp
  have hm := LinearPMap.le_graph_of_le (closedDerivative_le_weakDerivative K)
    (ClosedOperatorEnergyResolvent.pair_mem_graph (closedDerivative K) (closedDerivative_closed K) x)
  rwa [weakDerivative_graph] at hm

theorem adjoint_probe_identity (K : 𝓢(ℝ, ℝ)) (x : H K) (g : 𝓢(ℝ, ℂ)) :
    inner ℝ (SignedSchwartzAdjointProbes.probe K g) (gradient K x) =
      inner ℝ (SignedSchwartzAdjointProbes.image K g) (resolvent K x) := by
  have h := SignedSchwartzAdjointProbes.closed_pairing K
    ⟨resolvent K x, resolvent_domain K x⟩ g
  rw [derivative_resolvent] at h
  exact h

def higherHeatResolvent (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    H (HigherHeatSignedLaws.realKernel m hm t ht) →L[ℝ]
      H (HigherHeatSignedLaws.realKernel m hm t ht) :=
  resolvent (HigherHeatSignedLaws.realKernel m hm t ht)

theorem higherHeatResolvent_injective_dense (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    Function.Injective (higherHeatResolvent m hm t ht) ∧
      DenseRange (higherHeatResolvent m hm t ht) :=
  ⟨(resolvent_properties _).1, (resolvent_properties _).2.1⟩

end OperatorDerivativeRewrite.Foundation.SignedSchwartzEnergyResolvent
