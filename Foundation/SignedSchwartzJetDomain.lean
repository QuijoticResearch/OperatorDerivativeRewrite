import Foundation.SignedSchwartzClosedDerivative
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-! A complete positive-majorant jet domain with unique marginal value.
All derivatives through r are retained; no signed path norm or causal bound is assumed. -/
noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.SignedSchwartzJetDomain
open SignedSchwartzL2Rigging SignedSchwartzClosedDerivative

abbrev Jets (K : 𝓢(ℝ, ℝ)) (r : ℕ) := Fin (r + 1) → H K

def step (K : 𝓢(ℝ, ℝ)) (r : ℕ) (i : Fin r) : Jets K r →L[ℝ] H K × H K :=
  (ContinuousLinearMap.proj i.castSucc).prod (ContinuousLinearMap.proj i.succ)

def compatible (K : 𝓢(ℝ, ℝ)) (r : ℕ) : Submodule ℝ (Jets K r) :=
  ⨅ i : Fin r, (closedDerivative K).graph.comap (step K r i).toLinearMap

theorem mem_compatible (K : 𝓢(ℝ, ℝ)) (r : ℕ) (u : Jets K r) :
    u ∈ compatible K r ↔ ∀ i : Fin r,
      (u i.castSucc, u i.succ) ∈ (closedDerivative K).graph := by
  simp [compatible, step]

theorem compatible_closed (K : 𝓢(ℝ, ℝ)) (r : ℕ) :
    IsClosed (compatible K r : Set (Jets K r)) := by
  have he : (compatible K r : Set (Jets K r)) =
      ⋂ i : Fin r, (step K r i) ⁻¹' ((closedDerivative K).graph : Set (H K × H K)) := by
    ext u
    simp only [Set.mem_iInter, Set.mem_preimage]
    exact mem_compatible K r u
  rw [he]
  exact isClosed_iInter (fun i => (closedDerivative_closed K).preimage (step K r i).continuous)

def jets (K : 𝓢(ℝ, ℝ)) (r : ℕ) : 𝓢(ℝ, ℂ) →ₗ[ℝ] Jets K r :=
  LinearMap.pi (fun i => (coreInput K).toLinearMap.comp
    (((SchwartzMap.derivCLM ℂ ℂ).restrictScalars ℝ).toLinearMap^i.val))

theorem jets_apply (K : 𝓢(ℝ, ℝ)) (r : ℕ) (f : 𝓢(ℝ, ℂ)) (i : Fin (r + 1)) :
    jets K r f i = coreInput K ((SchwartzMap.derivCLM ℂ ℂ)^[i.val] f) := by
  change coreInput K
    ((((SchwartzMap.derivCLM ℂ ℂ).restrictScalars ℝ).toLinearMap^i.val) f) = _
  rw [Module.End.pow_apply]
  rfl

theorem jets_compatible (K : 𝓢(ℝ, ℝ)) (r : ℕ) (f : 𝓢(ℝ, ℂ)) :
    jets K r f ∈ compatible K r := by
  rw [mem_compatible]
  intro i
  rw [jets_apply, jets_apply]
  simp only [Fin.val_castSucc, Fin.val_succ]
  rw [Function.iterate_succ_apply']
  exact schwartz_mem_closed_graph K _

def coreClosure (K : 𝓢(ℝ, ℝ)) (r : ℕ) : Submodule ℝ (Jets K r) :=
  (jets K r).range.topologicalClosure

theorem coreClosure_closed (K : 𝓢(ℝ, ℝ)) (r : ℕ) :
    IsClosed (coreClosure K r : Set (Jets K r)) :=
  (jets K r).range.isClosed_topologicalClosure

theorem coreClosure_compatible (K : 𝓢(ℝ, ℝ)) (r : ℕ) :
    coreClosure K r ≤ compatible K r := by
  apply Submodule.topologicalClosure_minimal
  · rintro u ⟨f, rfl⟩
    exact jets_compatible K r f
  · exact compatible_closed K r

abbrev Domain (K : 𝓢(ℝ, ℝ)) (r : ℕ) := coreClosure K r

instance domain_complete (K : 𝓢(ℝ, ℝ)) (r : ℕ) : CompleteSpace (Domain K r) :=
  completeSpace_coe_iff_isComplete.mpr (coreClosure_closed K r).isComplete

theorem compatible_zero (K : 𝓢(ℝ, ℝ)) (r : ℕ) (u : Jets K r)
    (hu : u ∈ compatible K r) (hz : u 0 = 0) : u = 0 := by
  funext i
  refine Fin.induction hz ?_ i
  intro j hj
  have hs := (mem_compatible K r u).mp hu j
  have hw := LinearPMap.le_graph_of_le (closedDerivative_le_weakDerivative K) hs
  rw [weakDerivative_graph] at hw
  exact weakGraph_singleValued K _ hw hj

def value (K : 𝓢(ℝ, ℝ)) (r : ℕ) : Domain K r →L[ℝ] H K :=
  (ContinuousLinearMap.proj 0).comp (coreClosure K r).subtypeL

theorem value_injective (K : 𝓢(ℝ, ℝ)) (r : ℕ) : Function.Injective (value K r) := by
  intro u v huv
  apply Subtype.ext
  have hz : ((u : Jets K r) - (v : Jets K r)) 0 = 0 := sub_eq_zero.mpr huv
  have he := compatible_zero K r _ (coreClosure_compatible K r (u-v).property) hz
  exact sub_eq_zero.mp he


def core (K : 𝓢(ℝ, ℝ)) (r : ℕ) : 𝓢(ℝ, ℂ) →ₗ[ℝ] Domain K r :=
  (jets K r).codRestrict (coreClosure K r) (fun f =>
    (jets K r).range.le_topologicalClosure ⟨f, rfl⟩)

theorem core_value (K : 𝓢(ℝ, ℝ)) (r : ℕ) (f : 𝓢(ℝ, ℂ)) :
    value K r (core K r f) = coreInput K f := by
  change jets K r f 0 = _
  rw [jets_apply]
  rfl

theorem core_dense (K : 𝓢(ℝ, ℝ)) (r : ℕ) : DenseRange (core K r) := by
  change DenseRange (Set.inclusion (s := Set.range (jets K r))
    (t := closure (Set.range (jets K r))) subset_closure ∘ Set.rangeFactorization (jets K r))
  exact ((denseRange_inclusion_iff subset_closure).2 subset_rfl).comp
    Set.rangeFactorization_surjective.denseRange (continuous_inclusion subset_closure)

def component (K : 𝓢(ℝ, ℝ)) (r : ℕ) (i : Fin (r + 1)) : Domain K r →L[ℝ] H K :=
  (ContinuousLinearMap.proj i).comp (coreClosure K r).subtypeL

theorem core_component (K : 𝓢(ℝ, ℝ)) (r : ℕ) (i : Fin (r + 1)) (f : 𝓢(ℝ, ℂ)) :
    component K r i (core K r f) = coreInput K ((SchwartzMap.derivCLM ℂ ℂ)^[i.val] f) :=
  jets_apply K r f i

end OperatorDerivativeRewrite.Foundation.SignedSchwartzJetDomain
