import Foundation.SignedSchwartzClosedDerivative
import Foundation.HilbertAdjointDomainDensity
import Mathlib.Analysis.InnerProductSpace.Dual

/-! Actual test-generated adjoint vectors and values for the closed signed-marginal derivative. -/
noncomputable section
open MeasureTheory
open scoped SchwartzMap Topology
namespace OperatorDerivativeRewrite.Foundation.SignedSchwartzAdjointProbes
open SignedSchwartzL2Rigging SignedSchwartzClosedDerivative

def eval (g : 𝓢(ℝ,ℂ)) : 𝓢'(ℝ,ℂ) →L[ℝ] ℂ :=
  (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ g).restrictScalars ℝ

def probeFunctional (K : 𝓢(ℝ,ℝ)) (g : 𝓢(ℝ,ℂ)) : H K →L[ℝ] ℝ :=
  Complex.reCLM.comp ((eval g).comp (embed K))

def driftFunctional (K : 𝓢(ℝ,ℝ)) (g : 𝓢(ℝ,ℂ)) : H K →L[ℝ] ℝ :=
  Complex.reCLM.comp ((eval g).comp (driftEmbedding K))

def probe (K : 𝓢(ℝ,ℝ)) (g : 𝓢(ℝ,ℂ)) : H K :=
  (InnerProductSpace.toDual ℝ (H K)).symm (probeFunctional K g)

def image (K : 𝓢(ℝ,ℝ)) (g : 𝓢(ℝ,ℂ)) : H K :=
  (InnerProductSpace.toDual ℝ (H K)).symm
    (-probeFunctional K (SchwartzMap.derivCLM ℂ ℂ g) - driftFunctional K g)

theorem probe_pairing (K : 𝓢(ℝ,ℝ)) (g : 𝓢(ℝ,ℂ)) (u : H K) :
    inner ℝ (probe K g) u = (embed K u g).re := by
  exact InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := u) (y := probeFunctional K g)

theorem image_pairing (K : 𝓢(ℝ,ℝ)) (g : 𝓢(ℝ,ℂ)) (u : H K) :
    inner ℝ (image K g) u =
      -(embed K u (SchwartzMap.derivCLM ℂ ℂ g)).re - (driftEmbedding K u g).re := by
  exact InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := u)
    (y := -probeFunctional K (SchwartzMap.derivCLM ℂ ℂ g) - driftFunctional K g)

theorem weak_pairing (K : 𝓢(ℝ,ℝ)) (u v : H K) (h : (u,v) ∈ weakGraph K) (g : 𝓢(ℝ,ℂ)) :
    inner ℝ (probe K g) v = inner ℝ (image K g) u := by
  rw [probe_pairing, image_pairing]
  have he := congrArg (fun F : 𝓢'(ℝ,ℂ) => (F g).re) ((weakGraph_mem K u v).mp h)
  change (embed K v g).re =
    (embed K u (-SchwartzMap.derivCLM ℂ ℂ g) - driftEmbedding K u g).re at he
  rw [map_neg, Complex.sub_re, Complex.neg_re] at he
  exact he

theorem closed_pairing (K : 𝓢(ℝ,ℝ)) (u : (closedDerivative K).domain) (g : 𝓢(ℝ,ℂ)) :
    inner ℝ (probe K g) (closedDerivative K u) = inner ℝ (image K g) (u:H K) := by
  have hw := LinearPMap.le_graph_of_le (closedDerivative_le_weakDerivative K)
    ((closedDerivative K).mem_graph u)
  rw [weakDerivative_graph] at hw
  exact weak_pairing K u (closedDerivative K u) hw g

theorem probe_in_adjoint_domain (K : 𝓢(ℝ,ℝ)) (g : 𝓢(ℝ,ℂ)) :
    probe K g ∈ (closedDerivative K).adjoint.domain := by
  apply LinearPMap.mem_adjoint_domain_of_exists (T := closedDerivative K)
  exact ⟨image K g, fun u => (closed_pairing K u g).symm⟩

theorem adjoint_probe_value (K : 𝓢(ℝ,ℝ)) (g : 𝓢(ℝ,ℂ)) :
    (closedDerivative K).adjoint ⟨probe K g, probe_in_adjoint_domain K g⟩ = image K g :=
  LinearPMap.adjoint_apply_eq (closedDerivative_dense_domain K) _
    (fun u => (closed_pairing K u g).symm)

theorem probes_span_dense (K : 𝓢(ℝ,ℝ)) :
    Dense (Submodule.span ℝ (Set.range (probe K)) : Set (H K)) := by
  let Z := Submodule.span ℝ (Set.range (probe K))
  have ho : Z.orthogonal=⊥ := by
    apply le_antisymm ?_ bot_le
    intro y hy
    change y=0
    have hr (g : 𝓢(ℝ,ℂ)) : (embed K y g).re=0 := by
      rw [← probe_pairing]
      exact hy (probe K g) (Submodule.subset_span ⟨g, rfl⟩)
    apply embed_injective K
    rw [map_zero]
    ext g
    have hi := hr (Complex.I • g)
    rw [map_smul] at hi
    simp only [smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_sub, neg_eq_zero] at hi
    apply Complex.ext
    · exact hr g
    · exact hi
  have ht : Z.topologicalClosure=⊤ := Z.topologicalClosure_eq_top_iff.mpr ho
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, ht]
  rfl

theorem adjoint_dense_domain (K : 𝓢(ℝ,ℝ)) :
    Dense ((closedDerivative K).adjoint.domain : Set (H K)) := by
  apply (probes_span_dense K).mono
  exact Submodule.span_le.mpr (fun _ ⟨g, hg⟩ => hg ▸ probe_in_adjoint_domain K g)

theorem derivative_bidual (K : 𝓢(ℝ,ℝ)) : (closedDerivative K).adjoint.adjoint=closedDerivative K :=
  HilbertAdjointDomainDensity.closed_bidual _ (closedDerivative_closed K) (closedDerivative_dense_domain K)

theorem core_bidual (K : 𝓢(ℝ,ℝ)) : (coreOperator K).adjoint.adjoint=closedDerivative K :=
  HilbertAdjointDomainDensity.closable_bidual _ (coreOperator_closable K) (coreOperator_dense_domain K)

end OperatorDerivativeRewrite.Foundation.SignedSchwartzAdjointProbes
