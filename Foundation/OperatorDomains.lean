import Foundation.Adjoint
import Foundation.LpProducts

/-!
# Actual operator domains

The adjoint domain is determined by the given operator, not by assigned derivative values.
Graph convergence concerns both an input and the value of this same operator.
L⁴ value-and-derivative membership is a restriction, not an algebra-closure assertion.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation

section Hilbert
variable {X V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The adjoint domain consists exactly of inputs having a representer against δ. -/
theorem mem_adjoint_domain_iff_representable (δ : V →ₗ.[ℝ] X)
    (hδ : Dense (δ.domain : Set V)) (F : X) :
    F ∈ δ.adjoint.domain ↔ ∃ v : V, ∀ u : δ.domain,
      inner ℝ v (u : V) = inner ℝ F (δ u) := by
  constructor
  · intro hF
    exact ⟨δ.adjoint ⟨F, hF⟩, δ.adjoint_isFormalAdjoint hδ ⟨F, hF⟩⟩
  · exact δ.mem_adjoint_domain_of_exists F

/-- A continuous linear operator on the whole space has an everywhere-defined adjoint. -/
theorem bounded_adjoint_domain [CompleteSpace X] (δ : V →L[ℝ] X) :
    (δ.toPMap ⊤).adjoint.domain = ⊤ := by
  rw [δ.toPMap_adjoint_eq_adjoint_toPMap_of_dense (by simp)]
  rfl

omit [CompleteSpace V] in
/-- Closedness passes a genuine graph limit into the domain and identifies its value. -/
theorem closed_graph_limit (D : X →ₗ.[ℝ] V) (hD : D.IsClosed)
    (F : ℕ → D.domain) (f : X) (v : V)
    (hf : Tendsto (fun n ↦ (F n : X)) atTop (𝓝 f))
    (hv : Tendsto (fun n ↦ D (F n)) atTop (𝓝 v)) :
    ∃ h : f ∈ D.domain, D ⟨f, h⟩ = v := by
  have hgraph : (f, v) ∈ D.graph :=
    hD.mem_of_tendsto (hf.prodMk_nhds hv) (Eventually.of_forall fun n ↦ D.mem_graph (F n))
  obtain ⟨y, hy, hyv⟩ := D.mem_graph_iff.mp hgraph
  have h : f ∈ D.domain := by simpa only [hy] using y.property
  exact ⟨h, by simpa [show y = ⟨f, h⟩ from Subtype.ext hy] using hyv⟩
end Hilbert

section Lp
variable {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Elements of the ACTUAL domain whose value and ACTUAL derivative are both L⁴.
This definition does not assert a Sobolev identification or product closure. -/
def fourthMomentDomain (D : Lp ℝ 2 μ →ₗ.[ℝ] Lp H 2 μ) : Set D.domain :=
  {F | MemLp (F : Ω → ℝ) 4 μ ∧ MemLp (D F : Ω → H) 4 μ}

/-- Fourth moments make the product and both proposed Leibniz terms L².
No domain membership for the product and no Leibniz identity is concluded. -/
theorem fourthMomentDomain_product_terms
    (D : Lp ℝ 2 μ →ₗ.[ℝ] Lp H 2 μ) (F G : D.domain)
    (hF : F ∈ fourthMomentDomain D) (hG : G ∈ fourthMomentDomain D) :
    MemLp (fun ω ↦ (F : Ω → ℝ) ω * (G : Ω → ℝ) ω) 2 μ ∧
    MemLp (fun ω ↦ (F : Ω → ℝ) ω • (D G : Ω → H) ω) 2 μ ∧
    MemLp (fun ω ↦ (G : Ω → ℝ) ω • (D F : Ω → H) ω) 2 μ :=
  ⟨mul_L4_memLp_two hF.1 hG.1, smul_L4_memLp_two hF.1 hG.2,
    smul_L4_memLp_two hG.1 hF.2⟩
end Lp
end OperatorDerivativeRewrite.Foundation
