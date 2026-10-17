import Foundation.FourierPathDirectionalFullGenerator
import Foundation.BanachUnboundedAdjoint

/-! The actual closed Banach adjoint of genuine path-directional differentiation. -/
noncomputable section
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathDirectionalAdjoint
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open FourierPathDirectionalOperator

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def realGraph (h : Path) : Submodule ℝ (TestSpace levels ξ × TestSpace levels ξ) :=
  (graph levels ξ h).restrictScalars ℝ

def realOperator (h : Path) : TestSpace levels ξ →ₗ.[ℝ] TestSpace levels ξ :=
  (realGraph levels ξ h).toLinearPMap

theorem realOperator_graph (h : Path) :
    (realOperator levels ξ h).graph=realGraph levels ξ h :=
  (realGraph levels ξ h).toLinearPMap_graph_eq (graph_vertical_zero levels ξ h)

theorem realOperator_dense (h : Path) : DenseRange (realOperator levels ξ h).domain.subtype := by
  change DenseRange (@Subtype.val (TestSpace levels ξ) (fun x => x ∈ (realOperator levels ξ h).domain))
  apply denseRange_subtype_val.mpr
  have he : ((realOperator levels ξ h).domain : Set (TestSpace levels ξ))=
      ((operator levels ξ h).domain : Set (TestSpace levels ξ)) := by
    ext f
    change f ∈ (realOperator levels ξ h).domain ↔ f ∈ (operator levels ξ h).domain
    rw [LinearPMap.mem_domain_iff, LinearPMap.mem_domain_iff, realOperator_graph, operator_graph]
    rfl
  change Dense ((realOperator levels ξ h).domain : Set (TestSpace levels ξ))
  rw [he]
  exact domain_dense levels ξ h

def adjoint (h : Path) :
    StrongDual ℝ (TestSpace levels ξ) →ₗ.[ℝ] StrongDual ℝ (TestSpace levels ξ) :=
  BanachUnboundedAdjoint.adjoint (realOperator levels ξ h) (realOperator_dense levels ξ h)

theorem adjoint_closed (h : Path) : (adjoint levels ξ h).IsClosed :=
  BanachUnboundedAdjoint.adjoint_isClosed _ _

theorem adjoint_graph_pairing (h : Path) (φ ψ : StrongDual ℝ (TestSpace levels ξ)) :
    (φ,ψ) ∈ (adjoint levels ξ h).graph ↔ ∀ z ∈ graph levels ξ h, ψ z.1=φ z.2 := by
  change (φ,ψ) ∈ (BanachUnboundedAdjoint.adjoint _ _).graph ↔ _
  rw [BanachUnboundedAdjoint.adjoint_graph_eq]
  constructor
  · intro hφ z hz
    have hg : z ∈ (realOperator levels ξ h).graph := by rw [realOperator_graph]; exact hz
    obtain ⟨u,hu⟩ := (realOperator levels ξ h).mem_graph_iff'.mp hg
    rw [← hu]
    exact hφ u
  · intro hφ u
    apply hφ ((u:TestSpace levels ξ),realOperator levels ξ h u)
    have hg := (realOperator levels ξ h).mem_graph u
    rw [realOperator_graph] at hg
    exact hg

theorem adjoint_domain_iff_transfer (h : Path) (φ : StrongDual ℝ (TestSpace levels ξ)) :
    φ ∈ (adjoint levels ξ h).domain ↔
      ∃ ψ : StrongDual ℝ (TestSpace levels ξ), ∀ z ∈ graph levels ξ h, φ z.2=ψ z.1 := by
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨ψ,hψ⟩
    exact ⟨ψ,fun z hz => ((adjoint_graph_pairing levels ξ h φ ψ).mp hψ z hz).symm⟩
  · rintro ⟨ψ,hψ⟩
    exact ⟨ψ,(adjoint_graph_pairing levels ξ h φ ψ).mpr (fun z hz => (hψ z hz).symm)⟩

end OperatorDerivativeRewrite.Foundation.FourierPathDirectionalAdjoint
