import Foundation.HigherHeatFourierPathGraphCore
import Foundation.BanachUnboundedAdjoint

/-! A genuine Banach adjoint of the realized path heat generator, with an explicit domain. -/
noncomputable section
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatFourierPathAdjoint
open HigherHeatDyadicLaws HigherHeatFourierBanach HigherHeatFourierPathGenerator
open HigherHeatFourierPathFullGenerator HigherHeatFourierPathResolvent

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def realGraph (m : ℕ) : Submodule ℝ (TestSpace levels ξ × TestSpace levels ξ) :=
  (graph levels ξ m).restrictScalars ℝ

def realOperator (m : ℕ) : TestSpace levels ξ →ₗ.[ℝ] TestSpace levels ξ :=
  (realGraph levels ξ m).toLinearPMap

theorem realOperator_graph (m : ℕ) (hm : 0 < m) :
    (realOperator levels ξ m).graph=realGraph levels ξ m :=
  (realGraph levels ξ m).toLinearPMap_graph_eq (graph_vertical_zero levels ξ m hm)

theorem realOperator_dense (m : ℕ) (hm : 0 < m) :
    DenseRange (realOperator levels ξ m).domain.subtype := by
  change DenseRange (@Subtype.val (TestSpace levels ξ) (fun x => x ∈ (realOperator levels ξ m).domain))
  apply denseRange_subtype_val.mpr
  have he : ((realOperator levels ξ m).domain : Set (TestSpace levels ξ))=
      ((operator levels ξ m).domain : Set (TestSpace levels ξ)) := by
    ext f
    change f ∈ (realOperator levels ξ m).domain ↔ f ∈ (operator levels ξ m).domain
    rw [LinearPMap.mem_domain_iff, LinearPMap.mem_domain_iff,
      realOperator_graph levels ξ m hm, operator_graph levels ξ m hm]
    rfl
  change Dense ((realOperator levels ξ m).domain : Set (TestSpace levels ξ))
  rw [he]
  exact domain_dense levels ξ m hm

def adjoint (m : ℕ) (hm : 0 < m) :
    StrongDual ℝ (TestSpace levels ξ) →ₗ.[ℝ] StrongDual ℝ (TestSpace levels ξ) :=
  BanachUnboundedAdjoint.adjoint (realOperator levels ξ m) (realOperator_dense levels ξ m hm)

theorem adjoint_closed (m : ℕ) (hm : 0 < m) : (adjoint levels ξ m hm).IsClosed :=
  BanachUnboundedAdjoint.adjoint_isClosed _ _

def dualResolvent (m : ℕ) (hm : 0 < m) :
    StrongDual ℝ (TestSpace levels ξ) →L[ℝ] StrongDual ℝ (TestSpace levels ξ) :=
  (ContinuousLinearMap.compL ℝ (TestSpace levels ξ) (TestSpace levels ξ) ℝ).flip
    ((resolvent levels ξ m hm).restrictScalars ℝ)

theorem dualResolvent_apply (m : ℕ) (hm : 0 < m)
    (φ : StrongDual ℝ (TestSpace levels ξ)) (f : TestSpace levels ξ) :
    dualResolvent levels ξ m hm φ f = φ (resolvent levels ξ m hm f) := rfl

theorem adjoint_graph_pairing (m : ℕ) (hm : 0 < m)
    (φ ψ : StrongDual ℝ (TestSpace levels ξ)) :
    (φ,ψ) ∈ (adjoint levels ξ m hm).graph ↔
      ∀ f v, (f,v) ∈ graph levels ξ m → ψ f=φ v := by
  change (φ,ψ) ∈ (BanachUnboundedAdjoint.adjoint _ _).graph ↔ _
  rw [BanachUnboundedAdjoint.adjoint_graph_eq]
  constructor
  · intro h f v hg
    have hg' : (f,v) ∈ (realOperator levels ξ m).graph := by
      rw [realOperator_graph levels ξ m hm]
      exact hg
    obtain ⟨u,hu⟩ := (realOperator levels ξ m).mem_graph_iff'.mp hg'
    change ψ (f,v).1=φ (f,v).2
    rw [← hu]
    exact h u
  · intro h u
    apply h (u:TestSpace levels ξ) (realOperator levels ξ m u)
    have hg := (realOperator levels ξ m).mem_graph u
    rw [realOperator_graph levels ξ m hm] at hg
    exact hg

theorem adjoint_graph_resolvent (m : ℕ) (hm : 0 < m)
    (φ ψ : StrongDual ℝ (TestSpace levels ξ)) :
    (φ,ψ) ∈ (adjoint levels ξ m hm).graph ↔
      φ=dualResolvent levels ξ m hm (φ-ψ) := by
  rw [adjoint_graph_pairing]
  constructor
  · intro h
    ext f
    have he := h _ _ (resolvent_graph levels ξ m hm f)
    change φ f=φ (resolvent levels ξ m hm f)-ψ (resolvent levels ξ m hm f)
    rw [map_sub] at he
    linarith
  · intro he f v hg
    have hf := congrArg (fun θ : StrongDual ℝ (TestSpace levels ξ) => θ (f-v)) he
    change φ (f-v)=(φ-ψ) (resolvent levels ξ m hm (f-v)) at hf
    rw [← resolvent_left_inverse levels ξ m hm (f,v) hg] at hf
    simp only [map_sub, sub_apply] at hf
    linarith

theorem adjoint_domain_iff_range (m : ℕ) (hm : 0 < m)
    (φ : StrongDual ℝ (TestSpace levels ξ)) :
    φ ∈ (adjoint levels ξ m hm).domain ↔ φ ∈ Set.range (dualResolvent levels ξ m hm) := by
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨ψ,hψ⟩
    exact ⟨φ-ψ, ((adjoint_graph_resolvent levels ξ m hm φ ψ).mp hψ).symm⟩
  · rintro ⟨η,hη⟩
    refine ⟨φ-η, (adjoint_graph_resolvent levels ξ m hm φ (φ-η)).mpr ?_⟩
    simpa only [sub_sub_cancel] using hη.symm

theorem dualResolvent_graph (m : ℕ) (hm : 0 < m)
    (η : StrongDual ℝ (TestSpace levels ξ)) :
    (dualResolvent levels ξ m hm η, dualResolvent levels ξ m hm η-η) ∈
      (adjoint levels ξ m hm).graph := by
  apply (adjoint_graph_resolvent levels ξ m hm _ _).mpr
  rw [sub_sub_cancel]

theorem resolvent_zero (m : ℕ) (hm : 0 < m) (f : TestSpace levels ξ)
    (hf : resolvent levels ξ m hm f=0) : f=0 := by
  have hg := resolvent_graph levels ξ m hm f
  rw [hf, zero_sub] at hg
  have hz := graph_vertical_zero levels ξ m hm (0,-f) hg rfl
  exact neg_eq_zero.mp hz

theorem adjoint_domain_separates (m : ℕ) (hm : 0 < m) (f : TestSpace levels ξ)
    (hf : ∀ φ : (adjoint levels ξ m hm).domain,
      (φ : StrongDual ℝ (TestSpace levels ξ)) f=0) : f=0 := by
  apply resolvent_zero levels ξ m hm f
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ)
  intro η
  have hη : dualResolvent levels ξ m hm η ∈ (adjoint levels ξ m hm).domain :=
    (adjoint_domain_iff_range levels ξ m hm _).mpr ⟨η,rfl⟩
  exact hf ⟨dualResolvent levels ξ m hm η,hη⟩

end OperatorDerivativeRewrite.Foundation.HigherHeatFourierPathAdjoint
