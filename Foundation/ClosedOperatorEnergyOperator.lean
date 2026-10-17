import Foundation.ClosedOperatorEnergyResolvent

/-! Actual densely defined nonnegative self-adjoint energy operators from closed derivatives. -/
noncomputable section
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.ClosedOperatorEnergyOperator
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
open ClosedOperatorEnergyResolvent

def energyGraph (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) : Submodule ℝ (E × E) :=
  ((resolvent T hT).toLinearMap.prod (LinearMap.id - (resolvent T hT).toLinearMap)).range

theorem energyGraph_mem (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (u v : E) :
    (u,v) ∈ energyGraph T hT ↔ ∃ x, resolvent T hT x=u ∧ x-resolvent T hT x=v := by
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨x, congrArg Prod.fst hx, congrArg Prod.snd hx⟩
  · rintro ⟨x,hx,hy⟩
    exact ⟨x, Prod.ext hx hy⟩

theorem energyGraph_singleValued (T : E →ₗ.[ℝ] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) (p : E × E) (hp : p ∈ energyGraph T hT)
    (hz : p.1=0) : p.2=0 := by
  obtain ⟨x,hx⟩ := hp
  have hr : resolvent T hT x=0 := (congrArg Prod.fst hx).trans hz
  have hx0 : x=0 := resolvent_injective T hT hd (hr.trans (map_zero _).symm)
  have he := congrArg Prod.snd hx
  change x-resolvent T hT x=p.2 at he
  simpa only [hx0, map_zero, sub_self] using he.symm

def energyOperator (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) : E →ₗ.[ℝ] E :=
  (energyGraph T hT).toLinearPMap

theorem energyOperator_graph (T : E →ₗ.[ℝ] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : (energyOperator T hT).graph=energyGraph T hT :=
  Submodule.toLinearPMap_graph_eq _ (energyGraph_singleValued T hT hd)

theorem resolvent_energy_domain (T : E →ₗ.[ℝ] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) (x : E) :
    resolvent T hT x ∈ (energyOperator T hT).domain := by
  apply LinearPMap.mem_domain_iff.mpr
  refine ⟨x-resolvent T hT x, ?_⟩
  rw [energyOperator_graph T hT hd, energyGraph_mem]
  exact ⟨x,rfl,rfl⟩

theorem energy_resolvent_value (T : E →ₗ.[ℝ] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) (x : E) :
    energyOperator T hT ⟨resolvent T hT x, resolvent_energy_domain T hT hd x⟩ =
      x-resolvent T hT x := by
  have hp : (resolvent T hT x, x-resolvent T hT x) ∈ (energyOperator T hT).graph := by
    rw [energyOperator_graph T hT hd, energyGraph_mem]
    exact ⟨x,rfl,rfl⟩
  obtain ⟨u,hu,hv⟩ := (LinearPMap.mem_graph_iff _).mp hp
  have he : u=⟨resolvent T hT x, resolvent_energy_domain T hT hd x⟩ := Subtype.ext hu
  simpa only [he] using hv

theorem input_representation (T : E →ₗ.[ℝ] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) (u : (energyOperator T hT).domain) :
    ∃ x, resolvent T hT x=(u:E) ∧ x-resolvent T hT x=energyOperator T hT u := by
  apply (energyGraph_mem T hT _ _).mp
  rw [← energyOperator_graph T hT hd]
  exact (energyOperator T hT).mem_graph u

theorem energy_dense_domain (T : E →ₗ.[ℝ] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : Dense ((energyOperator T hT).domain : Set E) := by
  apply (resolvent_dense_range T hT hd).mono
  rintro _ ⟨x,rfl⟩
  exact resolvent_energy_domain T hT hd x

theorem energy_formal_selfAdjoint (T : E →ₗ.[ℝ] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    (energyOperator T hT).IsFormalAdjoint (energyOperator T hT) := by
  intro u v
  obtain ⟨x,hx,hy⟩ := input_representation T hT hd u
  obtain ⟨a,ha,hb⟩ := input_representation T hT hd v
  rw [← hx, ← hy, ← ha, ← hb]
  simp only [inner_sub_left, inner_sub_right]
  linarith [resolvent_symmetric T hT x a]

theorem energy_adjoint_eq (T : E →ₗ.[ℝ] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : (energyOperator T hT).adjoint=energyOperator T hT := by
  apply le_antisymm
  · apply LinearPMap.le_of_le_graph
    rintro ⟨y,z⟩ hp
    obtain ⟨v,hvy,hvz⟩ := (LinearPMap.mem_graph_iff _).mp hp
    have hr : resolvent T hT (y+z)=y := by
      apply ext_inner_right ℝ
      intro a
      have hh := (energyOperator T hT).adjoint_isFormalAdjoint (energy_dense_domain T hT hd)
        v ⟨resolvent T hT a, resolvent_energy_domain T hT hd a⟩
      rw [hvz, hvy, energy_resolvent_value T hT hd] at hh
      rw [resolvent_symmetric, inner_add_left]
      rw [inner_sub_right] at hh
      linarith
    rw [energyOperator_graph T hT hd, energyGraph_mem]
    refine ⟨y+z,hr,?_⟩
    rw [hr]
    abel
  · exact (energy_formal_selfAdjoint T hT hd).le_adjoint (energy_dense_domain T hT hd)

theorem energy_selfAdjoint (T : E →ₗ.[ℝ] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : IsSelfAdjoint (energyOperator T hT) :=
  LinearPMap.isSelfAdjoint_def.mpr (energy_adjoint_eq T hT hd)

theorem energy_resolvent_surjective (T : E →ₗ.[ℝ] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) (x : E) :
    ∃ u : (energyOperator T hT).domain, (u:E)+energyOperator T hT u=x := by
  refine ⟨⟨resolvent T hT x, resolvent_energy_domain T hT hd x⟩, ?_⟩
  rw [energy_resolvent_value T hT hd]
  abel

theorem energy_closed (T : E →ₗ.[ℝ] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : (energyOperator T hT).IsClosed := by
  rw [← energy_adjoint_eq T hT hd]
  exact (energyOperator T hT).adjoint_isClosed (energy_dense_domain T hT hd)

theorem energy_nonnegative (T : E →ₗ.[ℝ] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) (u : (energyOperator T hT).domain) :
    0 ≤ inner ℝ (energyOperator T hT u) (u:E) := by
  obtain ⟨x,hx,hy⟩ := input_representation T hT hd u
  rw [← hx, ← hy, inner_sub_left, real_inner_self_eq_norm_sq]
  have he := energy_identity T hT x
  nlinarith [sq_nonneg ‖gradient T hT x‖]

theorem resolvent_factor_graph (T : E →ₗ.[ℝ] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) (x : E) :
    (gradient T hT x, x-resolvent T hT x) ∈ T.adjoint.graph := by
  have hh := T.adjoint.mem_graph ⟨gradient T hT x, gradient_mem_adjoint T hT x⟩
  rwa [adjoint_gradient T hT hd] at hh

theorem energy_graph_factorization (T : E →ₗ.[ℝ] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) (u w : E) :
    (u,w) ∈ (energyOperator T hT).graph ↔
      ∃ v : F, (u,v) ∈ T.graph ∧ (v,w) ∈ T.adjoint.graph := by
  constructor
  · intro hp
    rw [energyOperator_graph T hT hd, energyGraph_mem] at hp
    obtain ⟨x,hx,hw⟩ := hp
    refine ⟨gradient T hT x, ?_, ?_⟩
    · simpa only [hx] using pair_mem_graph T hT x
    · simpa only [hw] using resolvent_factor_graph T hT hd x
  · rintro ⟨v,hv,hw⟩
    obtain ⟨a,ha,hav⟩ := T.mem_graph_iff.mp hv
    obtain ⟨b,hb,hbw⟩ := T.adjoint.mem_graph_iff.mp hw
    have hr : resolvent T hT (u+w)=u := by
      apply ext_inner_right ℝ
      intro x
      have hh := T.adjoint_isFormalAdjoint hd b
        ⟨resolvent T hT x, resolvent_mem_domain T hT x⟩
      rw [hbw, hb, derivative_resolvent] at hh
      have he := weak_identity T hT x a
      rw [ha, hav] at he
      rw [resolvent_symmetric, inner_add_left]
      have hc := real_inner_comm v (gradient T hT x)
      have hu := real_inner_comm u (resolvent T hT x)
      have hx := real_inner_comm u x
      linarith
    rw [energyOperator_graph T hT hd, energyGraph_mem]
    refine ⟨u+w,hr,?_⟩
    rw [hr]
    abel

end OperatorDerivativeRewrite.Foundation.ClosedOperatorEnergyOperator
