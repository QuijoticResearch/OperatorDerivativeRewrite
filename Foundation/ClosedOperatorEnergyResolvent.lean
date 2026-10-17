import Foundation.HilbertAdjointDomainDensity

/-! Genuine energy resolvents constructed by projecting onto a closed Hilbert operator graph. -/
noncomputable section
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.ClosedOperatorEnergyResolvent
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def graphSpace (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) : ClosedSubmodule ℝ (WithLp 2 (E × F)) :=
  ⟨T.graph.comap (WithLp.linearEquiv 2 ℝ (E × F)).toLinearMap,
    hT.preimage (WithLp.prod_continuous_ofLp 2 E F)⟩

def input : E →L[ℝ] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] F))

def projection (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) :
    WithLp 2 (E × F) →L[ℝ] WithLp 2 (E × F) := (graphSpace T hT).starProjection

def resolvent (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) : E →L[ℝ] E :=
  (WithLp.fstL 2 ℝ E F).comp ((projection T hT).comp input)

def gradient (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) : E →L[ℝ] F :=
  (WithLp.sndL 2 ℝ E F).comp ((projection T hT).comp input)

theorem pair_mem_graph (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (x : E) :
    (resolvent T hT x, gradient T hT x) ∈ T.graph := by
  exact (graphSpace T hT).starProjection_apply_mem (input x)

theorem resolvent_mem_domain (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (x : E) :
    resolvent T hT x ∈ T.domain :=
  LinearPMap.mem_domain_iff.mpr ⟨gradient T hT x, pair_mem_graph T hT x⟩

theorem derivative_resolvent (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (x : E) :
    T ⟨resolvent T hT x, resolvent_mem_domain T hT x⟩ = gradient T hT x := by
  obtain ⟨y, hy, he⟩ := (T.mem_graph_iff).mp (pair_mem_graph T hT x)
  have hy' : y = ⟨resolvent T hT x, resolvent_mem_domain T hT x⟩ := Subtype.ext hy
  simpa only [hy'] using he

theorem weak_identity (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (x : E) (u : T.domain) :
    inner ℝ (resolvent T hT x) (u : E) + inner ℝ (gradient T hT x) (T u) =
      inner ℝ x (u : E) := by
  have hh := (graphSpace T hT).starProjection_inner_eq_zero
    (input x) (WithLp.toLp 2 ((u : E), T u)) (T.mem_graph u)
  rw [inner_sub_left] at hh
  change inner ℝ (WithLp.toLp 2 (x, (0 : F))) (WithLp.toLp 2 ((u : E), T u)) -
    inner ℝ (WithLp.toLp 2 (resolvent T hT x, gradient T hT x))
      (WithLp.toLp 2 ((u : E), T u)) = 0 at hh
  simp only [WithLp.prod_inner_apply, inner_zero_left, add_zero] at hh
  linarith

theorem gradient_mem_adjoint (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (x : E) :
    gradient T hT x ∈ T.adjoint.domain := by
  apply LinearPMap.mem_adjoint_domain_of_exists (T := T)
  refine ⟨x - resolvent T hT x, fun u => ?_⟩
  rw [inner_sub_left]
  linarith [weak_identity T hT x u]

theorem adjoint_gradient (T : E →ₗ.[ℝ] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) (x : E) :
    T.adjoint ⟨gradient T hT x, gradient_mem_adjoint T hT x⟩ = x - resolvent T hT x := by
  apply LinearPMap.adjoint_apply_eq hd
  intro u
  rw [inner_sub_left]
  linarith [weak_identity T hT x u]

theorem resolvent_equation (T : E →ₗ.[ℝ] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) (x : E) :
    resolvent T hT x + T.adjoint ⟨gradient T hT x, gradient_mem_adjoint T hT x⟩ = x := by
  rw [adjoint_gradient T hT hd]
  abel

theorem energy_identity (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (x : E) :
    ‖resolvent T hT x‖ ^ 2 + ‖gradient T hT x‖ ^ 2 = inner ℝ x (resolvent T hT x) := by
  have h := weak_identity T hT x ⟨resolvent T hT x, resolvent_mem_domain T hT x⟩
  rw [derivative_resolvent, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact h

theorem resolvent_contraction (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (x : E) :
    ‖resolvent T hT x‖ ≤ ‖x‖ := by
  calc
    _ ≤ ‖projection T hT (input x)‖ :=
      WithLp.norm_fst_le (p := 2) (α := E) (β := F) (projection T hT (input x))
    _ ≤ ‖input (F := F) x‖ := (graphSpace T hT).norm_starProjection_apply_le _
    _ = ‖x‖ := WithLp.norm_toLp_fst 2 E F x

theorem resolvent_symmetric (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (x y : E) :
    inner ℝ (resolvent T hT x) y = inner ℝ x (resolvent T hT y) := by
  have h := (graphSpace T hT).inner_starProjection_left_eq_right (input x) (input y)
  change inner ℝ (WithLp.toLp 2 (resolvent T hT x, gradient T hT x))
    (WithLp.toLp 2 (y, (0 : F))) =
    inner ℝ (WithLp.toLp 2 (x, (0 : F)))
      (WithLp.toLp 2 (resolvent T hT y, gradient T hT y)) at h
  simpa only [WithLp.prod_inner_apply, inner_zero_right, inner_zero_left, add_zero] using h

theorem resolvent_positive (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (x : E) :
    0 ≤ inner ℝ x (resolvent T hT x) := by
  rw [← energy_identity T hT x]
  positivity

theorem resolvent_injective (T : E →ₗ.[ℝ] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : Function.Injective (resolvent T hT) := by
  have ht : T.domain.topologicalClosure = ⊤ := by
    apply SetLike.coe_injective
    simpa only [Submodule.topologicalClosure_coe, Submodule.top_coe] using hd.closure_eq
  have ho := T.domain.topologicalClosure_eq_top_iff.mp ht
  intro x y hxy
  have hz : resolvent T hT (x-y) = 0 := by rw [map_sub, hxy, sub_self]
  have hg : gradient T hT (x-y) = 0 := by
    have hp := pair_mem_graph T hT (x-y)
    rw [hz] at hp
    exact T.graph_fst_eq_zero_snd hp rfl
  have hm : x-y ∈ T.domain.orthogonal := by
    intro a ha
    have hh := weak_identity T hT (x-y) ⟨a, ha⟩
    rw [hz, hg, inner_zero_left, inner_zero_left, zero_add] at hh
    rw [real_inner_comm]
    exact hh.symm
  rw [ho] at hm
  exact sub_eq_zero.mp hm

theorem resolvent_dense_range (T : E →ₗ.[ℝ] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : DenseRange (resolvent T hT) := by
  let Z := (resolvent T hT).toLinearMap.range
  have ho : Z.orthogonal = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro y hy
    change y=0
    have hh := hy (resolvent T hT (resolvent T hT y)) ⟨resolvent T hT y, rfl⟩
    rw [resolvent_symmetric] at hh
    have hz : resolvent T hT y=0 := inner_self_eq_zero.mp hh
    exact resolvent_injective T hT hd (hz.trans (map_zero _).symm)
  have ht : Z.topologicalClosure=⊤ := Z.topologicalClosure_eq_top_iff.mpr ho
  change Dense (Z : Set E)
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, ht]
  rfl

theorem energy_gap (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (x : E) (u : T.domain) :
    ‖x - (u : E)‖ ^ 2 + ‖T u‖ ^ 2 =
      ‖x - resolvent T hT x‖ ^ 2 + ‖gradient T hT x‖ ^ 2 +
        ‖(u : E) - resolvent T hT x‖ ^ 2 + ‖T u - gradient T hT x‖ ^ 2 := by
  simp only [norm_sub_sq_real]
  have hw := weak_identity T hT x u
  rw [real_inner_comm (u : E) (resolvent T hT x),
    real_inner_comm (T u) (gradient T hT x)] at hw
  nlinarith [energy_identity T hT x]

theorem energy_minimum (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (x : E) (u : T.domain) :
    ‖x - resolvent T hT x‖ ^ 2 + ‖gradient T hT x‖ ^ 2 ≤
      ‖x - (u : E)‖ ^ 2 + ‖T u‖ ^ 2 := by
  rw [energy_gap T hT x u]
  nlinarith [sq_nonneg ‖(u : E) - resolvent T hT x‖,
    sq_nonneg ‖T u - gradient T hT x‖]

theorem energy_minimum_unique (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (x : E) (u : T.domain)
    (hu : ‖x - (u : E)‖ ^ 2 + ‖T u‖ ^ 2 ≤
      ‖x - resolvent T hT x‖ ^ 2 + ‖gradient T hT x‖ ^ 2) :
    (u : E) = resolvent T hT x := by
  rw [energy_gap T hT x u] at hu
  have hz : ‖(u : E) - resolvent T hT x‖ = 0 := by
    nlinarith [sq_nonneg ‖T u - gradient T hT x‖,
      norm_nonneg ((u : E) - resolvent T hT x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end OperatorDerivativeRewrite.Foundation.ClosedOperatorEnergyResolvent
