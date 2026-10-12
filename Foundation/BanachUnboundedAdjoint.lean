import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Banach adjoint graphs for densely defined partial operators

The relation below uses actual continuous duals. Its defining equality is
tested only on the original operator domain. Dense domain is needed to make
the reverse graph single-valued; no Hilbert identification is used.
-/

noncomputable section

namespace OperatorDerivativeRewrite.Foundation.BanachUnboundedAdjoint

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The paired adjoint graph, as an actual linear subspace of the two strong
duals. Membership is precisely the transposed pairing equality. -/
def adjointGraph (T : X →ₗ.[ℝ] Y) :
    Submodule ℝ (StrongDual ℝ Y × StrongDual ℝ X) where
  carrier := {z | ∀ x : T.domain, z.2 (x : X) = z.1 (T x)}
  zero_mem' := by simp
  add_mem' := by
    rintro ⟨φ, f⟩ ⟨ψ, g⟩ hf hg x
    change (f + g) (x : X) = (φ + ψ) (T x)
    simp only [add_apply, hf x, hg x]
  smul_mem' := by
    intro c z hz x
    change (c • z.2) (x : X) = (c • z.1) (T x)
    simp only [smul_apply, hz x]

/-- Membership in the graph is exactly the paired identity, without an
extra assumption about the operator values. -/
theorem mem_adjointGraph_iff (T : X →ₗ.[ℝ] Y)
    (φ : StrongDual ℝ Y) (f : StrongDual ℝ X) :
    (φ, f) ∈ adjointGraph T ↔
      ∀ x : T.domain, f (x : X) = φ (T x) := Iff.rfl

/-- The Banach adjoint relation has a closed graph even when `T` itself is
not closed. -/
theorem isClosed_adjointGraph (T : X →ₗ.[ℝ] Y) :
    IsClosed (adjointGraph T : Set (StrongDual ℝ Y × StrongDual ℝ X)) := by
  have hset : (adjointGraph T : Set (StrongDual ℝ Y × StrongDual ℝ X)) =
      ⋂ x : T.domain,
        {z : StrongDual ℝ Y × StrongDual ℝ X |
          z.2 (x : X) = z.1 (T x)} := by
    ext z
    simp [adjointGraph]
  rw [hset]
  apply isClosed_iInter
  intro x
  exact isClosed_eq
    ((continuous_eval_const (x : X)).comp continuous_snd)
    ((continuous_eval_const (T x)).comp continuous_fst)

/-- If the original domain is dense, a fixed dual input has at most one
continuous extension satisfying the adjoint relation. -/
theorem adjointGraph_unique (T : X →ₗ.[ℝ] Y)
    (hDense : DenseRange T.domain.subtype) (φ : StrongDual ℝ Y)
    (f g : StrongDual ℝ X)
    (hf : (φ, f) ∈ adjointGraph T)
    (hg : (φ, g) ∈ adjointGraph T) : f = g := by
  apply ContinuousLinearMap.coeFn_injective
  apply hDense.equalizer f.continuous g.continuous
  funext x
  exact (mem_adjointGraph_iff T φ f).mp hf x |>.trans
    ((mem_adjointGraph_iff T φ g).mp hg x).symm

/-- Density makes the transposed relation single-valued. -/
theorem adjointGraph_vertical_zero (T : X →ₗ.[ℝ] Y)
    (hDense : DenseRange T.domain.subtype)
    (z : StrongDual ℝ Y × StrongDual ℝ X)
    (hz : z ∈ adjointGraph T) (hzero : z.1 = 0) : z.2 = 0 := by
  rcases z with ⟨φ, f⟩
  change φ = 0 at hzero
  subst φ
  exact adjointGraph_unique T hDense 0 f 0 hz (adjointGraph T).zero_mem

/-- The genuine Banach adjoint of a densely defined partial linear operator.
Its domain consists exactly of dual functionals admitting a continuous
extension of their pairing with `T` from the original domain. -/
def adjoint (T : X →ₗ.[ℝ] Y)
    (hDense : DenseRange T.domain.subtype) :
    StrongDual ℝ Y →ₗ.[ℝ] StrongDual ℝ X where
  domain := (adjointGraph T).map
    (LinearMap.fst ℝ (StrongDual ℝ Y) (StrongDual ℝ X))
  toFun := (adjointGraph T).toLinearPMapAux
    (adjointGraph_vertical_zero T hDense)

theorem adjoint_mem_domain_iff (T : X →ₗ.[ℝ] Y)
    (hDense : DenseRange T.domain.subtype) (φ : StrongDual ℝ Y) :
    φ ∈ (adjoint T hDense).domain ↔
      ∃ f : StrongDual ℝ X, ∀ x : T.domain, f (x : X) = φ (T x) := by
  simp only [adjoint, Submodule.mem_map, LinearMap.fst_apply]
  constructor
  · rintro ⟨⟨ψ, f⟩, hmem, hψ⟩
    change ψ = φ at hψ
    subst ψ
    exact ⟨f, hmem⟩
  · rintro ⟨f, hf⟩
    exact ⟨(φ, f), hf, rfl⟩

/-- The partial adjoint's graph is exactly the transposed pairing relation. -/
theorem adjoint_graph_eq (T : X →ₗ.[ℝ] Y)
    (hDense : DenseRange T.domain.subtype) :
    (adjoint T hDense).graph = adjointGraph T := by
  have hv := adjointGraph_vertical_zero T hDense
  have haux := (adjointGraph T).toLinearPMap_graph_eq hv
  convert haux using 1
  simp only [adjoint, Submodule.toLinearPMap]
  split_ifs with hh
  · rfl
  · exact False.elim (hh hv)

/-- The defining identity holds for the actual value of the partial adjoint. -/
theorem adjoint_apply_pairing (T : X →ₗ.[ℝ] Y)
    (hDense : DenseRange T.domain.subtype)
    (φ : (adjoint T hDense).domain) (x : T.domain) :
    (adjoint T hDense φ) (x : X) = (φ : StrongDual ℝ Y) (T x) := by
  have hm : ((φ : StrongDual ℝ Y), adjoint T hDense φ) ∈
      (adjoint T hDense).graph := LinearPMap.mem_graph (adjoint T hDense) φ
  rw [adjoint_graph_eq] at hm
  exact hm x

/-- The partial Banach adjoint has a closed graph in the product of strong
dual spaces. -/
theorem adjoint_isClosed (T : X →ₗ.[ℝ] Y)
    (hDense : DenseRange T.domain.subtype) :
    IsClosed ((adjoint T hDense).graph :
      Set (StrongDual ℝ Y × StrongDual ℝ X)) := by
  rw [adjoint_graph_eq]
  exact isClosed_adjointGraph T

/-- A dual input belongs to the adjoint domain exactly when the composition
with the original operator is bounded in the ambient `X` norm. -/
theorem adjoint_mem_domain_iff_exists_bound (T : X →ₗ.[ℝ] Y)
    (hDense : DenseRange T.domain.subtype) (φ : StrongDual ℝ Y) :
    φ ∈ (adjoint T hDense).domain ↔
      ∃ C : ℝ, ∀ x : T.domain, ‖φ (T x)‖ ≤ C * ‖(x : X)‖ := by
  constructor
  · intro hφ
    obtain ⟨f, hf⟩ := (adjoint_mem_domain_iff T hDense φ).mp hφ
    refine ⟨‖f‖, ?_⟩
    intro x
    rw [← hf x]
    exact f.le_opNorm (x : X)
  · rintro ⟨C, hC⟩
    let l : T.domain →ₗ[ℝ] ℝ := φ.toLinearMap.comp T.toFun
    let f : StrongDual ℝ X := l.extendOfNorm T.domain.subtype
    apply (adjoint_mem_domain_iff T hDense φ).mpr
    refine ⟨f, ?_⟩
    intro x
    have hb : ∀ y : T.domain, ‖l y‖ ≤ C * ‖T.domain.subtype y‖ := by
      intro y
      exact hC y
    exact (LinearMap.extendOfNorm_eq hDense ⟨C, hb⟩ x)

/-- The adjoint value is Mathlib's genuine continuous extension of the
bounded pairing from the dense original domain. -/
theorem adjoint_apply_eq_extension (T : X →ₗ.[ℝ] Y)
    (hDense : DenseRange T.domain.subtype) (φ : StrongDual ℝ Y)
    (C : ℝ)
    (hC : ∀ x : T.domain, ‖φ (T x)‖ ≤ C * ‖(x : X)‖) :
    adjoint T hDense
        ⟨φ, (adjoint_mem_domain_iff_exists_bound T hDense φ).2 ⟨C, hC⟩⟩ =
      (φ.toLinearMap.comp T.toFun).extendOfNorm T.domain.subtype := by
  let l : T.domain →ₗ[ℝ] ℝ := φ.toLinearMap.comp T.toFun
  have hb : ∀ x : T.domain, ‖l x‖ ≤ C * ‖T.domain.subtype x‖ := hC
  apply adjointGraph_unique T hDense φ
  · have hm := LinearPMap.mem_graph (adjoint T hDense)
      ⟨φ, (adjoint_mem_domain_iff_exists_bound T hDense φ).2 ⟨C, hC⟩⟩
    rw [adjoint_graph_eq] at hm
    exact hm
  · intro x
    exact LinearMap.extendOfNorm_eq hDense ⟨C, hb⟩ x

/-- Regard a bounded operator as a partial operator on the whole space. -/
def boundedAsPartial (S : X →L[ℝ] Y) : X →ₗ.[ℝ] Y :=
  S.toLinearMap.toPMap ⊤

theorem boundedAsPartial_dense (S : X →L[ℝ] Y) :
    DenseRange (boundedAsPartial S).domain.subtype := by
  change DenseRange (⊤ : Submodule ℝ X).subtype
  apply Function.Surjective.denseRange
  intro x
  exact ⟨⟨x, Submodule.mem_top⟩, rfl⟩

theorem boundedAsPartial_adjoint_domain (S : X →L[ℝ] Y)
    (φ : StrongDual ℝ Y) :
    φ ∈ (adjoint (boundedAsPartial S) (boundedAsPartial_dense S)).domain := by
  apply (adjoint_mem_domain_iff _ _ φ).2
  refine ⟨φ.comp S, ?_⟩
  intro x
  change φ (S (x : X)) = φ (S (x : X))
  rfl

/-- On a bounded operator, the partial adjoint agrees pointwise with the
ordinary continuous transpose by precomposition. -/
theorem boundedAsPartial_adjoint_apply (S : X →L[ℝ] Y)
    (φ : StrongDual ℝ Y) :
    adjoint (boundedAsPartial S) (boundedAsPartial_dense S)
      ⟨φ, boundedAsPartial_adjoint_domain S φ⟩ = φ.comp S := by
  apply adjointGraph_unique (boundedAsPartial S) (boundedAsPartial_dense S) φ
  · have hm := LinearPMap.mem_graph
      (adjoint (boundedAsPartial S) (boundedAsPartial_dense S))
      ⟨φ, boundedAsPartial_adjoint_domain S φ⟩
    rw [adjoint_graph_eq] at hm
    exact hm
  · intro x
    change φ (S (x : X)) = φ (S (x : X))
    rfl

end OperatorDerivativeRewrite.Foundation.BanachUnboundedAdjoint
