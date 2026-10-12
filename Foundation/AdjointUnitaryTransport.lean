import Foundation.OperatorDomains

/-!
# Exact unitary transport of partially defined Hilbert operators

The input domain is pulled back along an actual linear isometry equivalence.
Density and closedness are transported, and both directions of the adjoint
domain identification are proved. No stochastic realization is assumed here.
-/

noncomputable section

namespace OperatorDerivativeRewrite.Foundation.AdjointUnitaryTransport

variable {K₁ K₂ X : Type*}
  [NormedAddCommGroup K₁] [InnerProductSpace ℝ K₁]
  [NormedAddCommGroup K₂] [InnerProductSpace ℝ K₂]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Precomposition by a unitary, with the full inverse-image domain. -/
def pullback (U : K₁ ≃ₗᵢ[ℝ] K₂) (T : K₂ →ₗ.[ℝ] X) : K₁ →ₗ.[ℝ] X where
  domain := T.domain.comap U.toLinearEquiv.toLinearMap
  toFun :=
    { toFun := fun u => T ⟨U u, u.property⟩
      map_add' := fun u v => by
        change T ⟨U ((u : K₁) + v), _⟩ = _
        calc
          _ = T (⟨U u, u.property⟩ + ⟨U v, v.property⟩) :=
            congrArg T (Subtype.ext (U.map_add (u : K₁) v))
          _ = _ := T.map_add ⟨U u, u.property⟩ ⟨U v, v.property⟩
      map_smul' := fun a u => by
        change T ⟨U (a • (u : K₁)), _⟩ = _
        calc
          _ = T (a • ⟨U u, u.property⟩) :=
            congrArg T (Subtype.ext (U.map_smul a (u : K₁)))
          _ = _ := T.map_smul a ⟨U u, u.property⟩ }

@[simp] theorem mem_pullback_domain (U : K₁ ≃ₗᵢ[ℝ] K₂) (T : K₂ →ₗ.[ℝ] X)
    (u : K₁) : u ∈ (pullback U T).domain ↔ U u ∈ T.domain := Iff.rfl

@[simp] theorem pullback_apply (U : K₁ ≃ₗᵢ[ℝ] K₂) (T : K₂ →ₗ.[ℝ] X)
    (u : (pullback U T).domain) : pullback U T u = T ⟨U u, u.property⟩ := rfl

/-- The graph is exactly the inverse image under `(u,x) ↦ (U u,x)`. -/
theorem mem_pullback_graph (U : K₁ ≃ₗᵢ[ℝ] K₂) (T : K₂ →ₗ.[ℝ] X)
    (u : K₁) (x : X) : (u, x) ∈ (pullback U T).graph ↔ (U u, x) ∈ T.graph := by
  constructor
  · intro h
    obtain ⟨v, hv, hx⟩ := (pullback U T).mem_graph_iff.mp h
    exact T.mem_graph_iff.mpr ⟨⟨U v, v.property⟩, congrArg U hv, hx⟩
  · intro h
    obtain ⟨v, hv, hx⟩ := T.mem_graph_iff.mp h
    change (v : K₂) = U u at hv
    have hu : U u ∈ T.domain := by rw [← hv]; exact v.property
    apply (pullback U T).mem_graph_iff.mpr
    refine ⟨⟨u, hu⟩, rfl, ?_⟩
    change T ⟨U u, hu⟩ = x
    simpa only [show (⟨U u, hu⟩ : T.domain) = v from Subtype.ext hv.symm] using hx

theorem pullback_dense_domain (U : K₁ ≃ₗᵢ[ℝ] K₂) (T : K₂ →ₗ.[ℝ] X)
    (hT : Dense (T.domain : Set K₂)) : Dense ((pullback U T).domain : Set K₁) :=
  hT.preimage U.toHomeomorph.isOpenMap

theorem pullback_dense_domain_iff (U : K₁ ≃ₗᵢ[ℝ] K₂) (T : K₂ →ₗ.[ℝ] X) :
    Dense ((pullback U T).domain : Set K₁) ↔ Dense (T.domain : Set K₂) := by
  refine ⟨fun h => ?_, pullback_dense_domain U T⟩
  have hd := h.preimage U.symm.toHomeomorph.isOpenMap
  have he : U.symm ⁻¹' ((pullback U T).domain : Set K₁) = (T.domain : Set K₂) := by
    ext u
    change U.symm u ∈ (pullback U T).domain ↔ u ∈ T.domain
    rw [mem_pullback_domain, U.apply_symm_apply]
  change Dense (U.symm ⁻¹' ((pullback U T).domain : Set K₁)) at hd
  rwa [he] at hd

/-- Closedness is a genuine graph-preimage consequence of continuity. -/
theorem pullback_isClosed (U : K₁ ≃ₗᵢ[ℝ] K₂) (T : K₂ →ₗ.[ℝ] X)
    (hT : T.IsClosed) : (pullback U T).IsClosed := by
  have he : ((pullback U T).graph : Set (K₁ × X)) =
      (fun z : K₁ × X => (U z.1, z.2)) ⁻¹' (T.graph : Set (K₂ × X)) := by
    ext z
    exact mem_pullback_graph U T z.1 z.2
  change IsClosed ((pullback U T).graph : Set (K₁ × X))
  rw [he]
  exact hT.preimage ((U.continuous.comp continuous_fst).prodMk continuous_snd)

/-- Unitary transport neither loses nor gains closedness. -/
theorem pullback_isClosed_iff (U : K₁ ≃ₗᵢ[ℝ] K₂) (T : K₂ →ₗ.[ℝ] X) :
    (pullback U T).IsClosed ↔ T.IsClosed := by
  refine ⟨fun h => ?_, pullback_isClosed U T⟩
  have he : (T.graph : Set (K₂ × X)) =
      (fun z : K₂ × X => (U.symm z.1, z.2)) ⁻¹'
        ((pullback U T).graph : Set (K₁ × X)) := by
    ext z
    change (z.1, z.2) ∈ T.graph ↔ (U.symm z.1, z.2) ∈ (pullback U T).graph
    rw [mem_pullback_graph, U.apply_symm_apply]
  change IsClosed (T.graph : Set (K₂ × X))
  rw [he]
  exact h.preimage ((U.symm.continuous.comp continuous_fst).prodMk continuous_snd)

variable [CompleteSpace K₁] [CompleteSpace K₂]

/-- The adjoint domains agree in both directions; density is required for the
actual Hilbert adjoint, not replaced by a supplied pairing identity. -/
theorem mem_pullback_adjoint_domain (U : K₁ ≃ₗᵢ[ℝ] K₂) (T : K₂ →ₗ.[ℝ] X)
    (hT : Dense (T.domain : Set K₂)) (f : X) :
    f ∈ (pullback U T).adjoint.domain ↔ f ∈ T.adjoint.domain := by
  rw [mem_adjoint_domain_iff_representable _ (pullback_dense_domain U T hT),
    mem_adjoint_domain_iff_representable _ hT]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨U v, fun u => ?_⟩
    have hu : U.symm (u : K₂) ∈ (pullback U T).domain := by
      simp only [mem_pullback_domain, U.apply_symm_apply]
      exact u.property
    have hh := hv ⟨U.symm u, hu⟩
    rw [U.inner_map_eq_flip]
    simpa [pullback_apply] using hh
  · rintro ⟨v, hv⟩
    refine ⟨U.symm v, fun u => ?_⟩
    rw [U.symm.inner_map_eq_flip]
    exact hv ⟨U u, u.property⟩

theorem pullback_adjoint_domain (U : K₁ ≃ₗᵢ[ℝ] K₂) (T : K₂ →ₗ.[ℝ] X)
    (hT : Dense (T.domain : Set K₂)) : (pullback U T).adjoint.domain = T.adjoint.domain := by
  ext f
  exact mem_pullback_adjoint_domain U T hT f

/-- The actual adjoint value is the inverse-unitary image of the original value. -/
theorem pullback_adjoint_apply (U : K₁ ≃ₗᵢ[ℝ] K₂) (T : K₂ →ₗ.[ℝ] X)
    (hT : Dense (T.domain : Set K₂)) (f : X)
    (hf : f ∈ (pullback U T).adjoint.domain) (hfT : f ∈ T.adjoint.domain) :
    (pullback U T).adjoint ⟨f, hf⟩ = U.symm (T.adjoint ⟨f, hfT⟩) := by
  apply (pullback U T).adjoint_apply_eq (pullback_dense_domain U T hT)
  intro u
  rw [U.symm.inner_map_eq_flip]
  exact T.adjoint_isFormalAdjoint hT ⟨f, hfT⟩ ⟨U u, u.property⟩

/-- Equality of partial operators, including their complete domains and values. -/
theorem pullback_adjoint_eq (U : K₁ ≃ₗᵢ[ℝ] K₂) (T : K₂ →ₗ.[ℝ] X)
    (hT : Dense (T.domain : Set K₂)) :
    (pullback U T).adjoint = U.symm.toLinearEquiv.toLinearMap.compPMap T.adjoint := by
  apply LinearPMap.ext (pullback_adjoint_domain U T hT)
  intro f hf hfT
  exact pullback_adjoint_apply U T hT f hf hfT

end OperatorDerivativeRewrite.Foundation.AdjointUnitaryTransport
