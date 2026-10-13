import Foundation.Adjoint

/-! Restriction of a closed source partial operator to a linear observable
subspace. Density is deliberately not assumed. -/
noncomputable section

namespace OperatorDerivativeRewrite.Foundation.ObservableRestriction

variable {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The maximal pullback domain on an observable submodule. -/
def derivative (A : H →ₗ.[ℝ] E) (V : Submodule ℝ H) : V →ₗ.[ℝ] E where
  domain := A.domain.comap V.subtype
  toFun := {
    toFun := fun f => A ⟨f.val.val, f.property⟩
    map_add' := fun f g => by
      calc
        _ = A (⟨f.val.val, f.property⟩ + ⟨g.val.val, g.property⟩) :=
          congrArg A (Subtype.ext rfl)
        _ = _ := A.map_add _ _
    map_smul' := fun a f => by
      calc
        _ = A (a • ⟨f.val.val, f.property⟩) :=
          congrArg A (Subtype.ext rfl)
        _ = _ := A.map_smul a _ }

/-- Domain membership is exactly source-domain membership after inclusion. -/
theorem derivative_domain (A : H →ₗ.[ℝ] E) (V : Submodule ℝ H) (f : V) :
    f ∈ (derivative A V).domain ↔ (f : H) ∈ A.domain := Iff.rfl

/-- The observable graph is the inverse image of the source graph. -/
theorem derivative_graph (A : H →ₗ.[ℝ] E) (V : Submodule ℝ H)
    (f : V) (g : E) :
    (f, g) ∈ (derivative A V).graph ↔ ((f : H), g) ∈ A.graph := by
  constructor
  · intro hz
    obtain ⟨a, ha, hg⟩ := (derivative A V).mem_graph_iff.mp hz
    exact A.mem_graph_iff.mpr
      ⟨⟨a.val.val, a.property⟩, congrArg Subtype.val ha, hg⟩
  · intro hz
    obtain ⟨a, ha, hg⟩ := A.mem_graph_iff.mp hz
    change a.val = (f : H) at ha
    have hf : (f : H) ∈ A.domain := by rw [← ha]; exact a.property
    refine (derivative A V).mem_graph_iff.mpr ⟨⟨f, hf⟩, rfl, ?_⟩
    change A ⟨(f : H), hf⟩ = g
    simpa only [show (⟨(f : H), hf⟩ : A.domain) = a from Subtype.ext ha.symm] using hg

/-- Closedness survives observable restriction, without any domain-density
hypothesis. -/
theorem derivative_isClosed (A : H →ₗ.[ℝ] E) (V : Submodule ℝ H)
    (hA : A.IsClosed) : (derivative A V).IsClosed := by
  have he : ((derivative A V).graph : Set (V × E)) =
      (fun z : V × E => ((z.1 : H), z.2)) ⁻¹' (A.graph : Set (H × E)) := by
    ext z
    exact derivative_graph A V z.1 z.2
  change IsClosed ((derivative A V).graph : Set (V × E))
  rw [he]
  exact hA.preimage ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

end OperatorDerivativeRewrite.Foundation.ObservableRestriction

