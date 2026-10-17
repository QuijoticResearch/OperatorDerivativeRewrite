import Foundation.OneSidedGramSector

/-! The one-sided cube with outward cap vertices and ribbon faces.
Its interior restriction is the previously verified incidence map. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.OneSidedCapComplex
open OneSidedBlockIncidence OneSidedBlockKernel OneSidedBlockRank
set_option maxRecDepth 65536
set_option maxHeartbeats 128000000
set_option backward.isDefEq.respectTransparency false

abbrev Cap := {a : Vertex × Fin 4 // a.1 a.2=1}
abbrev Boundary := Cap ⊕ Upper
abbrev FullVertex := Vertex ⊕ Cap
abbrev FullEdge := Interior ⊕ Boundary
abbrev FullFace := Inner ⊕ Upper
abbrev Potential := FullVertex → ℝ
abbrev FullField := FullEdge → ℝ

theorem cap_card : Fintype.card Cap=32 := by decide

theorem boundary_card : Fintype.card Boundary=80 := by
  simp only [Boundary,Fintype.card_sum,cap_card,upper_card]

theorem fullVertex_card : Fintype.card FullVertex=48 := by decide

theorem fullEdge_card : Fintype.card FullEdge=112 := by
  simp only [FullEdge,Fintype.card_sum,interior_card,cap_card,upper_card]

theorem fullFace_card : Fintype.card FullFace=72 := by
  simp only [FullFace,Fintype.card_sum,inner_card,upper_card]

def ribbonInterior (p : Upper) : Interior :=
  ⟨p.val.1,(Finset.mem_filter.mp p.property).2.1⟩

def capLow (p : Upper) : Cap :=
  ⟨(p.val.1.1,p.val.2),(Finset.mem_filter.mp p.property).2.2.2⟩

def capHigh (p : Upper) : Cap :=
  ⟨(shifted p.val.1.1 p.val.1.2,p.val.2),by
    have hn := (Finset.mem_filter.mp p.property).2.2.1
    have hv := (Finset.mem_filter.mp p.property).2.2.2
    simpa only [shifted,Function.update_of_ne hn] using hv⟩

def source : FullEdge → FullVertex
  | .inl e => .inl e.val.1
  | .inr (.inl c) => .inl c.val.1
  | .inr (.inr p) => .inr (capLow p)

def target : FullEdge → FullVertex
  | .inl e => .inl (shifted e.val.1 e.val.2)
  | .inr (.inl c) => .inr c
  | .inr (.inr p) => .inr (capHigh p)

def direction : FullEdge → Fin 4
  | .inl e => e.val.2
  | .inr (.inl c) => c.val.2
  | .inr (.inr p) => p.val.1.2

def d0 : Potential →ₗ[ℝ] FullField where
  toFun phi e := phi (target e)-phi (source e)
  map_add' phi psi := by funext e; simp only [Pi.add_apply]; ring
  map_smul' c phi := by
    funext e
    change c*phi (target e)-c*phi (source e)=c*(phi (target e)-phi (source e))
    ring

def interiorPart : FullField →ₗ[ℝ] Field where
  toFun f e := f (.inl e)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def ribbonRow (p : Upper) : FullField →ₗ[ℝ] ℝ where
  toFun f := f (.inl (ribbonInterior p))+f (.inr (.inl (capHigh p)))-
    f (.inr (.inr p))-f (.inr (.inl (capLow p)))
  map_add' f g := by simp only [Pi.add_apply]; ring
  map_smul' c f := by
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    ring

def d1 : FullField →ₗ[ℝ] Curvature :=
  ((OneSidedGramSector.innerMap).comp interiorPart).prod (LinearMap.pi ribbonRow)

def injectInterior (f : Field) : FullField := Sum.elim f (fun _ => 0)

theorem d1_interior (f : Field) : d1 (injectInterior f)=incidence f := by
  apply Prod.ext
  · rfl
  · funext p
    change f (ribbonInterior p)+0-0-0=extend f p.val.1
    have he := (Finset.mem_filter.mp p.property).2.1
    simp [ribbonInterior,extend,he]

theorem shifted_commute : ∀ v : Vertex, ∀ i j : Fin 4,
    shifted (shifted v i) j=shifted (shifted v j) i := by decide

theorem interior_gradient_value (phi : Potential) (e : EdgeData) (he : e∈edges) :
    extend (interiorPart (d0 phi)) e=
      phi (.inl (shifted e.1 e.2))-phi (.inl e.1) := by
  simp [extend,he,interiorPart,d0,source,target]

theorem inner_gradient_zero (phi : Potential) (p : Inner) :
    OneSidedGramSector.innerMap (interiorPart (d0 phi)) p=0 := by
  obtain ⟨h1,h2,h3,h4⟩ := inner_edge_geometry p p.property
  change realCurl (extend (interiorPart (d0 phi))) p=0
  unfold realCurl
  rw [interior_gradient_value phi _ h1,interior_gradient_value phi _ h2,
    interior_gradient_value phi _ h3,interior_gradient_value phi _ h4,
    shifted_commute p.val.1 p.val.2.1 p.val.2.2]
  ring

theorem ribbon_gradient_zero (phi : Potential) (p : Upper) : ribbonRow p (d0 phi)=0 := by
  simp [ribbonRow,d0,source,target,ribbonInterior,capLow,capHigh] <;> ring

theorem d1_d0 (phi : Potential) : d1 (d0 phi)=0 := by
  apply Prod.ext <;> funext p
  · exact inner_gradient_zero phi p
  · exact ribbon_gradient_zero phi p

abbrev WideVertex := Fin 4 → Fin 3
abbrev WideEdge := WideVertex × Fin 4

def embedInner (v : Vertex) : WideVertex := fun i => ⟨(v i).val,by omega⟩

def embedVertex : FullVertex → WideVertex
  | .inl v => embedInner v
  | .inr c => Function.update (embedInner c.val.1) c.val.2 2

def embedEdge (e : FullEdge) : WideEdge := (embedVertex (source e),direction e)

def wideShift (v : WideVertex) (i : Fin 4) : WideVertex :=
  Function.update v i (if v i=0 then 1 else 2)

theorem embedVertex_injective : Function.Injective embedVertex := by decide

theorem embedEdge_injective : Function.Injective embedEdge := by decide

theorem embed_target : ∀ e : FullEdge,
    embedVertex (target e)=wideShift (embedVertex (source e)) (direction e) ∧
      (embedVertex (source e) (direction e)).val<2 := by decide

def wideInterior (e : WideEdge) : Prop := (∀ i, (e.1 i).val<2) ∧ e.1 e.2=0

instance wideInterior_decidable (e : WideEdge) : Decidable (wideInterior e) :=
  inferInstanceAs (Decidable ((∀ i, (e.1 i).val<2) ∧ e.1 e.2=0))

def sourceFaces : Finset (WideVertex × (Fin 4 × Fin 4)) :=
  Finset.univ.filter (fun p => p.2.1<p.2.2 ∧
    (wideInterior (p.1,p.2.1) ∨ wideInterior (wideShift p.1 p.2.1,p.2.2) ∨
      wideInterior (wideShift p.1 p.2.2,p.2.1) ∨ wideInterior (p.1,p.2.2)))

abbrev SourceFace := {p : WideVertex × (Fin 4 × Fin 4) // p∈sourceFaces}

theorem sourceFaces_card : sourceFaces.card=72 := by decide

def faceData : FullFace → WideVertex × (Fin 4 × Fin 4)
  | .inl p => (embedInner p.val.1,p.val.2)
  | .inr p => (embedInner p.val.1.1,
      (min p.val.1.2 p.val.2,max p.val.1.2 p.val.2))

theorem faceData_mem : ∀ p : FullFace, faceData p∈sourceFaces := by decide

def embedFace (p : FullFace) : SourceFace := ⟨faceData p,faceData_mem p⟩

theorem embedFace_bijective : Function.Bijective embedFace := by decide

end OperatorDerivativeRewrite.Foundation.OneSidedCapComplex
