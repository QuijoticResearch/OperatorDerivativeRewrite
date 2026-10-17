import Foundation.OneSidedCapPoincare

/-! Signed transport of full cap rows to canonical lattice plaquette rows. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.OneSidedSourceRows
open OneSidedBlockIncidence OneSidedBlockKernel OneSidedBlockRank OneSidedCapComplex
  OneSidedCapPoincare
set_option maxRecDepth 65536
set_option maxHeartbeats 128000000
set_option backward.isDefEq.respectTransparency false

abbrev WideField := WideEdge → ℝ

def innerEdges (p : Inner) : Fin 4 → Interior :=
  ![⟨(p.val.1,p.val.2.1),(inner_edge_geometry p p.property).1⟩,
    ⟨(shifted p.val.1 p.val.2.1,p.val.2.2),(inner_edge_geometry p p.property).2.1⟩,
    ⟨(shifted p.val.1 p.val.2.2,p.val.2.1),(inner_edge_geometry p p.property).2.2.1⟩,
    ⟨(p.val.1,p.val.2.2),(inner_edge_geometry p p.property).2.2.2⟩]

def rowEdges : FullFace → Fin 4 → FullEdge
  | .inl p => fun t => .inl (innerEdges p t)
  | .inr p => ![.inl (ribbonInterior p),.inr (.inl (capHigh p)),
      .inr (.inr p),.inr (.inl (capLow p))]

def wideEdges (p : SourceFace) : Fin 4 → WideEdge :=
  ![(p.val.1,p.val.2.1),(wideShift p.val.1 p.val.2.1,p.val.2.2),
    (wideShift p.val.1 p.val.2.2,p.val.2.1),(p.val.1,p.val.2.2)]

def flipped : FullFace → Bool
  | .inl _ => false
  | .inr p => decide (p.val.2<p.val.1.2)

def rowSign (p : FullFace) : ℝ := if flipped p then -1 else 1

theorem row_geometry : ∀ p : FullFace, ∀ t : Fin 4,
    embedEdge (rowEdges p t)=wideEdges (embedFace p) (if flipped p then t.rev else t) := by decide

def faceCurl (f : FullField) : FullFace → ℝ := Sum.elim (d1 f).1 (d1 f).2

def pullWide (f : WideField) : FullField := fun e => f (embedEdge e)

def wideCurl (f : WideField) (p : SourceFace) : ℝ :=
  f (wideEdges p 0)+f (wideEdges p 1)-f (wideEdges p 2)-f (wideEdges p 3)

theorem row_formula (f : FullField) (p : FullFace) : faceCurl f p=
    f (rowEdges p 0)+f (rowEdges p 1)-f (rowEdges p 2)-f (rowEdges p 3) := by
  cases p with
  | inl p =>
    have he (e : EdgeData) (h : e∈edges) :
        extend (interiorPart f) e=f (.inl ⟨e,h⟩) := by
      simp [extend,h,interiorPart]
    obtain ⟨h1,h2,h3,h4⟩ := inner_edge_geometry p p.property
    change realCurl (extend (interiorPart f)) p=_
    unfold realCurl
    rw [he _ h1,he _ h2,he _ h3,he _ h4]
    rfl
  | inr p => rfl

theorem row_transport (f : WideField) (p : FullFace) :
    faceCurl (pullWide f) p=rowSign p*wideCurl f (embedFace p) := by
  rw [row_formula]
  simp only [pullWide,row_geometry]
  cases h : flipped p <;> simp [h,rowSign,wideCurl,Fin.rev] <;> ring

def sourceEdges : Finset WideEdge :=
  Finset.univ.biUnion (fun p : SourceFace => Finset.univ.image (wideEdges p))

abbrev SourceEdge := {e : WideEdge // e∈sourceEdges}

theorem sourceEdges_card : sourceEdges.card=112 := by decide

theorem embedEdge_mem : ∀ e : FullEdge, embedEdge e∈sourceEdges := by decide

def sourceEdgeMap (e : FullEdge) : SourceEdge := ⟨embedEdge e,embedEdge_mem e⟩

theorem sourceEdgeMap_bijective : Function.Bijective sourceEdgeMap := by decide

theorem interior_embedding : ∀ i : Interior, wideInterior (embedEdge (.inl i)) := by decide

theorem boundary_embedding : ∀ b : Boundary, ¬wideInterior (embedEdge (.inr b)) := by decide

theorem interior_classification (e : FullEdge) :
    wideInterior (embedEdge e) ↔ ∃ i : Interior, e=Sum.inl i := by
  cases e with
  | inl i => exact ⟨fun _ => ⟨i,rfl⟩,fun _ => interior_embedding i⟩
  | inr b => simp [boundary_embedding b]

def edgeEquiv : FullEdge ≃ SourceEdge := Equiv.ofBijective sourceEdgeMap sourceEdgeMap_bijective

def liftWide (f : FullField) (q : WideEdge) : ℝ :=
  if hq : q∈sourceEdges then f (edgeEquiv.symm ⟨q,hq⟩) else 0

theorem pull_lift (f : FullField) : pullWide (liftWide f)=f := by
  funext e
  change (if hq : embedEdge e∈sourceEdges then f (edgeEquiv.symm ⟨embedEdge e,hq⟩) else 0)=f e
  rw [dif_pos (embedEdge_mem e)]
  change f (edgeEquiv.symm (edgeEquiv e))=f e
  rw [Equiv.symm_apply_apply]

def capEnergy (f : FullField) : ℝ := ∑ p : FullFace, (faceCurl f p)^2

def sourceEnergy (f : WideField) : ℝ := ∑ p : SourceFace, (wideCurl f p)^2

theorem energy_transport (f : WideField) : capEnergy (pullWide f)=sourceEnergy f := by
  calc
    _ = ∑ p : FullFace, (wideCurl f (embedFace p))^2 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [row_transport]
      cases h : flipped p <;> simp [rowSign,h]
    _ = sourceEnergy f := by
      exact Fintype.sum_equiv (Equiv.ofBijective embedFace embedFace_bijective)
        (fun p => (wideCurl f (embedFace p))^2) (fun p => (wideCurl f p)^2) (fun _ => rfl)

theorem lifted_energy (f : FullField) : capEnergy f=sourceEnergy (liftWide f) := by
  rw [← energy_transport,pull_lift]

theorem d1_zero_iff_rows (f : FullField) : d1 f=0 ↔ ∀ p : FullFace, faceCurl f p=0 := by
  constructor
  · intro h p
    cases p <;> simp [faceCurl,h]
  · intro h
    apply Prod.ext <;> funext p
    · exact h (.inl p)
    · exact h (.inr p)

theorem source_closed_iff (f : WideField) :
    (∀ p : SourceFace, wideCurl f p=0) ↔ d1 (pullWide f)=0 := by
  rw [d1_zero_iff_rows]
  constructor
  · intro h p
    rw [row_transport,h,mul_zero]
  · intro h q
    obtain ⟨p,rfl⟩ := embedFace_bijective.2 q
    have hp := h p
    rw [row_transport] at hp
    cases hf : flipped p <;> simpa [rowSign,hf] using hp

theorem source_closed_has_potential (f : WideField) (hf : ∀ p : SourceFace, wideCurl f p=0) :
    ∃ phi : Potential, d0 phi=pullWide f :=
  (closed_iff_gradient (pullWide f)).mp ((source_closed_iff f).mp hf)

end OperatorDerivativeRewrite.Foundation.OneSidedSourceRows
