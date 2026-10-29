import Foundation.FourCubeProjectiveInteraction
import Foundation.YMFiniteWilsonVacuum

/-! A correctly split unit4-cube: two12-link spatial boundaries and8 temporal links.
Finite geometry serves the homogeneous Wilson transfer comparison only. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CubeTemporalSlab
open OneSidedBlockIncidence QuaternionSU2Representation

abbrev SpatialVertex := Fin 3 → Fin 2
abbrev SpatialEdgeData := SpatialVertex × Fin 3
abbrev SpatialFaceData := SpatialVertex × (Fin 3 × Fin 3)
abbrev SpatialEdge := {e : SpatialEdgeData // e.1 e.2=0}
abbrev SpatialFace := {p : SpatialFaceData // p.2.1 < p.2.2 ∧ p.1 p.2.1=0 ∧ p.1 p.2.2=0}
abbrev State := SpatialEdge → SU2
abbrev Gauge := SpatialVertex → SU2

private instance spatialVertexDecidableEq : DecidableEq SpatialVertex :=
  fun v w => decidable_of_decidable_of_iff (p := ∀ i,v i=w i) funext_iff.symm

def shift (v : SpatialVertex) (a : Fin 3) : SpatialVertex := Function.update v a 1
def extend (v : SpatialVertex) (t : Fin 2) : Vertex := ![v 0,v 1,v 2,t]
def project (v : Vertex) : SpatialVertex := ![v 0,v 1,v 2]
def rawFaceEdge (p : SpatialFaceData) (i : Fin 4) : SpatialEdgeData :=
  ![(p.1,p.2.1),(shift p.1 p.2.1,p.2.2),
    (shift p.1 p.2.2,p.2.1),(p.1,p.2.2)] i

theorem rawFaceEdge_valid : ∀ p : SpatialFace,∀ i : Fin 4,
    (rawFaceEdge p.val i).1 (rawFaceEdge p.val i).2=0 := by decide +kernel

def faceEdge (p : SpatialFace) (i : Fin 4) : SpatialEdge :=
  ⟨rawFaceEdge p.val i,rawFaceEdge_valid p i⟩
def spatialFace (p : SpatialFace) (t : Fin 2) : FaceData :=
  (extend p.val.1 t,(p.val.2.1.castSucc,p.val.2.2.castSucc))
def temporalFace (e : SpatialEdge) : FaceData := (extend e.val.1 0,(e.val.2.castSucc,3))

def label (e : EdgeData) : Option ((Fin 2 × SpatialEdge) ⊕ SpatialVertex) :=
  if ha : e.2.val < 3 then
    let a : Fin 3 := ⟨e.2.val,ha⟩
    let v := project e.1
    if hv : v a=0 then some (.inl (e.1 3,⟨(v,a),hv⟩)) else none
  else if e.1 3=0 then some (.inr (project e.1)) else none

def link (U V : State) (g : Gauge) (e : EdgeData) : SU2 :=
  match label e with
  | none => 1
  | some (.inl (t,j)) => if t=0 then U j else V j
  | some (.inr v) => g v

def spatialWord (U : State) (p : SpatialFace) : SU2 :=
  U (faceEdge p 0)*U (faceEdge p 1)*(U (faceEdge p 2))⁻¹*(U (faceEdge p 3))⁻¹
def temporalWord (U V : State) (g : Gauge) (e : SpatialEdge) : SU2 :=
  U e*g (shift e.val.1 e.val.2)*(V e)⁻¹*(g e.val.1)⁻¹
def gaugeAction (g : Gauge) (V : State) (e : SpatialEdge) : SU2 :=
  g e.val.1*V e*(g (shift e.val.1 e.val.2))⁻¹

theorem vertex_count : Fintype.card SpatialVertex=8 := by decide +kernel
theorem edge_count : Fintype.card SpatialEdge=12 := by decide +kernel
theorem face_count : Fintype.card SpatialFace=6 := by decide +kernel

theorem faces_split : innerFaces=
    (Finset.univ.image (fun p : SpatialFace × Fin 2 => spatialFace p.1 p.2)) ∪
      (Finset.univ.image temporalFace) := by decide +kernel

theorem faces_disjoint : Disjoint
    (Finset.univ.image (fun p : SpatialFace × Fin 2 => spatialFace p.1 p.2))
      (Finset.univ.image temporalFace) := by decide +kernel

theorem spatialFace_injective : Function.Injective (fun p : SpatialFace × Fin 2 => spatialFace p.1 p.2) := by
  decide +kernel

theorem temporalFace_injective : Function.Injective temporalFace := by decide +kernel

/-- Kernel-checked48 spatial word slots, before any noncommutative rearrangement. -/
theorem spatial_labels : ∀ p : SpatialFace,∀ t : Fin 2,∀ i : Fin 4,
    label (FourCubeChordIncidence.faceEdge (spatialFace p t) i)=some (.inl (t,faceEdge p i)) := by
  intro p t i
  fin_cases p <;> fin_cases t <;> fin_cases i <;>
    norm_num [label,spatialFace,extend,project,faceEdge,rawFaceEdge,
      FourCubeChordIncidence.faceEdge,OneSidedBlockIncidence.shifted,shift,
      funext_iff,Fin.forall_fin_succ,Function.update_apply] <;> decide +kernel

/-- Kernel-checked48 temporal word slots, including both endpoint and vertex indices. -/
theorem temporal_labels : ∀ e : SpatialEdge,∀ i : Fin 4,
    label (FourCubeChordIncidence.faceEdge (temporalFace e) i)=
      (![some (.inl (0,e)),some (.inr (shift e.val.1 e.val.2)),
        some (.inl (1,e)),some (.inr e.val.1)] i) := by
  intro e i
  fin_cases e <;> fin_cases i <;>
    norm_num [label,temporalFace,extend,project,shift,
      FourCubeChordIncidence.faceEdge,OneSidedBlockIncidence.shifted,
      funext_iff,Fin.forall_fin_succ,Function.update_apply] <;> decide +kernel

theorem spatial_word (U V : State) (g : Gauge) (p : SpatialFace) (t : Fin 2) :
    link U V g (FourCubeChordIncidence.faceEdge (spatialFace p t) 0)*
      link U V g (FourCubeChordIncidence.faceEdge (spatialFace p t) 1)*
      (link U V g (FourCubeChordIncidence.faceEdge (spatialFace p t) 2))⁻¹*
      (link U V g (FourCubeChordIncidence.faceEdge (spatialFace p t) 3))⁻¹=
        spatialWord (if t=0 then U else V) p := by
  simp only [link,spatial_labels]
  split_ifs <;> rfl

theorem temporal_word (U V : State) (g : Gauge) (e : SpatialEdge) :
    link U V g (FourCubeChordIncidence.faceEdge (temporalFace e) 0)*
      link U V g (FourCubeChordIncidence.faceEdge (temporalFace e) 1)*
      (link U V g (FourCubeChordIncidence.faceEdge (temporalFace e) 2))⁻¹*
      (link U V g (FourCubeChordIncidence.faceEdge (temporalFace e) 3))⁻¹=
        temporalWord U V g e := by
  simp [link,temporal_labels,temporalWord]

theorem temporal_gauge_word (U V : State) (g : Gauge) (e : SpatialEdge) :
    temporalWord U V g e=U e*(gaugeAction g V e)⁻¹ := by
  unfold temporalWord gaugeAction
  group

end OperatorDerivativeRewrite.Foundation.CubeTemporalSlab
