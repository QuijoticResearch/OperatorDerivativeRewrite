import Foundation.PeriodicSU2FlatHolonomy
import Foundation.CubeTemporalSlab

/-! Temporal slices of the actual side-four periodic four-dimensional SU2 field.
No boundary links are pinned and no temporal links are omitted. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicTemporalSlab
open QuaternionSU2Representation

abbrev SpatialVertex := Fin 3 → ZMod 4
abbrev SpatialEdge := SpatialVertex × Fin 3
abbrev SpatialFace := {p : SpatialVertex × (Fin 3 × Fin 3) // p.2.1 < p.2.2}
abbrev State := SpatialEdge → SU2
abbrev Gauge := SpatialVertex → SU2

def shift (v : SpatialVertex) (i : Fin 3) : SpatialVertex :=
  fun k => v k + if k=i then 1 else 0

def embed (v : SpatialVertex) (t : ZMod 4) : PeriodicInteriorGaugeKernel.Vertex :=
  Fin.lastCases t v

theorem embed_spatial (v : SpatialVertex) (t : ZMod 4) (i : Fin 3) :
    embed v t i.castSucc=v i := Fin.lastCases_castSucc _

theorem embed_time (v : SpatialVertex) (t : ZMod 4) :
    embed v t (Fin.last 3)=t := Fin.lastCases_last

theorem embed_shift_spatial (v : SpatialVertex) (t : ZMod 4) (i : Fin 3) :
    PeriodicInteriorGaugeKernel.shift (embed v t) i.castSucc=embed (shift v i) t := by
  funext k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · change (t + if (Fin.last 3)=i.castSucc then 1 else 0)=t
    rw [if_neg (Ne.symm (Fin.castSucc_ne_last i)),add_zero]
  · simp only [PeriodicInteriorGaugeKernel.shift,embed_spatial,shift,Fin.castSucc_inj]

theorem embed_shift_time (v : SpatialVertex) (t : ZMod 4) :
    PeriodicInteriorGaugeKernel.shift (embed v t) (Fin.last 3)=embed v (t+1) := by
  funext k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · change (t + if (Fin.last 3)=(Fin.last 3) then 1 else 0)=t+1
    simp only [ite_true]
  · simp only [PeriodicInteriorGaugeKernel.shift,embed_spatial]
    rw [if_neg (Fin.castSucc_ne_last j),add_zero]

def spatialField (L : PeriodicSU2FlatHolonomy.Links) (t : ZMod 4) : State :=
  fun e => L (embed e.1 t,e.2.castSucc)

def temporalField (L : PeriodicSU2FlatHolonomy.Links) (t : ZMod 4) : Gauge :=
  fun v => L (embed v t,Fin.last 3)

def spatialWord (U : State) (p : SpatialFace) : SU2 :=
  U (p.val.1,p.val.2.1)*U (shift p.val.1 p.val.2.1,p.val.2.2)*
    (U (shift p.val.1 p.val.2.2,p.val.2.1))⁻¹*(U (p.val.1,p.val.2.2))⁻¹

def temporalWord (U V : State) (g : Gauge) (e : SpatialEdge) : SU2 :=
  U e*g (shift e.1 e.2)*(V e)⁻¹*(g e.1)⁻¹

theorem spatial_word (L : PeriodicSU2FlatHolonomy.Links) (t : ZMod 4) (p : SpatialFace) :
    PeriodicSU2FlatHolonomy.plaquette L (embed p.val.1 t)
      p.val.2.1.castSucc p.val.2.2.castSucc=spatialWord (spatialField L t) p := by
  simp [PeriodicSU2FlatHolonomy.plaquette,spatialWord,spatialField,embed_shift_spatial]

theorem temporal_word (L : PeriodicSU2FlatHolonomy.Links) (t : ZMod 4) (e : SpatialEdge) :
    PeriodicSU2FlatHolonomy.plaquette L (embed e.1 t) e.2.castSucc (Fin.last 3)=
      temporalWord (spatialField L t) (spatialField L (t+1)) (temporalField L t) e := by
  unfold PeriodicSU2FlatHolonomy.plaquette temporalWord spatialField temporalField
  rw [embed_shift_spatial,embed_shift_time]

theorem edge_count : Fintype.card SpatialEdge=192 := by
  norm_num [SpatialEdge,SpatialVertex,Fintype.card_prod,Fintype.card_fun]

theorem face_count : Fintype.card SpatialFace=192 := by
  let e : SpatialFace ≃ SpatialVertex × {ij : Fin 3 × Fin 3 // ij.1 < ij.2} :=
    { toFun := fun p => (p.val.1,⟨p.val.2,p.property⟩)
      invFun := fun p => ⟨(p.1,p.2.val),p.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e,Fintype.card_prod]
  have hc : Fintype.card {ij : Fin 3 × Fin 3 // ij.1 < ij.2}=3 := by decide
  norm_num [hc,SpatialVertex,Fintype.card_fun]

end OperatorDerivativeRewrite.Foundation.PeriodicTemporalSlab
