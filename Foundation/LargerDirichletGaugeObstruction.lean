import Foundation.FourCubeCompletedHaar

/-! Explicit scope obstruction for extending the thin-cell link-defect bound.
A216-link4D core has a genuinely interior gauge vertex; frozen exterior links
can coexist with nontrivial core links and zero action on ALL2400 box plaquettes.
This concerns gauge-variant link coercivity, NOT the physical mass gap. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.LargerDirichletGaugeObstruction
open QuaternionSU2Representation FourCubePinnedCoercivity

abbrev Vertex := Fin 4 → ℤ
abbrev Edge := Vertex × Fin 4
abbrev Face := Vertex × (Fin 4 × Fin 4)

def center : Vertex := fun _ => 1
def shift (v : Vertex) (a : Fin 4) : Vertex := fun j => v j+if j=a then 1 else 0

def Core (e : Edge) : Prop := (∀ j : Fin 4,0≤e.1 j ∧ e.1 j≤2) ∧ e.1 e.2<2

def coreIndexEdges : Finset ((Fin 4 → Fin 3) × Fin 4) :=
  Finset.univ.filter (fun e => (e.1 e.2).val<2)
def coreEdgeMap (e : (Fin 4 → Fin 3) × Fin 4) : Edge := (fun j => (e.1 j).val,e.2)
def coreEdges : Finset Edge := coreIndexEdges.image coreEdgeMap

def boxIndexFaces : Finset ((Fin 4 → Fin 5) × (Fin 4 × Fin 4)) :=
  Finset.univ.filter (fun p => p.2.1<p.2.2 ∧ (p.1 p.2.1).val<4 ∧ (p.1 p.2.2).val<4)
def boxFaceMap (p : (Fin 4 → Fin 5) × (Fin 4 × Fin 4)) : Face :=
  (fun j => ((p.1 j).val : ℤ)-1,p.2)
def boxFaces : Finset Face := boxIndexFaces.image boxFaceMap

def gauge (U : SU2) (v : Vertex) : SU2 := if v=center then U else 1
def links (U : SU2) (e : Edge) : SU2 := gauge U e.1*(gauge U (shift e.1 e.2))⁻¹

def plaquette (f : Edge → SU2) (p : Face) : SU2 :=
  f (p.1,p.2.1)*f (shift p.1 p.2.1,p.2.2)*
    (f (shift p.1 p.2.2,p.2.1))⁻¹*(f (p.1,p.2.2))⁻¹

def wilsonAction (f : Edge → SU2) (F : Finset Face) : ℝ := ∑ p∈F,defect (plaquette f p)
def linkEnergy (f : Edge → SU2) : ℝ := ∑ e∈coreEdges,defect (f e)

theorem shift_comm (v : Vertex) (a b : Fin 4) : shift (shift v a) b=shift (shift v b) a := by
  funext j
  dsimp [shift]
  ring

theorem flat (U : SU2) (p : Face) : plaquette (links U) p=1 := by
  dsimp [plaquette,links]
  rw [shift_comm p.1 p.2.1 p.2.2]
  group

theorem coreEdgeMap_injective : Function.Injective coreEdgeMap := by
  intro e f h
  apply Prod.ext
  · funext j
    apply Fin.ext
    have hj := congrArg (fun e : Edge => e.1 j) h
    dsimp [coreEdgeMap] at hj
    omega
  · exact congrArg (fun e : Edge => e.2) h

theorem boxFaceMap_injective : Function.Injective boxFaceMap := by
  intro p q h
  apply Prod.ext
  · funext j
    apply Fin.ext
    have hj := congrArg (fun p : Face => p.1 j) h
    dsimp [boxFaceMap] at hj
    omega
  · exact congrArg (fun p : Face => p.2) h

theorem core_edges_card : coreEdges.card=216 := by
  rw [coreEdges,Finset.card_image_of_injective _ coreEdgeMap_injective]
  decide +kernel

theorem box_faces_card : boxFaces.card=2400 := by
  rw [boxFaces,Finset.card_image_of_injective _ boxFaceMap_injective]
  decide +kernel

attribute [local irreducible] coreEdges coreIndexEdges boxFaces boxIndexFaces

theorem core_edges_iff (e : Edge) : e∈coreEdges ↔ Core e := by
  constructor
  · intro h
    rw [coreEdges] at h
    obtain ⟨⟨v,a⟩,hv,rfl⟩ := Finset.mem_image.mp h
    have hm : (v a).val<2 := by simpa [coreIndexEdges] using hv
    constructor
    · intro j
      have hj := (v j).isLt
      change (0 : ℤ)≤(v j).val ∧ ((v j).val : ℤ)≤2
      omega
    · change ((v a).val : ℤ)<2
      omega
  · rintro ⟨hv,ha⟩
    let v : Fin 4 → Fin 3 := fun j => ⟨(e.1 j).toNat,by have hj := hv j; omega⟩
    have hvertex : (fun j => ((v j).val : ℤ))=e.1 := by
      funext j
      dsimp [v]
      have hj := hv j
      omega
    have hm : (v,e.2)∈coreIndexEdges := by
      simp only [coreIndexEdges,Finset.mem_filter,Finset.mem_univ,true_and]
      change (e.1 e.2).toNat<2
      have hj := hv e.2
      omega
    rw [coreEdges]
    exact Finset.mem_image.mpr ⟨(v,e.2),hm,Prod.ext hvertex rfl⟩

theorem center_core (a : Fin 4) : Core (center,a) := by
  constructor
  · intro j
    norm_num [center]
  · norm_num [center]

private theorem predecessor_core (v : Vertex) (a : Fin 4) (h : shift v a=center) : Core (v,a) := by
  constructor
  · intro j
    change (0 : ℤ)≤v j ∧ v j≤2
    have hj := congrArg (fun v : Vertex => v j) h
    dsimp [shift,center] at hj
    split_ifs at hj <;> omega
  · change v a<2
    have hj := congrArg (fun v : Vertex => v a) h
    simp only [shift,center,ite_true] at hj
    omega

/-- Every link outside the216-link core is ACTUAL identity, not an omitted action term. -/
theorem frozen_exterior (U : SU2) (e : Edge) (he : e∉coreEdges) : links U e=1 := by
  have hn : ¬Core e := fun h => he ((core_edges_iff e).mpr h)
  have hv : e.1≠center := by
    intro h
    apply hn
    change Core (e.1,e.2)
    rw [h]
    exact center_core e.2
  have hs : shift e.1 e.2≠center := fun h => hn (predecessor_core _ _ h)
  simp [links,gauge,hv,hs]

theorem center_link (U : SU2) : links U (center,0)=U := by
  have hs : shift center 0≠center := by
    intro h
    have hh := congrArg (fun v : Vertex => v 0) h
    norm_num [shift,center] at hh
  simp [links,gauge,hs]

theorem action_zero (U : SU2) (F : Finset Face) : wilsonAction (links U) F=0 := by
  simp [wilsonAction,flat,defect_one]

theorem core_energy_positive (U : SU2) (hU : U≠1) : 0<linkEnergy (links U) := by
  have hd : 0<defect U := lt_of_le_of_ne (defect_nonneg U)
    (fun h => hU ((defect_zero_iff U).mp h.symm))
  have hm : (center,0)∈coreEdges := (core_edges_iff _).mpr (center_core 0)
  have hs := Finset.single_le_sum (fun e (_ : e∈coreEdges) => defect_nonneg (links U e)) hm
  change defect (links U (center,0)) ≤ linkEnergy (links U) at hs
  rw [center_link] at hs
  exact hd.trans_le hs

/-- No positive raw-link coercivity constant survives this actual larger Dirichlet core. -/
theorem no_link_coercivity (U : SU2) (hU : U≠1) (c : ℝ) (hc : 0<c) :
    ¬c*linkEnergy (links U) ≤ wilsonAction (links U) boxFaces := by
  rw [action_zero]
  exact not_le_of_gt (mul_pos hc (core_energy_positive U hU))

/-- Explicit nonempty SU(2) witness, with full frozen exterior and flat plaquettes. -/
theorem exists_flat_nontrivial : ∃ U : SU2,U≠1 ∧
    (∀ e : Edge,e∉coreEdges → links U e=1) ∧
    wilsonAction (links U) boxFaces=0 ∧ 0<linkEnergy (links U) := by
  let U := SU2JointPlaquetteCubic.axis 0 Real.pi
  have hU : U≠1 := by
    intro h
    have hh := congrArg halfTrace h
    rw [FourCubeWilsonCubic.axis_trace,FourCubeWilsonCubic.trace_one,Real.cos_pi] at hh
    norm_num at hh
  exact ⟨U,hU,frozen_exterior U,action_zero U boxFaces,core_energy_positive U hU⟩

end OperatorDerivativeRewrite.Foundation.LargerDirichletGaugeObstruction
