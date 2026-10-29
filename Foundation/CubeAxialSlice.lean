import Foundation.CubeInvariantTransfer
import Foundation.FourCubeBoundaryCoercivity

/-! Actual five-chord axial slice of the spatial cube. The nonlinear bound is
modulo gauge, not the impossible raw-link coercivity on a larger lattice. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CubeAxialSlice
open QuaternionSU2Representation CubeTemporalSlab CubeWilsonSlab
open FourCubePinnedCoercivity

private instance vertexDecidableEq : DecidableEq SpatialVertex :=
  fun v w => decidable_of_decidable_of_iff (p := ∀ i,v i=w i) funext_iff.symm

abbrev Chords := Fin 5 → SU2

def chordEdge : Fin 5 → SpatialEdge := ![
  ⟨(![0,1,0],0),by decide +kernel⟩,
  ⟨(![0,0,1],0),by decide +kernel⟩,
  ⟨(![0,1,1],0),by decide +kernel⟩,
  ⟨(![0,0,1],1),by decide +kernel⟩,
  ⟨(![1,0,1],1),by decide +kernel⟩]

def chordLabel (e : SpatialEdge) : Option (Fin 5) :=
  if e.val.2=0 then
    if e.val.1 1=0 then (if e.val.1 2=1 then some 1 else none)
    else (if e.val.1 2=0 then some 0 else some 2)
  else if e.val.2=1 ∧ e.val.1 2=1 then
    (if e.val.1 0=0 then some 3 else some 4)
  else none

def axialState (q : Chords) (e : SpatialEdge) : SU2 := (chordLabel e).elim 1 q

theorem chord_label : ∀ i : Fin 5, chordLabel (chordEdge i)=some i := by
  intro i
  fin_cases i <;> norm_num [chordLabel,chordEdge]

theorem axial_chord (q : Chords) (i : Fin 5) : axialState q (chordEdge i)=q i := by
  simp only [axialState,chord_label,Option.elim_some]

def faceEnum : Fin 6 → SpatialFace := ![
  ⟨(![0,0,0],(0,1)),by decide +kernel⟩,
  ⟨(![0,0,1],(0,1)),by decide +kernel⟩,
  ⟨(![0,0,0],(0,2)),by decide +kernel⟩,
  ⟨(![0,1,0],(0,2)),by decide +kernel⟩,
  ⟨(![0,0,0],(1,2)),by decide +kernel⟩,
  ⟨(![1,0,0],(1,2)),by decide +kernel⟩]

theorem face_enum_bijective : Function.Bijective faceEnum := by decide +kernel

def axialWord (q : Chords) : Fin 6 → SU2 :=
  ![(q 0)⁻¹,q 1*q 4*(q 2)⁻¹*(q 3)⁻¹,(q 1)⁻¹,q 0*(q 2)⁻¹,(q 3)⁻¹,(q 4)⁻¹]

/-- Six exact noncommutative plaquette words of the actual cube. -/
theorem axial_words (q : Chords) : ∀ i : Fin 6,
    spatialWord (axialState q) (faceEnum i)=axialWord q i := by
  intro i
  fin_cases i <;>
    norm_num [spatialWord,axialState,chordLabel,faceEdge,rawFaceEdge,faceEnum,
      axialWord,shift,Function.update] <;> group

/-- Exact nonlinear action; no quadratic approximation is involved. -/
theorem axial_action (q : Chords) :
    spatialAction (axialState q)=defect (q 0)+defect (q 1)+defect (q 0*(q 2)⁻¹)+
      defect (q 3)+defect (q 4)+defect (q 1*q 4*(q 2)⁻¹*(q 3)⁻¹) := by
  have h := Fintype.sum_equiv (Equiv.ofBijective faceEnum face_enum_bijective)
    (fun i => defect (spatialWord (axialState q) (faceEnum i)))
    (fun p => defect (spatialWord (axialState q) p)) (fun i => rfl)
  change (∑ i : Fin 6, defect (spatialWord (axialState q) (faceEnum i)))=
    spatialAction (axialState q) at h
  rw [← h]
  simp_rw [axial_words]
  simp [axialWord,Fin.sum_univ_succ,defect_inv]
  <;> ring

def chordEnergy (q : Chords) : ℝ := ∑ i,defect (q i)

/-- The missing chord is controlled by its adjacent face and one chord. -/
private theorem third_control (q : Chords) :
    defect (q 2) ≤ 3*(defect (q 0*(q 2)⁻¹)+defect (q 0)) := by
  have h := FourCubeBoundaryCoercivity.defect_mul ((q 0*(q 2)⁻¹)⁻¹) (q 0)
  have he : (q 0*(q 2)⁻¹)⁻¹*q 0=q 2 := by group
  rw [he,defect_inv] at h
  exact h

/-- Global finite-cell nonlinear confinement on the actual axial slice. -/
theorem axial_coercive (q : Chords) : chordEnergy q ≤ 4*spatialAction (axialState q) := by
  rw [axial_action]
  unfold chordEnergy
  simp only [Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,Finset.sum_empty,add_zero]
  have h := third_control q
  have h0 := defect_nonneg (q 0)
  have h1 := defect_nonneg (q 1)
  have h2 := defect_nonneg (q 0*(q 2)⁻¹)
  have h3 := defect_nonneg (q 3)
  have h4 := defect_nonneg (q 4)
  have h5 := defect_nonneg (q 1*q 4*(q 2)⁻¹*(q 3)⁻¹)
  norm_num at *
  linarith

end OperatorDerivativeRewrite.Foundation.CubeAxialSlice
