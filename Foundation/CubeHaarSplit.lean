import Foundation.CubeAxialGauge
import Mathlib.MeasureTheory.Constructions.Pi

/-! Exact product-Haar splitting of original tree and chord links of the actual cube. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.CubeHaarSplit
open QuaternionSU2Representation CubeTemporalSlab CubeWilsonSlab CubeAxialSlice CubeAxialGauge

abbrev TreeIndex := {e : SpatialEdge // chordLabel e=none}
abbrev ChordIndex := {e : SpatialEdge // ¬chordLabel e=none}
abbrev TreeState := TreeIndex → SU2
abbrev RawChords := ChordIndex → SU2

def treeHaar : Measure TreeState := Measure.pi (fun _ => law)
def rawChordHaar : Measure RawChords := Measure.pi (fun _ => law)
def chordHaar : Measure Chords := Measure.pi (fun _ => law)
instance tree_probability : IsProbabilityMeasure treeHaar := by unfold treeHaar; infer_instance
instance rawChord_probability : IsProbabilityMeasure rawChordHaar := by unfold rawChordHaar; infer_instance
instance chord_probability : IsProbabilityMeasure chordHaar := by unfold chordHaar; infer_instance

def split : State ≃ᵐ (TreeState × RawChords) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : SpatialEdge => SU2) (fun e => chordLabel e=none)

theorem split_preserving : MeasurePreserving split boundaryHaar (treeHaar.prod rawChordHaar) := by
  simpa only [split,boundaryHaar,treeHaar,rawChordHaar] using
    measurePreserving_piEquivPiSubtypeProd (fun _ : SpatialEdge => law) (fun e => chordLabel e=none)

def rawState (t : TreeState) (c : RawChords) : State := split.symm (t,c)

theorem rawState_tree (t : TreeState) (c : RawChords) (e : SpatialEdge)
    (h : chordLabel e=none) : rawState t c e=t ⟨e,h⟩ := by
  simp [rawState,split,MeasurableEquiv.piEquivPiSubtypeProd,h]

def indexedChord (i : Fin 5) : ChordIndex :=
  ⟨chordEdge i,by rw [chord_label]; simp⟩

private theorem chord_readback : ∀ (e : SpatialEdge) (i : Fin 5),
    chordLabel e=some i → chordEdge i=e := by decide +kernel

private theorem indexed_bijective : Function.Bijective indexedChord := by
  constructor
  · intro i j h
    have hh := congrArg (fun e : ChordIndex => chordLabel e.val) h
    simpa only [indexedChord,chord_label,Option.some.injEq] using hh
  · intro e
    cases h : chordLabel e.val with
    | none => exact False.elim (e.property h)
    | some i =>
      refine ⟨i,Subtype.ext ?_⟩
      exact chord_readback e.val i h

private def chordEquiv : Fin 5 ≃ ChordIndex := Equiv.ofBijective indexedChord indexed_bijective

def readChords (c : RawChords) : Chords := fun i => c (indexedChord i)

theorem readChords_preserving : MeasurePreserving readChords rawChordHaar chordHaar := by
  let E := MeasurableEquiv.piCongrLeft (fun _ : ChordIndex => SU2) chordEquiv
  have h : MeasurePreserving E chordHaar rawChordHaar :=
    measurePreserving_piCongrLeft (fun _ : ChordIndex => law) chordEquiv
  exact h.symm E

theorem rawState_chord (t : TreeState) (c : RawChords) (i : Fin 5) :
    rawState t c (chordEdge i)=readChords c i := by
  simp [rawState,split,MeasurableEquiv.piEquivPiSubtypeProd,chord_label,readChords,indexedChord]

/-- The rooted tree gauge depends only on the seven original tree variables. -/
theorem rooted_tree_only (t : TreeState) (c c' : RawChords) (v : SpatialVertex) :
    rootedGauge (rawState t c) v=rootedGauge (rawState t c') v := by
  have h (e : SpatialEdge) (he : chordLabel e=none) : rawState t c e=rawState t c' e := by
    rw [rawState_tree t c e he,rawState_tree t c' e he]
  unfold rootedGauge
  congr 2 <;> split_ifs <;> first | rfl | exact h _ (by rfl)

end OperatorDerivativeRewrite.Foundation.CubeHaarSplit
