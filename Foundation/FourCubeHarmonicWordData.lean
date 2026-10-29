import Foundation.FourCubeHarmonicIntegerData

/-! Exact ordered face-word certificate for the actual harmonic cubic. -/
namespace OperatorDerivativeRewrite.Foundation.FourCubeHarmonicWordData
open OneSidedBlockIncidence OneSidedBlockRank OneSidedCapComplex OneSidedSourceRows
open OneSidedSourceMatrixData OneSidedBoundaryCycleData OneSidedSparseSourceData

def edgePoint : (Fin 32 ⊕ Fin 80) → FullEdge := Sum.map interiorPoint point

def slot (p : Fin 72) (i : Fin 4) : Fin 4 := if flipped (facePoint p) then i.rev else i

theorem source_links : ∀ (p : Fin 72) (i : Fin 4),
    wideEdges (embedFace (facePoint p)) i=embedEdge (edgePoint (rowLink p i)) := by
  intro p
  fin_cases p <;> decide +kernel

theorem actual_rows (p : Fin 72) (i : Fin 4) :
    rowEdges (facePoint p) i=edgePoint (rowLink p (slot p i)) := by
  apply sourceEdgeMap_bijective.injective
  apply Subtype.ext
  change embedEdge (rowEdges (facePoint p) i)=embedEdge (edgePoint (rowLink p (slot p i)))
  rw [row_geometry]
  exact source_links p (slot p i)

def word (p : Fin 72) (i : Fin 4) (a : Fin 3) : ℤ :=
  OneSidedSparseSourceData.rowSign i*FourCubeHarmonicIntegerData.linkValue (rowLink p (slot p i)) a

def det3 (u v w : Fin 3 → ℤ) : ℤ :=
  u 0*(v 1*w 2-v 2*w 1)-u 1*(v 0*w 2-v 2*w 0)+u 2*(v 0*w 1-v 1*w 0)

def cubicInt (w : Fin 4 → Fin 3 → ℤ) : ℤ :=
  det3 (w 0) (w 1) (w 2)+det3 (w 0) (w 1) (w 3)+
    det3 (w 0) (w 2) (w 3)+det3 (w 1) (w 2) (w 3)

theorem cubic_total : (∑ p : Fin 72,cubicInt (word p))=89146927712029176 := by decide +kernel

end OperatorDerivativeRewrite.Foundation.FourCubeHarmonicWordData
