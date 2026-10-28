import Foundation.OneSidedBlockIncidence
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! Exact reuse of the existing one-sided four-cube incidence. The count
serves the joint Wilson cubic audit, not a new general gauge library. -/
namespace OperatorDerivativeRewrite.Foundation.FourCubeChordIncidence
open OneSidedBlockIncidence

def faceEdge (p : FaceData) : Fin 4 → EdgeData :=
  ![(p.1,p.2.1),(shifted p.1 p.2.1,p.2.2),(shifted p.1 p.2.2,p.2.1),(p.1,p.2.2)]

def boundary (p : FaceData) : Finset EdgeData := Finset.univ.image (faceEdge p)

theorem boundary_subset : ∀ p∈innerFaces, boundary p ⊆ edges := by
  intro p
  rcases p with ⟨v,a,b⟩
  fin_cases v <;> fin_cases a <;> fin_cases b <;> decide

theorem boundary_card : ∀ p∈innerFaces, (boundary p).card=4 := by
  intro p
  rcases p with ⟨v,a,b⟩
  fin_cases v <;> fin_cases a <;> fin_cases b <;> decide

theorem edge_degree : ∀ e∈edges, (innerFaces.filter (fun p => e∈boundary p)).card=3 := by decide

/-- No tree hypothesis is hidden: ANY15 retained edges leave a square with
at least3 independent complementary edges. A spanning tree is a special case. -/
theorem three_chords (T : Finset EdgeData) (hT : T ⊆ edges) (hcard : T.card=15) :
    ∃ p∈innerFaces, ((edges \ T).filter (fun e => e∈boundary p)).card ≥ 3 := by
  let S := edges \ T
  have hS : S.card=17 := by rw [Finset.card_sdiff_of_subset hT,edges_card,hcard]
  have he := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := innerFaces) (t := S) (fun p e => e∈boundary p)
  have hr : (∑ e∈S,(innerFaces.filter (fun p => e∈boundary p)).card)=51 := by
    calc
      _ = ∑ e∈S,3 := Finset.sum_congr rfl (fun e he => edge_degree e (Finset.mem_sdiff.mp he).1)
      _ = 51 := by simp [hS]
  change (∑ p∈innerFaces,(S.filter (fun e => e∈boundary p)).card)=
    ∑ e∈S,(innerFaces.filter (fun p => e∈boundary p)).card at he
  rw [hr] at he
  by_contra hn
  push_neg at hn
  have hb : ∀ p∈innerFaces,(S.filter (fun e => e∈boundary p)).card ≤ 2 := by
    intro p hp
    have hh := hn p hp
    change (S.filter (fun e => e∈boundary p)).card < 3 at hh
    omega
  have hu := Finset.sum_le_sum hb
  have hsum : (∑ p∈innerFaces,(S.filter (fun e => e∈boundary p)).card) ≤ 48 := by
    simpa [innerFaces_card] using hu
  omega

/-- The existing24 faces, explicitly listed only for small symbolic sums. -/
def faceList : List FaceData := [
  ((![0,0,0,0] : Vertex),(0,1)),
  ((![0,0,0,0] : Vertex),(0,2)),
  ((![0,0,0,0] : Vertex),(0,3)),
  ((![0,0,0,0] : Vertex),(1,2)),
  ((![0,0,0,0] : Vertex),(1,3)),
  ((![0,0,0,0] : Vertex),(2,3)),
  ((![0,0,0,1] : Vertex),(0,1)),
  ((![0,0,0,1] : Vertex),(0,2)),
  ((![0,0,0,1] : Vertex),(1,2)),
  ((![0,0,1,0] : Vertex),(0,1)),
  ((![0,0,1,0] : Vertex),(0,3)),
  ((![0,0,1,0] : Vertex),(1,3)),
  ((![0,0,1,1] : Vertex),(0,1)),
  ((![0,1,0,0] : Vertex),(0,2)),
  ((![0,1,0,0] : Vertex),(0,3)),
  ((![0,1,0,0] : Vertex),(2,3)),
  ((![0,1,0,1] : Vertex),(0,2)),
  ((![0,1,1,0] : Vertex),(0,3)),
  ((![1,0,0,0] : Vertex),(1,2)),
  ((![1,0,0,0] : Vertex),(1,3)),
  ((![1,0,0,0] : Vertex),(2,3)),
  ((![1,0,0,1] : Vertex),(1,2)),
  ((![1,0,1,0] : Vertex),(1,3)),
  ((![1,1,0,0] : Vertex),(2,3))]

theorem innerFaces_eq : innerFaces=faceList.toFinset := by
  ext p
  rcases p with ⟨v,a,b⟩
  fin_cases v <;> fin_cases a <;> fin_cases b <;> decide

/-- Axial tree: each retained edge has no nonzero coordinate after its axis. -/
def axialTree : Finset EdgeData := edges.filter (fun e => ∀ j : Fin 4,e.2<j → e.1 j=0)

def parent (v : Vertex) : Vertex :=
  if v 3=1 then Function.update v 3 0 else
  if v 2=1 then Function.update v 2 0 else
  if v 1=1 then Function.update v 1 0 else origin

theorem axialTree_card : axialTree.card=15 := by decide

theorem parent_four : ∀ v : Vertex,(parent^[4]) v=origin := by decide

theorem tree_parent : ∀ e∈axialTree,parent (shifted e.1 e.2)=e.1 := by decide

theorem tree_incoming : ∀ v : Vertex,
    (axialTree.filter (fun e => shifted e.1 e.2=v)).card=if v=origin then 0 else 1 := by decide

end OperatorDerivativeRewrite.Foundation.FourCubeChordIncidence
