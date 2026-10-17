import Foundation.HigherHeatObservationRefinement

/-! Finite signed position laws agree when a doubled time grid is restricted to its old times. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatGridDoubling
open HigherHeatSignedLaws HigherHeatCylinderFourier HigherHeatBlockCoarsening
open HigherHeatObservationRefinement

def pairBlock {n : ℕ} (j : Fin (2*n)) : Fin n := ⟨j.val/2,by omega⟩

def evenIndex {n : ℕ} (i : Fin n) : Fin (2*n) := ⟨2*i.val,by omega⟩

def oddIndex {n : ℕ} (i : Fin n) : Fin (2*n) := ⟨2*i.val+1,by omega⟩

theorem pairBlock_surjective (n : ℕ) : Function.Surjective (@pairBlock n) := by
  intro i
  refine ⟨evenIndex i,?_⟩
  apply Fin.ext
  simp [pairBlock,evenIndex]

theorem even_ne_odd {n : ℕ} (i : Fin n) : evenIndex i ≠ oddIndex i := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [evenIndex,oddIndex] at hv
  omega

theorem pair_fiber {n : ℕ} (i : Fin n) :
    Finset.univ.filter (fun j : Fin (2*n) => pairBlock j=i) = {evenIndex i,oddIndex i} := by
  classical
  ext j
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton,
    Fin.ext_iff,pairBlock,evenIndex,oddIndex]
  omega

theorem pair_times {n : ℕ} (s : ℝ≥0) (i : Fin n) :
    blockTimes pairBlock (fun _ : Fin (2*n) => s) i=s+s := by
  classical
  calc
    blockTimes pairBlock (fun _ : Fin (2*n) => s) i =
        ∑ j ∈ Finset.univ.filter (fun j : Fin (2*n) => pairBlock j=i), s := by
          simp only [blockTimes]
          congr 1
          ext j
          simp
    _ = ∑ j ∈ ({evenIndex i,oddIndex i} : Finset (Fin (2*n))), s :=
      congrArg (fun S : Finset (Fin (2*n)) => ∑ _j ∈ S, s) (pair_fiber i)
    _ = s+s := by simp [even_ne_odd i,two_mul]

def oldPositions {n : ℕ} (y : Fin (2*n) → ℝ) (i : Fin n) : ℝ := y (oddIndex i)

theorem oldPositions_measurable (n : ℕ) : Measurable (@oldPositions n) := by
  apply Measurable.of_eval
  intro i
  exact measurable_pi_apply _

theorem oldPositions_apply {n : ℕ} (x : Fin (2*n) → ℝ) :
    oldPositions (linearImage (cumulativeMatrix (2*n)) x)=blockPositions pairBlock x := by
  classical
  funext i
  change linearImage (cumulativeMatrix (2*n)) x (oddIndex i) = _
  rw [cumulative_apply]
  unfold blockPositions
  congr 1
  apply Finset.filter_congr
  intro j _
  change j.val ≤ 2*i.val+1 ↔ j.val/2 ≤ i.val
  omega

theorem position_doubling (n m : ℕ) (hm : 0 < m) (s : ℝ≥0) (hs : 0 < s) :
    (positionLaw (2*n) m hm (fun _ => s) (fun _ => hs)).map oldPositions =
      positionLaw n m hm (fun _ => s+s) (fun _ => add_pos hs hs) := by
  unfold positionLaw configurationLaw
  rw [map_comp _ _ _ (linearImage_measurable _) (oldPositions_measurable n)]
  have he : oldPositions ∘ linearImage (cumulativeMatrix (2*n)) = blockPositions pairBlock := by
    funext x
    exact oldPositions_apply x
  rw [he]
  have hr := position_refinement m hm pairBlock (pairBlock_surjective n)
    (fun _ : Fin (2*n) => s) (fun _ => hs)
  have ht : blockTimes pairBlock (fun _ : Fin (2*n) => s) = fun _ : Fin n => s+s := by
    funext i
    exact pair_times s i
  simpa only [positionLaw,configurationLaw,ht] using hr

end OperatorDerivativeRewrite.Foundation.HigherHeatGridDoubling
