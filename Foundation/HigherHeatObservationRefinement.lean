import Foundation.HigherHeatBlockCoarsening

/-! Actual finite signed observation laws are invariant under block refinement. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatObservationRefinement
open HigherHeatSignedLaws HigherHeatCylinderFourier HigherHeatBlockCoarsening

theorem map_comp {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (ν : SignedMeasure α) (f : α → β) (g : β → γ) (hf : Measurable f) (hg : Measurable g) :
    (ν.map f).map g=ν.map (g ∘ f) := by
  ext S hS
  rw [VectorMeasure.map_apply _ hg hS,VectorMeasure.map_apply _ hf (hg hS),
    VectorMeasure.map_apply _ (hg.comp hf) hS]
  rfl

variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]

theorem block_observation (p : ι → κ) (A : τ → κ → ℝ) (x : ι → ℝ) :
    linearImage A (linearImage (blockMatrix p) x)=linearImage (fun i j => A i (p j)) x := by
  classical
  funext i
  change (∑ k, A i k*linearImage (blockMatrix p) x k) = ∑ j, A i (p j)*x j
  simp_rw [block_apply,Finset.mul_sum]
  calc
    (∑ k, ∑ j ∈ Finset.univ.filter (fun j => p j=k), A i k*x j) =
        ∑ k, ∑ j ∈ Finset.univ.filter (fun j => p j=k), A i (p j)*x j := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j hj
      rw [(Finset.mem_filter.mp hj).2]
    _ = ∑ j, A i (p j)*x j := Finset.sum_fiberwise Finset.univ p _

theorem configuration_refinement (m : ℕ) (hm : 0 < m) (p : ι → κ) (hp : Function.Surjective p)
    (t : ι → ℝ≥0) (ht : ∀ j, 0 < t j) (A : τ → κ → ℝ) :
    configurationLaw m hm t ht (fun i j => A i (p j)) =
      configurationLaw m hm (blockTimes p t) (blockTimes_pos p hp t ht) A := by
  have h := congrArg (fun ν : SignedMeasure (κ → ℝ) => ν.map (linearImage A))
    (block_law m hm p hp t ht)
  unfold configurationLaw at h ⊢
  rw [map_comp _ _ _ (linearImage_measurable (blockMatrix p)) (linearImage_measurable A)] at h
  convert h using 1
  congr 1
  funext x
  exact (block_observation p A x).symm

def blockPositions {n : ℕ} (p : ι → Fin n) (x : ι → ℝ) (i : Fin n) : ℝ := by
  classical
  exact ∑ j ∈ Finset.univ.filter (fun j => p j ≤ i), x j

theorem blockPositions_eq {n : ℕ} (p : ι → Fin n) :
    blockPositions p=linearImage (fun i j => cumulativeMatrix n i (p j)) := by
  classical
  funext x i
  simp [blockPositions,linearImage,cumulativeMatrix,Finset.sum_filter]

theorem position_refinement {n : ℕ} (m : ℕ) (hm : 0 < m) (p : ι → Fin n)
    (hp : Function.Surjective p) (t : ι → ℝ≥0) (ht : ∀ j, 0 < t j) :
    (incrementLaw m hm t ht).map (blockPositions p) =
      positionLaw n m hm (blockTimes p t) (blockTimes_pos p hp t ht) := by
  rw [blockPositions_eq]
  exact configuration_refinement m hm p hp t ht (cumulativeMatrix n)

end OperatorDerivativeRewrite.Foundation.HigherHeatObservationRefinement
