import Foundation.SignedFourierUniqueness

/-! Exact finite block coarsening of genuine higher-order signed heat increments. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology Classical
namespace OperatorDerivativeRewrite.Foundation.HigherHeatBlockCoarsening
open HigherHeatSignedLaws HigherHeatCylinderFourier SignedDensityIntegral SignedFourierUniqueness
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def identityMatrix (i j : ι) : ℝ := if j=i then 1 else 0

theorem identity_apply (x : ι → ℝ) : linearImage identityMatrix x=x := by
  funext i
  simp [linearImage,identityMatrix,Finset.sum_ite_eq']

theorem identity_dual (ξ : ι → ℝ) : dualImage identityMatrix ξ=ξ := by
  funext j
  simp [dualImage,identityMatrix,Finset.sum_ite_eq]

theorem identity_law (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ j, 0 < t j) :
    configurationLaw m hm t ht (identityMatrix : ι → ι → ℝ)=incrementLaw m hm t ht := by
  unfold configurationLaw
  have he : (linearImage identityMatrix : (ι → ℝ) → (ι → ℝ))=id := funext identity_apply
  rw [he,VectorMeasure.map_id]

def blockMatrix (p : ι → κ) (i : κ) (j : ι) : ℝ := if p j=i then 1 else 0

def blockTimes (p : ι → κ) (t : ι → ℝ≥0) (i : κ) : ℝ≥0 :=
  ∑ j ∈ Finset.univ.filter (fun j => p j=i), t j

theorem blockTimes_pos (p : ι → κ) (hp : Function.Surjective p)
    (t : ι → ℝ≥0) (ht : ∀ j, 0 < t j) (i : κ) : 0 < blockTimes p t i := by
  obtain ⟨j,hj⟩ := hp i
  unfold blockTimes
  apply Finset.sum_pos'
  · intro k _
    positivity
  · exact ⟨j,by simp [hj],ht j⟩

theorem block_dual (p : ι → κ) (ξ : κ → ℝ) (j : ι) :
    dualImage (blockMatrix p) ξ j=ξ (p j) := by
  simp [dualImage,blockMatrix,Finset.sum_ite_eq]

theorem symbol_sum (m : ℕ) (s : Finset ι) (t : ι → ℝ≥0) (ξ : ℝ) :
    HigherHeatL2.symbol m (∑ j ∈ s, t j) ξ = ∏ j ∈ s, HigherHeatL2.symbol m (t j) ξ := by
  induction s using Finset.induction_on with
  | empty => simp [HigherHeatL2.symbol_zero]
  | @insert j s hj ih => simp [hj,HigherHeatL2.symbol_add,ih]

theorem block_symbol_product (m : ℕ) (p : ι → κ) (t : ι → ℝ≥0) (ξ : κ → ℝ) :
    (∏ j, HigherHeatL2.symbol m (t j) (ξ (p j))) =
      ∏ i, HigherHeatL2.symbol m (blockTimes p t i) (ξ i) := by
  rw [← Finset.prod_fiberwise Finset.univ p (fun j => HigherHeatL2.symbol m (t j) (ξ (p j)))]
  apply Finset.prod_congr rfl
  intro i _
  rw [blockTimes,symbol_sum]
  apply Finset.prod_congr rfl
  intro j hj
  rw [(Finset.mem_filter.mp hj).2]

theorem block_law (m : ℕ) (hm : 0 < m) (p : ι → κ) (hp : Function.Surjective p)
    (t : ι → ℝ≥0) (ht : ∀ j, 0 < t j) :
    configurationLaw m hm t ht (blockMatrix p) =
      incrementLaw m hm (blockTimes p t) (blockTimes_pos p hp t ht) := by
  apply finite_signed_ext
  intro ξ
  rw [configurationLaw_fourier,← identity_law m hm (blockTimes p t) (blockTimes_pos p hp t ht),
    configurationLaw_fourier,identity_dual]
  simp_rw [block_dual]
  exact block_symbol_product m p t ξ

theorem block_apply (p : ι → κ) (x : ι → ℝ) (i : κ) :
    linearImage (blockMatrix p) x i = ∑ j ∈ Finset.univ.filter (fun j => p j=i), x j := by
  simp [linearImage,blockMatrix,Finset.sum_filter]

theorem block_sum_law (m : ℕ) (hm : 0 < m) (p : ι → κ) (hp : Function.Surjective p)
    (t : ι → ℝ≥0) (ht : ∀ j, 0 < t j) :
    (incrementLaw m hm t ht).map (fun x i => ∑ j ∈ Finset.univ.filter (fun j => p j=i), x j) =
      incrementLaw m hm (blockTimes p t) (blockTimes_pos p hp t ht) := by
  have he : linearImage (blockMatrix p) = fun (x : ι → ℝ) i =>
      ∑ j ∈ Finset.univ.filter (fun j => p j=i), x j := by
    funext x i
    exact block_apply p x i
  simpa only [configurationLaw,he] using block_law m hm p hp t ht

end OperatorDerivativeRewrite.Foundation.HigherHeatBlockCoarsening
