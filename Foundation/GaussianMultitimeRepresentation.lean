import Foundation.GaussianOrderedTensorRepresentation
import Mathlib.Data.Finset.Sort

/-! Genuine representation of arbitrary finite Brownian observation polynomials.
Sorting is performed only on the finite observation set; repetitions and zero times are allowed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set MvPolynomial
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianMultitimeRepresentation
open InfiniteGaussian GaussianTimeProcess GaussianTimeDivergence GaussianTimeHilbert
open SeparableHilbertEmbedding GaussianPredictableFull GaussianTerminalRepresentation
open GaussianOrderedTensorRepresentation GaussianBrownianGeneratedSpace GaussianPredictableAdjoint
attribute [local instance] timeHilbert_secondCountable

theorem partition_direction_span {m : ℕ} (τ : Fin (m + 1) → ℝ≥0)
    (hτ : Monotone τ) (h0 : τ 0 = 0) (j : Fin (m + 1)) :
    hilbertEmbedding TimeHilbert (timeVector (τ j)) ∈ Submodule.span ℝ
      (Set.range (fun i : Fin m => incrementDirection (τ i.castSucc) (τ i.succ))) := by
  let S := Submodule.span ℝ
    (Set.range (fun i : Fin m => incrementDirection (τ i.castSucc) (τ i.succ)))
  change _ ∈ S
  induction j using Fin.induction with
  | zero => simp only [h0, timeVector_zero, map_zero]; exact S.zero_mem
  | succ i ih =>
    have he : hilbertEmbedding TimeHilbert (timeVector (τ i.succ)) =
        hilbertEmbedding TimeHilbert (timeVector (τ i.castSucc)) +
          incrementDirection (τ i.castSucc) (τ i.succ) := by
      rw [GaussianShiftedHermite.incrementDirection_sub _ _
        (hτ (by simpa only [Fin.le_def, Fin.val_castSucc, Fin.val_succ] using Nat.le_succ i.val))]
      module
    rw [he]
    exact S.add_mem ih (Submodule.subset_span ⟨i, rfl⟩)

theorem centered_observationPolynomial_mem_range {ι : Type*} [Fintype ι]
    (r : ι → ℝ≥0) (p : MvPolynomial ι ℝ) :
    centering (pastCoefficient r p : GaussianL2) ∈ itoIntegral.toLinearMap.range := by
  classical
  let S := Finset.univ.image r
  let v := S.orderEmbOfFin rfl
  let τ : Fin (S.card + 1) → ℝ≥0 := Fin.cons 0 v
  have hτ : Monotone τ := by
    intro i j hij
    cases i using Fin.cases with
    | zero => exact zero_le
    | succ i =>
      cases j using Fin.cases with
      | zero => simp only [Fin.le_def, Fin.val_succ, Fin.val_zero] at hij; omega
      | succ j => exact v.monotone (by simpa using hij)
  have h0 : τ 0 = 0 := rfl
  let k : Fin S.card → CoefficientSpace :=
    fun i => incrementDirection (τ i.castSucc) (τ i.succ)
  have hr (i : ι) : hilbertEmbedding TimeHilbert (timeVector (r i)) ∈
      Submodule.span ℝ (Set.range k) := by
    have hi : r i ∈ S := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have hir : r i ∈ Set.range v := by rwa [Finset.range_orderEmbOfFin]
    obtain ⟨j, hj⟩ := hir
    simpa only [k, τ, Fin.cons_succ, hj] using partition_direction_span τ hτ h0 j.succ
  choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hr i)
  have he : (fun i => ∑ j, c i j • k j) =
      (fun i => hilbertEmbedding TimeHilbert (timeVector (r i))) := funext hc
  change centering (isonormalCylinderL2 _ p) ∈ _
  rw [← he, isonormalCylinderL2_linear_substitution]
  apply centered_incrementPolynomial_mem_range
  · intro i
    exact hτ (by simpa only [Fin.le_def, Fin.val_castSucc, Fin.val_succ] using Nat.le_succ i.val)
  · intro i j hij
    exact hτ (Fin.succ_le_castSucc_iff.mpr hij)

theorem centered_brownianPolynomial_mem_range (p : MvPolynomial ℝ≥0 ℝ) :
    centering (brownianPolynomial p) ∈ itoIntegral.toLinearMap.range := by
  obtain ⟨s, q, rfl⟩ := exists_finset_rename p
  change centering (familyPolynomialEmbedding _ _) ∈ _
  rw [familyPolynomial_rename]
  exact centered_observationPolynomial_mem_range (fun t : s => t.val) q

def multitimePolynomialIntegrand {ι : Type*} [Fintype ι]
    (r : ι → ℝ≥0) (p : MvPolynomial ι ℝ) : fullPredictable :=
  predictableAdjoint (centering (pastCoefficient r p : GaussianL2))

theorem multitimePolynomial_representation {ι : Type*} [Fintype ι]
    (r : ι → ℝ≥0) (p : MvPolynomial ι ℝ) :
    itoIntegral (multitimePolynomialIntegrand r p) =
      (pastCoefficient r p : GaussianL2) -
        (∫ ω, (pastCoefficient r p : GaussianL2) ω ∂gaussianProduct) • gaussianOne := by
  obtain ⟨U, hU⟩ := centered_observationPolynomial_mem_range r p
  change itoIntegral U = _ at hU
  rw [← centering_apply]
  unfold multitimePolynomialIntegrand
  rw [← hU, predictableAdjoint_integral]

theorem multitimePolynomial_exists_unique {ι : Type*} [Fintype ι]
    (r : ι → ℝ≥0) (p : MvPolynomial ι ℝ) :
    ∃! U : fullPredictable, itoIntegral U = centering (pastCoefficient r p : GaussianL2) := by
  obtain ⟨U, hU⟩ := centered_observationPolynomial_mem_range r p
  refine ⟨U, hU, ?_⟩
  intro V hV
  exact itoIntegral.injective (hV.trans hU.symm)

end OperatorDerivativeRewrite.Foundation.GaussianMultitimeRepresentation
