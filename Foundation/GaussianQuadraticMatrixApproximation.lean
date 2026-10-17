import Foundation.GaussianFiniteQuadraticL4
import Foundation.GaussianQuadraticRecoverySurjectivity
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.AtTopBot.Finset

/-! Actual rectangular finite matrix approximations to every completed second
chaos target. Their L2 norms are bounded by the target norm. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianQuadraticMatrixApproximation
open InfiniteGaussian GaussianNumberSectors GaussianSourceHodge GaussianDivergenceRecovery
open GaussianLinearFieldDivergenceCompletion GaussianLinearFieldMatrixCoordinates
open GaussianQuadraticSourceHodge GaussianQuadraticRecoverySurjectivity GaussianFiniteQuadraticL4

def boxSource (s : Finset ℕ) (v : linearGaussianFields) : GaussianVectorL2 :=
  linearField (fun i : s => unit i) (fun i j : s => coordinates v (i, j))

def boxCore (s : Finset ℕ) (v : linearGaussianFields) : polynomialCylindricalDomain :=
  matrixCore (fun i : s => unit i) (fun i j : s => coordinates v (i, j))

theorem boxSource_eq_sum (s : Finset ℕ) (v : linearGaussianFields) :
    boxSource s v = ∑ p ∈ s ×ˢ s, coordinates v p • matrixUnit p := by
  let F : ℕ → ℕ → GaussianVectorL2 := fun i j =>
    coordinates v (i,j) • scalarTensor (unit i) (firstChaosEmbedding (unit j))
  change (∑ i : s, ∑ j : s, F i.val j.val) = ∑ p ∈ s ×ˢ s, F p.1 p.2
  rw [Finset.sum_product]
  calc
    _ = ∑ i : s, ∑ j ∈ s, F i.val j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_coe_sort s (fun j => F i.val j)
    _ = _ := Finset.sum_coe_sort s (fun i => ∑ j ∈ s, F i j)

theorem boxSource_mem (s : Finset ℕ) (v : linearGaussianFields) : boxSource s v ∈ linearGaussianFields := by
  rw [boxSource_eq_sum]
  exact linearGaussianFields.sum_mem (fun p _ => linearGaussianFields.smul_mem _
    (linear_rank_mem _ _))

theorem boxSource_energy (s : Finset ℕ) (v : linearGaussianFields) :
    ‖boxSource s v‖^2 = ∑ p ∈ s ×ˢ s, (coordinates v p)^2 := by
  rw [boxSource_eq_sum, ← real_inner_self_eq_norm_sq,
    matrixUnits_orthonormal.inner_sum]
  simp only [starRingEnd_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem boxSource_energy_le (s : Finset ℕ) (v : linearGaussianFields) :
    ‖boxSource s v‖^2 ≤ ‖(v : GaussianVectorL2)‖^2 := by
  rw [boxSource_energy]
  have h := matrixUnits_orthonormal.sum_inner_products_le (s := s ×ˢ s) (v : GaussianVectorL2)
  simpa only [coordinates_apply, Real.norm_eq_abs, sq_abs] using h

set_option maxHeartbeats 800000 in
theorem boxSource_tendsto (v : linearGaussianFields) :
    Tendsto (fun N : ℕ => boxSource (Finset.range N) v) atTop (𝓝 (v : GaussianVectorL2)) := by
  have he : matrixSynthesis (coordinates v) = (v : GaussianVectorL2) :=
    congrArg (fun w : linearGaussianFields => (w : GaussianVectorL2)) (matrixUnitary.apply_symm_apply v)
  have hs := matrixUnits_orthonormal.orthogonalFamily.hasSum_linearIsometry (coordinates v)
  change HasSum (fun p => coordinates v p • matrixUnit p) (matrixSynthesis (coordinates v)) at hs
  rw [he] at hs
  have ht : Tendsto (fun N : ℕ => Finset.range N ×ˢ Finset.range N) atTop atTop :=
    by
      have h := tendsto_finsetProd_atTop.comp (tendsto_atTop_diagonal.comp tendsto_finset_range)
      simpa only [Function.comp_def] using h
  simpa only [boxSource_eq_sum, Function.comp_def] using hs.comp ht

theorem boxCore_eq_divergence (s : Finset ℕ) (v : linearGaussianFields) :
    (boxCore s v : GaussianL2) = completedDivergence (boxSource s v) := by
  rw [boxCore, matrixCore_eq_target]
  have h := linearField_divergence_graph (fun i : s => unit i)
    (fun i j : s => coordinates v (i,j))
  exact hilbertDivergence.mem_graph_snd_inj h (full_divergence_graph (boxSource_mem s v)) rfl

theorem boxCore_tendsto (f : GaussianL2) (hf : f ∈ sector 2) :
    Tendsto (fun N : ℕ => (boxCore (Finset.range N)
      ⟨recovery f, recovery_second_chaos_linear hf⟩ : GaussianL2)) atTop (𝓝 f) := by
  have ht := completedDivergence.continuous.continuousAt.tendsto.comp
    (boxSource_tendsto ⟨recovery f, recovery_second_chaos_linear hf⟩)
  rw [completed_divergence_recovery hf] at ht
  convert ht using 1
  funext N
  exact boxCore_eq_divergence _ _

theorem boxCore_norm_le (f : GaussianL2) (hf : f ∈ sector 2) (s : Finset ℕ) :
    ‖(boxCore s ⟨recovery f, recovery_second_chaos_linear hf⟩ : GaussianL2)‖ ≤ ‖f‖ := by
  let v : linearGaussianFields := ⟨recovery f, recovery_second_chaos_linear hf⟩
  have hb := boxSource_energy_le s v
  have hp := gradientRange.norm_starProjection_apply_le (boxSource s v)
  have he := completed_energy (boxSource_mem s v)
  have hr := second_recovery_energy hf
  change ‖boxSource s v‖^2 ≤ ‖recovery f‖^2 at hb
  change ‖gradientProjection (boxSource s v)‖ ≤ ‖boxSource s v‖ at hp
  rw [boxCore_eq_divergence]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖completedDivergence (boxSource s v)‖^2 ≤ ‖f‖^2
  rw [he]
  nlinarith [sq_nonneg ‖boxSource s v‖, norm_nonneg (gradientProjection (boxSource s v))]

theorem boxCore_fourth_upper_bound (f : GaussianL2) (hf : f ∈ sector 2) (s : Finset ℕ) :
    ‖(polynomialProduct
      (boxCore s ⟨recovery f, recovery_second_chaos_linear hf⟩)
      (boxCore s ⟨recovery f, recovery_second_chaos_linear hf⟩) : GaussianL2)‖^2 ≤
        15 * (‖f‖^2)^2 := by
  have hh : Orthonormal ℝ (fun i : s => unit i) := units_orthonormal.comp Subtype.val Subtype.val_injective
  have hb := finite_matrix_fourth_upper_bound (fun i : s => unit i) hh
    (fun i j : s => coordinates ⟨recovery f, recovery_second_chaos_linear hf⟩ (i,j))
  exact hb.trans (by gcongr; exact boxCore_norm_le f hf s)

end OperatorDerivativeRewrite.Foundation.GaussianQuadraticMatrixApproximation
