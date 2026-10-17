import Foundation.GaussianFiniteObservationRecovery
import Mathlib.Analysis.PSeries

/-! Even compact one-source Gaussian recovery has infinite orthonormal image
energy. Compactness does not imply a Hilbert--Schmidt summability estimate. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianObservedRecoveryHarmonicEnergy
open InfiniteGaussian GaussianNumberSectors GaussianConditionalGraph GaussianConditionalCompactness
open GaussianWickConditionalProjection GaussianDivergenceRecovery GaussianInverseNumberPotential

theorem recovery_sector_energy {n : ℕ} (f : sector n) :
    ‖recovery f‖^2 = (n : ℝ)⁻¹ * ‖f‖^2 := by
  have he := recoveryOperator.adjoint_inner_left f.val (recovery f)
  change inner ℝ (potentialOperator f) f.val = inner ℝ (recovery f) (recovery f) at he
  rw [GaussianPotentialPredictionRank.potential_sector n f, real_inner_smul_left,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at he
  exact he.symm

theorem observed_normalized_energy {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) (hu : ‖u‖^2 = 1) (hm : u ∈ sourceSpan h) (n : ℕ) :
    ‖recovery (conditionalProjection h (normalizedWick u (n+1)))‖^2 = (n+1 : ℝ)⁻¹ := by
  have hf : normalizedWick u (n+1) ∈ sector (n+1) :=
    (sector (n+1)).smul_mem _ (IBMCubicFirstChaos.wick_mem_sector u (n+1))
  have hc : conditionalProjection h (normalizedWick u (n+1)) = normalizedWick u (n+1) := by
    apply (generated h).starProjection_eq_self_iff.mpr
    exact (generated h).smul_mem _ (wick_mem_generated_of_sourceSpan h u hm (n+1))
  rw [hc, recovery_sector_energy ⟨_, hf⟩]
  change (↑(n+1) : ℝ)⁻¹ * ‖normalizedWick u (n+1)‖^2 = (n+1 : ℝ)⁻¹
  rw [(normalizedWick_orthonormal u hu).norm_eq_one (n+1)]
  simp

/-- A concrete orthonormal sequence witnesses divergent squared image norms. -/
theorem observed_energy_sum_tendsto {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) (hu : ‖u‖^2 = 1) (hm : u ∈ sourceSpan h) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      ‖recovery (conditionalProjection h (normalizedWick u (n+1)))‖^2) atTop atTop := by
  simp_rw [observed_normalized_energy h u hu hm]
  simpa only [one_div] using Real.tendsto_sum_range_one_div_nat_succ_atTop

theorem no_uniform_orthonormal_image_energy {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) (hu : ‖u‖^2 = 1) (hm : u ∈ sourceSpan h) (M : ℝ) :
    ∃ N : ℕ, M < ∑ n ∈ Finset.range N,
      ‖recovery (conditionalProjection h (normalizedWick u (n+1)))‖^2 :=
  ((observed_energy_sum_tendsto h u hu hm).eventually (eventually_gt_atTop M)).exists

theorem observed_energy_not_summable {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) (hu : ‖u‖^2 = 1) (hm : u ∈ sourceSpan h) :
    ¬ Summable (fun n : ℕ =>
      ‖recovery (conditionalProjection h (normalizedWick u (n+1)))‖^2) := by
  exact (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n => sq_nonneg _)).mpr
    (observed_energy_sum_tendsto h u hu hm)

/-- The actual one-observation compact operator exhibits the divergent energy. -/
theorem one_source_compact_divergent_energy (u : CoefficientSpace) (hu : ‖u‖^2 = 1) :
    IsCompactOperator (recoveryOperator.comp (conditionalProjection (fun _ : Unit => u))) ∧
      ¬ Summable (fun n : ℕ =>
        ‖recovery (conditionalProjection (fun _ : Unit => u) (normalizedWick u (n+1)))‖^2) := by
  refine ⟨GaussianFiniteObservationRecovery.finite_observations_recovery_compact _, ?_⟩
  apply observed_energy_not_summable _ u hu
  exact (Submodule.span ℝ (Set.range (fun _ : Unit => u))).le_topologicalClosure
    (Submodule.subset_span ⟨(), rfl⟩)

end OperatorDerivativeRewrite.Foundation.GaussianObservedRecoveryHarmonicEnergy
