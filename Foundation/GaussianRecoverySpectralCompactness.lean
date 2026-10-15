import Foundation.GaussianPotentialIteration
import Foundation.PoissonRecoveryCompactness

/-! Exact positive-chaos compactness criterion for full actual Gaussian recovery compositions. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianRecoverySpectralCompactness
open InfiniteGaussian GaussianNumberSectors GaussianDivergenceRecovery GaussianInverseNumberPotential GaussianPotentialIteration

def partialRecovery (N : ℕ) : GaussianL2 →L[ℝ] GaussianVectorL2 := recoveryOperator.comp (truncation N)

theorem projection_truncation (n N : ℕ) (f : GaussianL2) :
    projection n (truncation N f)=if n≤N then projection n f else 0 := by
  have he (m : ℕ) : projection n (projection m f)=if m=n then projection n f else 0 := by
    by_cases hm : m=n
    · subst m
      rw [if_pos rfl,projection_idempotent]
    · simpa only [hm,Ne.symm hm,ite_false] using projection_of_sector (n := n) ⟨_,projection_mem m f⟩
  simp only [truncation,ContinuousLinearMap.sum_apply,map_sum,he]
  simp [Finset.sum_ite_eq,Finset.mem_range,Nat.lt_succ_iff]

theorem projection_residual (n N : ℕ) (f : GaussianL2) :
    projection n (f-truncation N f)=if n≤N then 0 else projection n f := by
  rw [map_sub,projection_truncation]
  split_ifs <;> simp

theorem recovery_tail_energy (N : ℕ) (f : GaussianL2) :
    ‖recovery (f-truncation N f)‖^2≤(N+1 : ℝ)⁻¹*‖f‖^2 := by
  have hb (n : ℕ) : (n : ℝ)⁻¹*‖projection n (f-truncation N f)‖^2≤
      (N+1 : ℝ)⁻¹*‖projection n f‖^2 := by
    rw [projection_residual]
    by_cases hn : n≤N
    · simp only [if_pos hn,norm_zero,zero_pow (by norm_num : (2 : ℕ)≠0),mul_zero]
      positivity
    · rw [if_neg hn]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply inv_anti₀ (by positivity)
      exact_mod_cast (show N+1≤n by omega)
  exact hasSum_le hb (recovery_inverse_energy_hasSum _) ((projection_hasSum_norm_sq f).mul_left _)

theorem recovery_tail_operator_bound (N : ℕ) :
    ‖recoveryOperator-partialRecovery N‖≤Real.sqrt ((N+1 : ℝ)⁻¹) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro f
  change ‖recoveryOperator f-recoveryOperator (truncation N f)‖≤_
  rw [← recoveryOperator.map_sub]
  change ‖recovery (f-truncation N f)‖≤Real.sqrt ((N+1 : ℝ)⁻¹)*‖f‖
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt (by positivity)]
  exact recovery_tail_energy N f

theorem partialRecovery_tendsto : Tendsto partialRecovery atTop (𝓝 recoveryOperator) := by
  have hn : Tendsto (fun N : ℕ => (N+1 : ℝ)) atTop atTop := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hs : Tendsto (fun N : ℕ => Real.sqrt ((N+1 : ℝ)⁻¹)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp (tendsto_inv_atTop_zero.comp hn)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun N => norm_nonneg _) (fun N => by rw [norm_sub_rev]; exact recovery_tail_operator_bound N) hs

def sectorExtract (n : ℕ) : GaussianVectorL2 →L[ℝ] GaussianL2 :=
  (n : ℝ) • (projection n).comp recoveryOperator.adjoint

theorem sectorExtract_recovery (n : ℕ) (hn : 0<n) (f : GaussianL2) : sectorExtract n (recovery f)=projection n f := by
  change (n : ℝ) • projection n (potentialOperator f)=_
  rw [projection_potential,smul_smul,mul_inv_cancel₀ (by exact_mod_cast hn.ne'),one_smul]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem partial_composition_compact (K : E →L[ℝ] GaussianL2)
    (hK : ∀ n,0<n → IsCompactOperator ((projection n).comp K)) (N : ℕ) :
    IsCompactOperator ((partialRecovery N).comp K) := by
  have hterm (n : ℕ) : IsCompactOperator (recoveryOperator.comp ((projection n).comp K)) := by
    by_cases hn : n=0
    · subst n
      have he : recoveryOperator.comp ((projection 0).comp K)=0 := by
        apply ContinuousLinearMap.ext
        intro f
        change recovery (projection 0 (K f))=0
        rw [projection_zero,recovery_smul,GaussianOneObservationRecoveryCompactness.recovery_vacuum_zero,smul_zero]
      rw [he]
      exact isCompactOperator_zero
    · exact (hK n (Nat.pos_of_ne_zero hn)).clm_comp recoveryOperator
  have he : (partialRecovery N).comp K=∑ n∈Finset.range (N+1),recoveryOperator.comp ((projection n).comp K) := by
    apply ContinuousLinearMap.ext
    intro f
    simp [partialRecovery,truncation,map_sum]
  rw [he]
  induction Finset.range (N+1) using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact isCompactOperator_zero
  | @insert n s hn ih =>
      rw [Finset.sum_insert hn]
      exact (hterm n).add ih

theorem recovery_composition_compact_iff (K : E →L[ℝ] GaussianL2) :
    IsCompactOperator (recoveryOperator.comp K) ↔ ∀ n,0<n → IsCompactOperator ((projection n).comp K) := by
  constructor
  · intro hK n hn
    have he : (sectorExtract n).comp (recoveryOperator.comp K)=(projection n).comp K := by
      apply ContinuousLinearMap.ext
      intro f
      exact sectorExtract_recovery n hn (K f)
    rw [← he]
    exact hK.clm_comp (sectorExtract n)
  · intro hK
    have hc : Continuous (fun T : GaussianL2 →L[ℝ] GaussianVectorL2 => T.comp K) := by fun_prop
    have ht : Tendsto (fun N => (partialRecovery N).comp K) atTop (𝓝 (recoveryOperator.comp K)) :=
      hc.continuousAt.tendsto.comp partialRecovery_tendsto
    exact isCompactOperator_of_tendsto ht (Eventually.of_forall (partial_composition_compact K hK))

end OperatorDerivativeRewrite.Foundation.GaussianRecoverySpectralCompactness

