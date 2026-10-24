import Foundation.GaussianTerminalWeightedBracket

/-! Uniform L2 coefficient bounds ALONE do not give vanishing bracket means.
The past-plus-terminal observation domain is a substantive hypothesis. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianTerminalBracketObstruction
open InfiniteGaussian GaussianTimeDivergence GaussianTimeFieldNorm GaussianTimeSpaceHermite
open GaussianBrownianQuadraticVariation GaussianTerminalWeightedBracket
open GaussianTerminalBracketPrediction GaussianConditionalGraph

def coefficient (N : ℕ) (i : Fin (N+1)) : GaussianL2 :=
  (N+1:ℝ) • (wick (incrementDirection (uniformTime 1 N i.castSucc)
    (uniformTime 1 N i.succ)) 2 : GaussianL2)

private theorem cell_energy (N : ℕ) (i : Fin (N+1)) :
    ‖(wick (incrementDirection (uniformTime 1 N i.castSucc)
      (uniformTime 1 N i.succ)) 2 : GaussianL2)‖^2 = 2/(N+1:ℝ)^2 := by
  rw [wick_norm_sq,incrementDirection_norm_sq _ _
    (uniformTime_monotone 1 N (Fin.castSucc_le_succ i)),uniformTime_step]
  norm_num
  ring

theorem coefficient_norm_sq (N : ℕ) (i : Fin (N+1)) : ‖coefficient N i‖^2 = 2 := by
  rw [coefficient,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,cell_energy]
  have hn : (N+1:ℝ) ≠ 0 := by positivity
  field_simp

theorem coefficient_norm_bound (N : ℕ) (i : Fin (N+1)) : ‖coefficient N i‖ ≤ 2 := by
  have h := coefficient_norm_sq N i
  nlinarith [norm_nonneg (coefficient N i)]

theorem coefficient_actual (N : ℕ) (i : Fin (N+1)) :
    coefficient N i =ᵐ[gaussianProduct] fun Y => (N+1:ℝ)*
      ((GaussianTimeProcess.process (uniformTime 1 N i.succ) Y-
        GaussianTimeProcess.process (uniformTime 1 N i.castSucc) Y)^2-1/(N+1)) := by
  filter_upwards [Lp.coeFn_smul (N+1:ℝ)
    (wick (incrementDirection (uniformTime 1 N i.castSucc) (uniformTime 1 N i.succ)) 2 : GaussianL2),
      increment_wick_actual _ _ (uniformTime_monotone 1 N (Fin.castSucc_le_succ i))] with Y hs hi
  change coefficient N i Y = _ at hs
  rw [hs,Pi.smul_apply,hi,smul_eq_mul,uniformTime_step]
  norm_num

theorem mean_error_eq_two (N : ℕ) : meanError 1 N (coefficient N) = 2 := by
  unfold meanError coefficient
  simp only [inner_smul_right,real_inner_self_eq_norm_sq,cell_energy]
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  simp only [nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  have hn : (N+1:ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

theorem not_tendsto_zero : ¬Tendsto (fun N => meanError 1 N (coefficient N)) atTop (𝓝 0) := by
  intro h
  have he : Tendsto (fun N => meanError 1 N (coefficient N)) atTop (𝓝 2) :=
    tendsto_const_nhds.congr' (Eventually.of_forall fun N => (mean_error_eq_two N).symm)
  have hc := tendsto_nhds_unique h he
  norm_num at hc

theorem observation_domain_essential : ∃ (N : ℕ) (i : Fin (N+1)),
    coefficient N i ∉ generated (observation (uniformTime 1 N i.castSucc) 1) := by
  classical
  by_contra hn
  push_neg at hn
  exact not_tendsto_zero (meanError_tendsto 1 (by norm_num) coefficient hn 2 (by norm_num)
    coefficient_norm_bound)

end OperatorDerivativeRewrite.Foundation.GaussianTerminalBracketObstruction
