import Foundation.GaussianTerminalBracketPrediction

/-! Vanishing actual mean bracket errors for coefficients measurable in the
ENTIRE past together with W_T. No predictability assumption is imposed. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianTerminalWeightedBracket
open InfiniteGaussian GaussianTerminalBracketPrediction GaussianConditionalGraph
open GaussianTimeProcess GaussianTimeDivergence GaussianTimeSpaceHermite
open GaussianBrownianQuadraticVariation IBMUniformClockGridEnergy

theorem reciprocal_sum_bound (n : ℕ) :
    (∑ i : Fin n, 1/((n-i.val:ℕ):ℝ)) ≤ 2*Real.sqrt n := by
  have he : (∑ i : Fin n, 1/((n-i.val:ℕ):ℝ)) =
      ∑ j ∈ Finset.range n, 1/(j+1:ℝ) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => 1/((n-i:ℕ):ℝ))]
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro j hj
    have hnat : n-(n-1-j)=j+1 := by have := Finset.mem_range.mp hj; omega
    rw [hnat]
    norm_cast
  rw [he]
  apply (Finset.sum_le_sum (fun i _ => ?_)).trans (inverse_sqrt_sum n)
  have hi : (1:ℝ) ≤ i+1 := by linarith [Nat.cast_nonneg (α:=ℝ) i]
  have hp : 0 < Real.sqrt (i+1:ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hs : Real.sqrt (i+1:ℝ) ≤ i+1 := by
    nlinarith [sq_nonneg (Real.sqrt (i+1:ℝ)-1),Real.sq_sqrt (by positivity : (0:ℝ) ≤ i+1)]
  exact one_div_le_one_div_of_le hp hs

private theorem left_lt_terminal (T : ℝ≥0) (hT : 0 < T) (N : ℕ) (i : Fin (N+1)) :
    uniformTime T N i.castSucc < T := by
  apply NNReal.coe_lt_coe.mp
  simp only [uniformTime,NNReal.coe_div,NNReal.coe_mul,NNReal.coe_natCast,
    Fin.val_castSucc,Nat.cast_add,Nat.cast_one,NNReal.coe_add,NNReal.coe_one]
  have hi : (i.val:ℝ) < N+1 := by exact_mod_cast i.isLt
  rw [div_lt_iff₀ (by positivity : (0:ℝ)<N+1)]
  exact mul_lt_mul_of_pos_left hi hT

private theorem right_le_terminal (T : ℝ≥0) (N : ℕ) (i : Fin (N+1)) :
    uniformTime T N i.succ ≤ T := by
  have h := uniformTime_monotone T N (Fin.le_last i.succ)
  simpa only [(uniformTime_endpoints T N).2] using h

private theorem cell_factor (T : ℝ≥0) (hT : 0 < T) (N : ℕ) (i : Fin (N+1)) :
    2*((uniformTime T N i.succ:ℝ)-uniformTime T N i.castSucc)^2 /
      ((T:ℝ)-uniformTime T N i.castSucc) =
      (2*(T:ℝ)/(N+1))*(1/((N+1-i.val:ℕ):ℝ)) := by
  rw [uniformTime_step]
  have hnn : (N+1:ℝ) ≠ 0 := by positivity
  have hd : ((T:ℝ)-uniformTime T N i.castSucc) =
      ((T:ℝ)/(N+1))*((N+1-i.val:ℕ):ℝ) := by
    simp only [uniformTime,NNReal.coe_div,NNReal.coe_mul,NNReal.coe_natCast,
      Fin.val_castSucc,Nat.cast_sub (Nat.le_of_lt i.isLt),Nat.cast_add,Nat.cast_one,
      NNReal.coe_add,NNReal.coe_one]
    field_simp
    <;> ring
  rw [hd]
  have ht : (T:ℝ) ≠ 0 := ne_of_gt hT
  have hr : ((N+1-i.val:ℕ):ℝ) ≠ 0 := by
    have hp : 0 < N+1-i.val := Nat.sub_pos_of_lt i.isLt
    exact_mod_cast ne_of_gt hp
  field_simp
  <;> ring

def meanError (T : ℝ≥0) (N : ℕ) (a : Fin (N+1) → GaussianL2) : ℝ :=
  ∑ i, inner ℝ (wick (incrementDirection (uniformTime T N i.castSucc)
    (uniformTime T N i.succ)) 2 : GaussianL2) (a i)

theorem meanError_actual (T : ℝ≥0) (N : ℕ) (a : Fin (N+1) → GaussianL2) :
    meanError T N a = ∫ Y, ∑ i : Fin (N+1),
      ((process (uniformTime T N i.succ) Y-process (uniformTime T N i.castSucc) Y)^2-
        ((uniformTime T N i.succ:ℝ)-uniformTime T N i.castSucc))*a i Y ∂gaussianProduct := by
  rw [integral_finset_sum _ (fun i _ => actual_error_integrable _ _
    (uniformTime_monotone T N (Fin.castSucc_le_succ i)) (a i))]
  exact Finset.sum_congr rfl fun i _ => (actual_error_pairing _ _
    (uniformTime_monotone T N (Fin.castSucc_le_succ i)) (a i)).symm

theorem meanError_bound (T : ℝ≥0) (hT : 0 < T) (N : ℕ) (a : Fin (N+1) → GaussianL2)
    (ha : ∀ i, a i ∈ generated (observation (uniformTime T N i.castSucc) T))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ i, ‖a i‖ ≤ M) :
    |meanError T N a| ≤ 4*M*(T:ℝ)/Real.sqrt (N+1) := by
  have hc (i : Fin (N+1)) :
      |inner ℝ (wick (incrementDirection (uniformTime T N i.castSucc)
        (uniformTime T N i.succ)) 2 : GaussianL2) (a i)| ≤
        (2*(T:ℝ)/(N+1))*M*(1/((N+1-i.val:ℕ):ℝ)) := by
    have hi := generated_pairing_bound _ _ T
      (uniformTime_monotone T N (Fin.castSucc_le_succ i)) (right_le_terminal T N i)
      (left_lt_terminal T hT N i) (a i) (ha i)
    rw [cell_factor T hT N i] at hi
    apply hi.trans
    calc
      _ ≤ ((2*(T:ℝ)/(N+1))*(1/((N+1-i.val:ℕ):ℝ)))*M :=
        mul_le_mul_of_nonneg_left (hb i) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ i, |inner ℝ (wick (incrementDirection (uniformTime T N i.castSucc)
        (uniformTime T N i.succ)) 2 : GaussianL2) (a i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (N+1), (2*(T:ℝ)/(N+1))*M*(1/((N+1-i.val:ℕ):ℝ)) :=
      Finset.sum_le_sum fun i _ => hc i
    _ = ((2*(T:ℝ)/(N+1))*M)*(∑ i : Fin (N+1), 1/((N+1-i.val:ℕ):ℝ)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ ((2*(T:ℝ)/(N+1))*M)*(2*Real.sqrt (N+1)) :=
      mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_add,Nat.cast_one] using reciprocal_sum_bound (N+1))
        (by positivity)
    _ = _ := by
      have hp : Real.sqrt (N+1:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
      have hs := Real.sq_sqrt (by positivity : (0:ℝ) ≤ N+1)
      field_simp
      nlinarith

theorem meanError_tendsto (T : ℝ≥0) (hT : 0 < T)
    (a : (N : ℕ) → Fin (N+1) → GaussianL2)
    (ha : ∀ N i, a N i ∈ generated (observation (uniformTime T N i.castSucc) T))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ N i, ‖a N i‖ ≤ M) :
    Tendsto (fun N => meanError T N (a N)) atTop (𝓝 0) := by
  have hs : Tendsto (fun N : ℕ => Real.sqrt (N+1:ℝ)) atTop atTop := by
    exact Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hr : Tendsto (fun N : ℕ => 4*M*(T:ℝ)/Real.sqrt (N+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hs
  have hn := squeeze_zero (fun _ => abs_nonneg _)
    (fun N => meanError_bound T hT N (a N) (ha N) M hM (hb N)) hr
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero,Real.norm_eq_abs] using hn

end OperatorDerivativeRewrite.Foundation.GaussianTerminalWeightedBracket
