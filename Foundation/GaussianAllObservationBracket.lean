import Foundation.GaussianInteriorClockBracket

/-! Strong actual clock-bracket errors for ONE arbitrary common observation
time. The observation and bounded Borel cell weights may vary by refinement. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianAllObservationBracket
open InfiniteGaussian GaussianTimeProcess GaussianTimeDivergence GaussianTimeSpaceHermite
open GaussianBrownianQuadraticVariation GaussianTerminalBracketProducts GaussianTerminalWeightedBracket
open GaussianTerminalBracketPrediction GaussianInteriorClockBracket GaussianFutureTerminalBracket

theorem prefix_reciprocal_bound (n m : ℕ) (hm : m ≤ n) :
    (∑ i : Fin n, if i.val < m then 1/((m-i.val:ℕ):ℝ) else 0) ≤ 2*Real.sqrt n := by
  have he : (∑ i : Fin n, if i.val < m then 1/((m-i.val:ℕ):ℝ) else 0) =
      ∑ i : Fin m, 1/((m-i.val:ℕ):ℝ) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < m then 1/((m-i:ℕ):ℝ) else 0) n,
      Fin.sum_univ_eq_sum_range (fun i : ℕ => 1/((m-i:ℕ):ℝ)) m]
    calc
      _ = ∑ i ∈ Finset.range m, if i < m then 1/((m-i:ℕ):ℝ) else 0 := by
        symm
        apply Finset.sum_subset (Finset.range_mono hm)
        intro i hi hn
        rw [if_neg (by simpa only [Finset.mem_range] using hn)]
      _ = _ := Finset.sum_congr rfl fun i hi => if_pos (Finset.mem_range.mp hi)
  rw [he]
  exact (reciprocal_sum_bound m).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast hm)) (by norm_num))

variable (H R : ℝ≥0) (N : ℕ) (φ : Fin (N+1) → ℝ × ℝ → ℝ)
  (hm : ∀ i, Measurable (φ i)) (hb : ∀ i x, ‖φ i x‖ ≤ 1)

def rowPairing (j : Fin (N+1)) : ℝ :=
  inner ℝ (wick (incrementDirection (uniformTime H N j.castSucc) (uniformTime H N j.succ)) 2 : GaussianL2)
    (row H R N φ hm hb j)

theorem rowPairing_bound (j : Fin (N+1)) : |rowPairing H R N φ hm hb j| ≤ 4*(H:ℝ)^2/(N+1) := by
  have h := norm_inner_le_norm (𝕜:=ℝ)
    (wick (incrementDirection (uniformTime H N j.castSucc) (uniformTime H N j.succ)) 2 : GaussianL2)
    (row H R N φ hm hb j)
  change ‖rowPairing H R N φ hm hb j‖ ≤ _ at h
  rw [Real.norm_eq_abs] at h
  have hw := wick_norm_bound _ _ (uniformTime_monotone H N (Fin.castSucc_le_succ j))
  rw [uniformTime_step] at hw
  calc
    _ ≤ ‖(wick (incrementDirection (uniformTime H N j.castSucc) (uniformTime H N j.succ)) 2 : GaussianL2)‖*
        ‖row H R N φ hm hb j‖ := h
    _ ≤ (2*((H:ℝ)/(N+1)))*(2*(H:ℝ)) :=
      mul_le_mul hw (row_norm_bound H R N φ hm hb j) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem early_rowPairing_bound (hH : 0 < H) (j : Fin (N+1)) (hj : j.val < cut H R N) :
    |rowPairing H R N φ hm hb j| ≤
      (4*(H:ℝ)^2/(N+1))*(1/((cut H R N-j.val:ℕ):ℝ)) := by
  have hd : 0 < (H:ℝ)/(N+1) := div_pos hH (by positivity)
  have hr : 0 < ((cut H R N-j.val:ℕ):ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hj
  have hg := early_gap H R hH N j hj
  have hp := generated_pairing_bound _ _ R
    (uniformTime_monotone H N (Fin.castSucc_le_succ j)) (early_right_le H R hH N j hj)
    (show uniformTime H N j.castSucc < R from
      (show (uniformTime H N j.castSucc:ℝ) < R from sub_pos.mp ((mul_pos hd hr).trans_le hg)))
    (row H R N φ hm hb j) (row_generated H R N φ hm hb j)
  have hf : 2*((uniformTime H N j.succ:ℝ)-uniformTime H N j.castSucc)^2 /
      ((R:ℝ)-uniformTime H N j.castSucc) ≤
      2*((H:ℝ)/(N+1))/((cut H R N-j.val:ℕ):ℝ) := by
    rw [uniformTime_step]
    calc
      _ ≤ 2*((H:ℝ)/(N+1))^2/(((H:ℝ)/(N+1))*((cut H R N-j.val:ℕ):ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos hd hr) hg
      _ = _ := by
        have hn : (N+1:ℝ) ≠ 0 := by positivity
        have hh : (H:ℝ) ≠ 0 := ne_of_gt hH
        have hrr : ((cut H R N-j.val:ℕ):ℝ) ≠ 0 := ne_of_gt hr
        field_simp
        <;> ring
  calc
    _ ≤ (2*((uniformTime H N j.succ:ℝ)-uniformTime H N j.castSucc)^2 /
        ((R:ℝ)-uniformTime H N j.castSucc))*‖row H R N φ hm hb j‖ := hp
    _ ≤ (2*((H:ℝ)/(N+1))/((cut H R N-j.val:ℕ):ℝ))*(2*(H:ℝ)) :=
      mul_le_mul hf (row_norm_bound H R N φ hm hb j) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem late_rowPairing_zero (hH : 0 < H) (j : Fin (N+1)) (hj : cut H R N < j.val) :
    rowPairing H R N φ hm hb j = 0 :=
  past_generated_pairing_zero _ _ R (uniformTime_monotone H N (Fin.castSucc_le_succ j))
    (late_left_ge H R hH N j hj) _ (row_generated H R N φ hm hb j)

theorem row_sum_bound (hH : 0 < H) :
    (∑ j, rowPairing H R N φ hm hb j) ≤
      (4*(H:ℝ)^2/(N+1))*(2*Real.sqrt (N+1))+4*(H:ℝ)^2/(N+1) := by
  have hp (j : Fin (N+1)) : rowPairing H R N φ hm hb j ≤
      (4*(H:ℝ)^2/(N+1))*(if j.val < cut H R N then 1/((cut H R N-j.val:ℕ):ℝ) else 0)+
        (4*(H:ℝ)^2/(N+1))*(if j.val=cut H R N then 1 else 0) := by
    rcases lt_trichotomy j.val (cut H R N) with hj | hj | hj
    · simp only [if_pos hj,if_neg (ne_of_lt hj),mul_zero,add_zero]
      exact (le_abs_self _).trans (early_rowPairing_bound H R N φ hm hb hH j hj)
    · simp only [hj,lt_self_iff_false,if_false,if_true,mul_zero,mul_one,zero_add]
      exact (le_abs_self _).trans (rowPairing_bound H R N φ hm hb j)
    · simp only [if_neg (not_lt_of_ge hj.le),if_neg (ne_of_gt hj),mul_zero,zero_add]
      exact le_of_eq (late_rowPairing_zero H R N φ hm hb hH j hj)
  have hcount : (∑ j : Fin (N+1), if j.val=cut H R N then (1:ℝ) else 0) ≤ 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j=cut H R N then (1:ℝ) else 0) (N+1)]
    simp only [Finset.sum_ite_eq',Finset.mem_range]
    split_ifs <;> norm_num
  calc
    _ ≤ ∑ j : Fin (N+1), ((4*(H:ℝ)^2/(N+1))*(if j.val < cut H R N then
        1/((cut H R N-j.val:ℕ):ℝ) else 0)+
        (4*(H:ℝ)^2/(N+1))*(if j.val=cut H R N then 1 else 0)) := Finset.sum_le_sum fun j _ => hp j
    _ = (4*(H:ℝ)^2/(N+1))*(∑ j : Fin (N+1), if j.val < cut H R N then
        1/((cut H R N-j.val:ℕ):ℝ) else 0)+
        (4*(H:ℝ)^2/(N+1))*(∑ j : Fin (N+1), if j.val=cut H R N then 1 else 0) := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    _ ≤ (4*(H:ℝ)^2/(N+1))*(2*Real.sqrt (N+1))+(4*(H:ℝ)^2/(N+1))*1 :=
      add_le_add (mul_le_mul_of_nonneg_left
        (by simpa only [Nat.cast_add,Nat.cast_one] using prefix_reciprocal_bound _ _ (cut_le H R N)) (by positivity))
        (mul_le_mul_of_nonneg_left hcount (by positivity))
    _ = _ := by ring

theorem error_norm_sq_bound (hH : 0 < H) :
    ‖error H R N φ hm hb‖^2 ≤ 12*(H:ℝ)^2/(N+1)+16*(H:ℝ)^2/Real.sqrt (N+1) := by
  have hd : (∑ i, ‖cell H R N φ hm hb i‖^2) ≤ 4*(H:ℝ)^2/(N+1) := by
    calc
      _ ≤ ∑ i : Fin (N+1), (2*(H:ℝ)/(N+1))^2 := by
        apply Finset.sum_le_sum
        intro i hi
        have h := term_norm_bound (φ i) (hm i) (hb i) _ _ R
          (uniformTime_monotone H N (Fin.castSucc_le_succ i))
        rw [uniformTime_step] at h
        exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [cell,mul_div_assoc] using h) 2
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
        field_simp
        <;> ring
  have hc := row_sum_bound H R N φ hm hb hH
  have hn : (N+1:ℝ) ≠ 0 := by positivity
  have hs : Real.sqrt (N+1:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have he : Real.sqrt (N+1:ℝ)/(N+1) = 1/Real.sqrt (N+1:ℝ) :=
    (div_eq_div_iff hn hs).mpr (by
      simpa only [one_mul,pow_two] using (Real.sq_sqrt (by positivity : (0:ℝ) ≤ N+1)))
  rw [energy_identity]
  change (∑ i, ‖cell H R N φ hm hb i‖^2)+2*(∑ j, rowPairing H R N φ hm hb j) ≤ _
  calc
    _ ≤ 4*(H:ℝ)^2/(N+1)+2*((4*(H:ℝ)^2/(N+1))*(2*Real.sqrt (N+1))+4*(H:ℝ)^2/(N+1)) :=
      add_le_add hd (mul_le_mul_of_nonneg_left hc (by norm_num))
    _ = 12*(H:ℝ)^2/(N+1)+16*(H:ℝ)^2*(Real.sqrt (N+1:ℝ)/(N+1)) := by ring
    _ = _ := by rw [he]; ring

omit R N φ hm hb in
theorem varying_error_tendsto (hH : 0 < H) (observations : ℕ → ℝ≥0)
    (weights : (N : ℕ) → Fin (N+1) → ℝ × ℝ → ℝ)
    (hm : ∀ N i, Measurable (weights N i)) (hb : ∀ N i x, ‖weights N i x‖ ≤ 1) :
    Tendsto (fun N => error H (observations N) N (weights N) (hm N) (hb N)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => 12*(H:ℝ)^2/(N+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have h2 : Tendsto (fun N : ℕ => 16*(H:ℝ)^2/Real.sqrt (N+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
  have hr := h1.add h2
  simp only [zero_add] at hr
  have he := squeeze_zero (fun N => sq_nonneg ‖error H (observations N) N (weights N) (hm N) (hb N)‖)
    (fun N => error_norm_sq_bound H (observations N) N (weights N) (hm N) (hb N) hH) hr
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp he
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero,sub_zero] using h

end OperatorDerivativeRewrite.Foundation.GaussianAllObservationBracket
