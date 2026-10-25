import Foundation.GaussianTerminalStrongBracket

/-! Actual centered clock-bracket errors when the terminal observation lies
strictly beyond the grid horizon. Borel weights may vary with every cell. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianFutureTerminalBracket
open InfiniteGaussian GaussianTimeProcess GaussianTimeDivergence GaussianTimeSpaceHermite
open GaussianBrownianQuadraticVariation GaussianTerminalBracketProducts
open GaussianConditionalGraph GaussianTerminalBracketPrediction

variable (H R : ℝ≥0) (N : ℕ)
  (φ : Fin (N+1) → ℝ × ℝ → ℝ) (hφ : ∀ i, Measurable (φ i))
  (hb : ∀ i x, ‖φ i x‖ ≤ 1)

def cell (i : Fin (N+1)) : GaussianL2 :=
  term (φ i) (hφ i) (hb i) (uniformTime H N i.castSucc) (uniformTime H N i.succ) R

def error : GaussianL2 := ∑ i, cell H R N φ hφ hb i

def row (j : Fin (N+1)) : GaussianL2 :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin (N+1) => i < j),
    pairCoefficient (φ i) (φ j) (hφ i) (hφ j) (hb i) (hb j)
      (uniformTime H N i.castSucc) (uniformTime H N i.succ) (uniformTime H N j.castSucc) R

theorem row_generated (j : Fin (N+1)) :
    row H R N φ hφ hb j ∈ generated (observation (uniformTime H N j.castSucc) R) := by
  apply Submodule.sum_mem
  intro i hi
  exact pairCoefficient_generated _ _ _ _ _ _ _ _ _ _
    (uniformTime_monotone H N (Fin.castSucc_le_succ i))
    (uniformTime_monotone H N (Fin.succ_le_castSucc_iff.mpr (Finset.mem_filter.mp hi).2))

theorem row_norm_bound (j : Fin (N+1)) : ‖row H R N φ hφ hb j‖ ≤ 2*(H:ℝ) := by
  calc
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin (N+1) => i < j),
        ‖pairCoefficient (φ i) (φ j) (hφ i) (hφ j) (hb i) (hb j)
          (uniformTime H N i.castSucc) (uniformTime H N i.succ) (uniformTime H N j.castSucc) R‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin (N+1) => i < j), 2*(H:ℝ)/(N+1) := by
      apply Finset.sum_le_sum
      intro i hi
      have h := pairCoefficient_norm_bound (φ i) (φ j) (hφ i) (hφ j) (hb i) (hb j)
        (uniformTime H N i.castSucc) (uniformTime H N i.succ) (uniformTime H N j.castSucc) R
        (uniformTime_monotone H N (Fin.castSucc_le_succ i))
      simpa only [uniformTime_step,mul_div_assoc] using h
    _ ≤ ∑ i : Fin (N+1), 2*(H:ℝ)/(N+1) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
      field_simp

theorem energy_identity :
    ‖error H R N φ hφ hb‖^2 = (∑ i, ‖cell H R N φ hφ hb i‖^2)+
      2*∑ j : Fin (N+1), inner ℝ
        (wick (incrementDirection (uniformTime H N j.castSucc) (uniformTime H N j.succ)) 2 : GaussianL2)
        (row H R N φ hφ hb j) := by
  rw [error,GaussianTerminalStrongBracket.finite_sum_energy]
  congr 2
  unfold row
  apply Finset.sum_congr rfl
  intro j hj
  rw [inner_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs
  · exact term_inner_pairCoefficient _ _ _ _ _ _ _ _ _ _ _
      (uniformTime_monotone H N (Fin.castSucc_le_succ i))
      (uniformTime_monotone H N (Fin.castSucc_le_succ j))
  · rfl

private theorem node_le_horizon (i : Fin (N+2)) : uniformTime H N i ≤ H := by
  have h := uniformTime_monotone H N (Fin.le_last i)
  simpa only [(uniformTime_endpoints H N).2] using h

theorem row_pairing_bound (hHR : H < R) (j : Fin (N+1)) :
    |inner ℝ
      (wick (incrementDirection (uniformTime H N j.castSucc) (uniformTime H N j.succ)) 2 : GaussianL2)
      (row H R N φ hφ hb j)| ≤ 4*(H:ℝ)^3/((N+1)^2*((R:ℝ)-H)) := by
  have hl := node_le_horizon H N j.castSucc
  have hr := node_le_horizon H N j.succ
  have hp := generated_pairing_bound _ _ R
    (uniformTime_monotone H N (Fin.castSucc_le_succ j)) (hr.trans hHR.le) (hl.trans_lt hHR)
    (row H R N φ hφ hb j) (row_generated H R N φ hφ hb j)
  have hgap : 0 < (R:ℝ)-H := sub_pos.mpr hHR
  have hden : (R:ℝ)-H ≤ (R:ℝ)-uniformTime H N j.castSucc := by
    exact sub_le_sub_left (show (uniformTime H N j.castSucc:ℝ) ≤ H from hl) (R:ℝ)
  have hfactor : 2*((uniformTime H N j.succ:ℝ)-uniformTime H N j.castSucc)^2 /
      ((R:ℝ)-uniformTime H N j.castSucc) ≤ 2*((H:ℝ)/(N+1))^2/((R:ℝ)-H) := by
    rw [uniformTime_step]
    exact div_le_div_of_nonneg_left (by positivity) hgap hden
  calc
    _ ≤ (2*((uniformTime H N j.succ:ℝ)-uniformTime H N j.castSucc)^2 /
        ((R:ℝ)-uniformTime H N j.castSucc))*‖row H R N φ hφ hb j‖ := hp
    _ ≤ (2*((H:ℝ)/(N+1))^2/((R:ℝ)-H))*(2*(H:ℝ)) :=
      mul_le_mul hfactor (row_norm_bound H R N φ hφ hb j) (norm_nonneg _) (by positivity)
    _ = _ := by
      have hn : (N+1:ℝ) ≠ 0 := by positivity
      have hg : (R:ℝ)-H ≠ 0 := ne_of_gt hgap
      field_simp
      <;> ring

theorem error_norm_sq_bound (hHR : H < R) :
    ‖error H R N φ hφ hb‖^2 ≤ 4*(H:ℝ)^2/(N+1)+8*(H:ℝ)^3/((N+1)*((R:ℝ)-H)) := by
  have hd : (∑ i, ‖cell H R N φ hφ hb i‖^2) ≤ 4*(H:ℝ)^2/(N+1) := by
    calc
      _ ≤ ∑ i : Fin (N+1), (2*(H:ℝ)/(N+1))^2 := by
        apply Finset.sum_le_sum
        intro i hi
        have h := term_norm_bound (φ i) (hφ i) (hb i) _ _ R
          (uniformTime_monotone H N (Fin.castSucc_le_succ i))
        rw [uniformTime_step] at h
        exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [cell,mul_div_assoc] using h) 2
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
        field_simp
        <;> ring
  rw [energy_identity]
  have hc : (∑ j : Fin (N+1), inner ℝ
      (wick (incrementDirection (uniformTime H N j.castSucc) (uniformTime H N j.succ)) 2 : GaussianL2)
      (row H R N φ hφ hb j)) ≤ 4*(H:ℝ)^3/((N+1)*((R:ℝ)-H)) := by
    calc
      _ ≤ ∑ j : Fin (N+1), 4*(H:ℝ)^3/((N+1)^2*((R:ℝ)-H)) :=
        Finset.sum_le_sum fun j _ => (le_abs_self _).trans (row_pairing_bound H R N φ hφ hb hHR j)
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
        have hn : (N+1:ℝ) ≠ 0 := by positivity
        have hg : (R:ℝ)-H ≠ 0 := ne_of_gt (sub_pos.mpr hHR)
        field_simp
        <;> ring
  calc
    _ ≤ 4*(H:ℝ)^2/(N+1)+2*(4*(H:ℝ)^3/((N+1)*((R:ℝ)-H))) :=
      add_le_add hd (mul_le_mul_of_nonneg_left hc (by norm_num))
    _ = _ := by ring

theorem error_actual : error H R N φ hφ hb =ᵐ[gaussianProduct] fun Y =>
    ∑ i : Fin (N+1),
      ((process (uniformTime H N i.succ) Y-process (uniformTime H N i.castSucc) Y)^2-
        ((uniformTime H N i.succ:ℝ)-uniformTime H N i.castSucc))*
          φ i (process (uniformTime H N i.castSucc) Y,process R Y) := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (cell H R N φ hφ hb),
    ae_all_iff.mpr (fun i : Fin (N+1) => term_actual (φ i) (hφ i) (hb i) _ _ R
      (uniformTime_monotone H N (Fin.castSucc_le_succ i)))] with Y hs hi
  change (∑ i, cell H R N φ hφ hb i : GaussianL2) Y = _
  rw [hs]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => hi i

omit N φ hφ hb in
theorem varying_error_tendsto (hHR : H < R)
    (weights : (N : ℕ) → Fin (N+1) → ℝ × ℝ → ℝ)
    (hm : ∀ N i, Measurable (weights N i)) (hbound : ∀ N i x, ‖weights N i x‖ ≤ 1) :
    Tendsto (fun N => error H R N (weights N) (hm N) (hbound N)) atTop (𝓝 0) := by
  have hr : Tendsto (fun N : ℕ => 4*(H:ℝ)^2/(N+1)+8*(H:ℝ)^3/((N+1)*((R:ℝ)-H))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => 4*(H:ℝ)^2/(N+1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have h2 : Tendsto (fun N : ℕ => (8*(H:ℝ)^3/((R:ℝ)-H))/(N+1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have h := h1.add h2
    simp only [zero_add] at h
    convert h using 1
    ext N
    have hn : (N+1:ℝ) ≠ 0 := by positivity
    have hg : (R:ℝ)-H ≠ 0 := ne_of_gt (sub_pos.mpr hHR)
    field_simp
    <;> ring
  have hs := squeeze_zero (fun N => sq_nonneg ‖error H R N (weights N) (hm N) (hbound N)‖)
    (fun N => error_norm_sq_bound H R N (weights N) (hm N) (hbound N) hHR) hr
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero,sub_zero] using h

end OperatorDerivativeRewrite.Foundation.GaussianFutureTerminalBracket
