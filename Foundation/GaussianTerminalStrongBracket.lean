import Foundation.GaussianTerminalBracketProducts

/-! Strong L2 bracket errors for bounded Borel current/terminal weights.
The cross-cell coefficients use the later generated observation domain. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianTerminalStrongBracket
open InfiniteGaussian GaussianTimeProcess GaussianTimeDivergence GaussianTimeSpaceHermite
open GaussianConditionalGraph GaussianTerminalBracketPrediction GaussianTerminalWeightedBracket
open GaussianTerminalBracketProducts GaussianBrownianQuadraticVariation

private theorem sum_energy {n : ℕ} (v : Fin n → GaussianL2) :
    ‖∑ i, v i‖^2 = ∑ i, ‖v i‖^2+
      2*∑ j, ∑ i, if i < j then inner ℝ (v i) (v j) else 0 := by
  have he (i j : Fin n) : inner ℝ (v i) (v j) =
      (if i=j then ‖v i‖^2 else 0)+(if i<j then inner ℝ (v i) (v j) else 0)+
        (if j < i then inner ℝ (v i) (v j) else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h,ne_of_lt h,not_lt_of_ge h.le]
    · subst j; simp [real_inner_self_eq_norm_sq]
    · simp [h,ne_of_gt h,not_lt_of_ge h.le]
  have hs : (∑ i : Fin n, ∑ j : Fin n, if j < i then inner ℝ (v i) (v j) else 0) =
      ∑ j : Fin n, ∑ i : Fin n, if i < j then inner ℝ (v i) (v j) else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp [real_inner_comm]
  have heSum : (∑ i : Fin n, ∑ j : Fin n, inner ℝ (v i) (v j)) =
      ∑ i : Fin n, ∑ j : Fin n,
        ((if i=j then ‖v i‖^2 else 0)+(if i<j then inner ℝ (v i) (v j) else 0)+
          (if j < i then inner ℝ (v i) (v j) else 0)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Finset.sum_congr rfl fun j _ => he i j
  rw [← real_inner_self_eq_norm_sq,sum_inner]
  simp_rw [inner_sum]
  rw [heSum]
  simp_rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
  rw [hs]
  rw [Finset.sum_comm (f:=fun i j : Fin n => if i<j then inner ℝ (v i) (v j) else 0)]
  ring

variable (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ) (hb : ∀ x, ‖φ x‖ ≤ 1)

def cell (T : ℝ≥0) (N : ℕ) (i : Fin (N+1)) : GaussianL2 :=
  term φ hφ hb (uniformTime T N i.castSucc) (uniformTime T N i.succ) T

def error (T : ℝ≥0) (N : ℕ) : GaussianL2 := ∑ i, cell φ hφ hb T N i

def row (T : ℝ≥0) (N : ℕ) (j : Fin (N+1)) : GaussianL2 :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin (N+1) => i<j), pairCoefficient φ φ hφ hφ hb hb
    (uniformTime T N i.castSucc) (uniformTime T N i.succ) (uniformTime T N j.castSucc) T

theorem row_generated (T : ℝ≥0) (N : ℕ) (j : Fin (N+1)) :
    row φ hφ hb T N j ∈ generated (observation (uniformTime T N j.castSucc) T) := by
  apply Submodule.sum_mem
  intro i hi
  exact pairCoefficient_generated φ φ hφ hφ hb hb _ _ _ _
    (uniformTime_monotone T N (Fin.castSucc_le_succ i))
    (uniformTime_monotone T N (Fin.succ_le_castSucc_iff.mpr (Finset.mem_filter.mp hi).2))

theorem row_norm_bound (T : ℝ≥0) (N : ℕ) (j : Fin (N+1)) : ‖row φ hφ hb T N j‖ ≤ 2*(T:ℝ) := by
  calc
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin (N+1) => i<j),
        ‖pairCoefficient φ φ hφ hφ hb hb (uniformTime T N i.castSucc)
          (uniformTime T N i.succ) (uniformTime T N j.castSucc) T‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin (N+1) => i<j), 2*(T:ℝ)/(N+1) := by
      apply Finset.sum_le_sum
      intro i hi
      have h := pairCoefficient_norm_bound φ φ hφ hφ hb hb
        (uniformTime T N i.castSucc) (uniformTime T N i.succ)
        (uniformTime T N j.castSucc) T
        (uniformTime_monotone T N (Fin.castSucc_le_succ i))
      simpa only [uniformTime_step,mul_div_assoc] using h
    _ ≤ ∑ i : Fin (N+1), 2*(T:ℝ)/(N+1) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
      field_simp

theorem error_energy (T : ℝ≥0) (N : ℕ) :
    ‖error φ hφ hb T N‖^2 = (∑ i, ‖cell φ hφ hb T N i‖^2)+
      2*meanError T N (row φ hφ hb T N) := by
  rw [error,sum_energy]
  congr 2
  unfold meanError row
  apply Finset.sum_congr rfl
  intro j hj
  rw [inner_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs
  · exact term_inner_pairCoefficient φ φ hφ hφ hb hb _ _ _ _ _
      (uniformTime_monotone T N (Fin.castSucc_le_succ i))
      (uniformTime_monotone T N (Fin.castSucc_le_succ j))
  · rfl

theorem error_norm_sq_bound (T : ℝ≥0) (hT : 0 < T) (N : ℕ) :
    ‖error φ hφ hb T N‖^2 ≤ 4*(T:ℝ)^2/(N+1)+16*(T:ℝ)^2/Real.sqrt (N+1) := by
  have hd : (∑ i, ‖cell φ hφ hb T N i‖^2) ≤ 4*(T:ℝ)^2/(N+1) := by
    calc
      _ ≤ ∑ i : Fin (N+1), (2*(T:ℝ)/(N+1))^2 := by
        apply Finset.sum_le_sum
        intro i hi
        have h := term_norm_bound φ hφ hb _ _ T
          (uniformTime_monotone T N (Fin.castSucc_le_succ i))
        rw [uniformTime_step] at h
        exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [cell,mul_div_assoc] using h) 2
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
        field_simp
        <;> ring
  have hc := meanError_bound T hT N (row φ hφ hb T N) (row_generated φ hφ hb T N)
    (2*(T:ℝ)) (by positivity) (row_norm_bound φ hφ hb T N)
  have hc' : |meanError T N (row φ hφ hb T N)| ≤ 8*(T:ℝ)^2/Real.sqrt (N+1) := by
    convert hc using 1 <;> ring
  rw [error_energy]
  calc
    _ ≤ (∑ i, ‖cell φ hφ hb T N i‖^2)+2*|meanError T N (row φ hφ hb T N)| := by
      linarith [le_abs_self (meanError T N (row φ hφ hb T N))]
    _ ≤ 4*(T:ℝ)^2/(N+1)+2*(8*(T:ℝ)^2/Real.sqrt (N+1)) :=
      add_le_add hd (mul_le_mul_of_nonneg_left hc' (by norm_num))
    _ = _ := by ring

theorem error_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (error φ hφ hb T) atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ => 4*(T:ℝ)^2/(N+1)+16*(T:ℝ)^2/Real.sqrt (N+1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => 4*(T:ℝ)^2/(N+1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have h2 : Tendsto (fun N : ℕ => 16*(T:ℝ)^2/Real.sqrt (N+1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
    simpa only [zero_add] using h1.add h2
  have hs := squeeze_zero (fun N => sq_nonneg ‖error φ hφ hb T N‖)
    (error_norm_sq_bound φ hφ hb T hT) hn
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero,sub_zero] using h

theorem error_actual (T : ℝ≥0) (N : ℕ) :
    error φ hφ hb T N =ᵐ[gaussianProduct] fun Y =>
      ∑ i : Fin (N+1),
        ((process (uniformTime T N i.succ) Y-process (uniformTime T N i.castSucc) Y)^2-
          ((uniformTime T N i.succ:ℝ)-uniformTime T N i.castSucc))*
            φ (process (uniformTime T N i.castSucc) Y,process T Y) := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (cell φ hφ hb T N),
    ae_all_iff.mpr (fun i : Fin (N+1) => term_actual φ hφ hb _ _ T
      (uniformTime_monotone T N (Fin.castSucc_le_succ i)))] with Y hs hi
  change (∑ i, cell φ hφ hb T N i : GaussianL2) Y = _
  rw [hs]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => hi i

theorem finite_sum_energy {n : ℕ} (v : Fin n → GaussianL2) :
    ‖∑ i, v i‖^2 = ∑ i, ‖v i‖^2+
      2*∑ j, ∑ i, if i < j then inner ℝ (v i) (v j) else 0 := sum_energy v

end OperatorDerivativeRewrite.Foundation.GaussianTerminalStrongBracket
