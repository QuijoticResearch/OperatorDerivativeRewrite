import Foundation.GaussianPotentialPredictionRank

/-! Uniform geometric extraction of first chaos by the actual inverse-number potential. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianPotentialIteration
open InfiniteGaussian GaussianNumberSectors GaussianInverseNumberPotential GaussianPotentialPredictionRank

theorem projection_potential (n : ℕ) (f : GaussianL2) :
    projection n (potentialOperator f)=(n : ℝ)⁻¹ • projection n f := by
  apply ext_inner_right ℝ
  intro g
  have hp := (sector n).inner_starProjection_left_eq_right f g
  change inner ℝ (projection n f) g=inner ℝ f (projection n g) at hp
  have hg : potentialOperator (projection n g)=(n : ℝ)⁻¹ • projection n g :=
    potential_sector n ⟨_,projection_mem n g⟩
  calc
    _=inner ℝ (potentialOperator f) (projection n g) :=
      (sector n).inner_starProjection_left_eq_right _ _
    _=inner ℝ f (potentialOperator (projection n g)) := potential_inner _ _
    _=(n : ℝ)⁻¹*inner ℝ f (projection n g) := by rw [hg,real_inner_smul_right]
    _=inner ℝ ((n : ℝ)⁻¹ • projection n f) g := by rw [real_inner_smul_left,hp]

theorem potential_firstProjection (f : GaussianL2) : potentialOperator (projection 1 f)=projection 1 f := by
  have he := potential_sector 1 ⟨_,projection_mem 1 f⟩
  simpa only [Nat.cast_one,inv_one,one_smul] using he

theorem potential_first_error_norm (f : GaussianL2) :
    ‖potentialOperator f-projection 1 f‖≤(1/2 : ℝ)*‖f‖ := by
  have hl (n : ℕ) : ‖projection n (potentialOperator f-projection 1 f)‖^2≤
      (1/4 : ℝ)*‖projection n f‖^2 := by
    rw [map_sub,projection_potential,projection_of_sector ⟨_,projection_mem 1 f⟩]
    by_cases hn0 : n=0
    · subst n
      norm_num
    · by_cases hn1 : n=1
      · subst n
        simp only [Nat.cast_one,inv_one,one_smul,ite_true,sub_self,norm_zero]
        nlinarith [sq_nonneg ‖projection 1 f‖]
      · rw [if_neg hn1,sub_zero,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
        have hn : (2 : ℝ)≤n := by exact_mod_cast (show 2≤n by omega)
        have hi : (n : ℝ)⁻¹≤1/2 := by
          simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<2) hn
        have h0 : 0≤(n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
        have hsq : ((n : ℝ)⁻¹)^2≤(1/4 : ℝ) := by nlinarith
        exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have he := hasSum_le hl (projection_hasSum_norm_sq (potentialOperator f-projection 1 f))
    ((projection_hasSum_norm_sq f).mul_left (1/4 : ℝ))
  nlinarith [norm_nonneg (potentialOperator f-projection 1 f),norm_nonneg f]

theorem iterate_firstProjection (k : ℕ) (f : GaussianL2) :
    projection 1 ((potentialOperator^k) f)=projection 1 f := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ']
    change projection 1 (potentialOperator ((potentialOperator^k) f))=_
    rw [projection_potential]
    simpa only [Nat.cast_one,inv_one,one_smul] using ih

theorem iterate_first_error (k : ℕ) (f : GaussianL2) :
    ‖(potentialOperator^k) f-projection 1 f‖≤(1/2 : ℝ)^k*‖f‖ := by
  induction k with
  | zero =>
    change ‖f-projection 1 f‖≤(1/2 : ℝ)^0*‖f‖
    rw [pow_zero,one_mul]
    change ‖f-(sector 1).starProjection f‖≤‖f‖
    simpa only [Submodule.starProjection_orthogonal_val] using
      (sector 1)ᗮ.norm_starProjection_apply_le f
  | succ k ih =>
    rw [pow_succ']
    change ‖potentialOperator ((potentialOperator^k) f)-projection 1 f‖≤_
    have hz : projection 1 ((potentialOperator^k) f-projection 1 f)=0 := by
      rw [map_sub,iterate_firstProjection,projection_idempotent,sub_self]
    have he := potential_first_error_norm ((potentialOperator^k) f-projection 1 f)
    rw [hz,sub_zero,map_sub,potential_firstProjection] at he
    calc
      _≤(1/2 : ℝ)*‖(potentialOperator^k) f-projection 1 f‖ := he
      _≤(1/2 : ℝ)*((1/2 : ℝ)^k*‖f‖) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _=(1/2 : ℝ)^(k+1)*‖f‖ := by rw [pow_succ]; ring

theorem iterate_opNorm_error (k : ℕ) : ‖potentialOperator^k-projection 1‖≤(1/2 : ℝ)^k := by
  apply ContinuousLinearMap.opNorm_le_bound (potentialOperator^k-projection 1) (by positivity)
  intro f
  exact iterate_first_error k f

theorem iterate_operator_tendsto : Tendsto (fun k : ℕ => potentialOperator^k) atTop (𝓝 (projection 1)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun k => norm_nonneg _) iterate_opNorm_error
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (1/2 : ℝ)<1))

end OperatorDerivativeRewrite.Foundation.GaussianPotentialIteration
