import Foundation.PoissonQuarticWeightedObstruction

/-! Exact normalized atom perturbations of the actual Poisson L4 normal map. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.PoissonQuarticAtomPerturbation
open PoissonDifferenceCore BanachLpDualityFour BanachLpDualityFourContinuity
open BanachQuarticDisjointObstruction PoissonQuarticWeightedObstruction
private instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
private instance : ENNReal.HolderConjugate (4/3 : ℝ≥0∞) 4 := by
  apply ENNReal.HolderConjugate.of_toReal
  norm_num [Real.holderConjugate_iff,ENNReal.toReal_div]
private instance : Fact ((1 : ℝ≥0∞) ≤ (4/3 : ℝ≥0∞)) :=
  ⟨ENNReal.HolderTriple.le (4/3 : ℝ≥0∞) 4 1⟩

def normalizedAtom (rate : ℝ≥0) (n : ℕ) : Lp ℝ 4 (poissonLaw rate) :=
  ‖poissonAtom rate n‖⁻¹ • poissonAtom rate n

theorem normalizedAtom_norm (rate : ℝ≥0) (hr : 0<rate) (n : ℕ) :
    ‖normalizedAtom rate n‖=1 := by
  rw [normalizedAtom,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (poissonAtom_ne_zero rate hr n))]

theorem normalized_normal_norm_le (rate : ℝ≥0) (hr : 0<rate) (n : ℕ) :
    ‖normalFour (ContinuousLinearMap.id ℝ _) (normalizedAtom rate n)‖ ≤ 1 := by
  have he := BanachLpAdjoint.boundedBanachDerivative_norm_le
    (ContinuousLinearMap.id ℝ (Lp ℝ 4 (poissonLaw rate))) (dualityFour (normalizedAtom rate n))
  rw [dualityFour_norm,normalizedAtom_norm rate hr,one_pow,one_mul] at he
  exact he.trans ContinuousLinearMap.norm_id_le

theorem normal_atom_shift (rate : ℝ≥0) (hr : 0<rate) (F : Lp ℝ 4 (poissonLaw rate))
    (n : ℕ) (a : ℝ) :
    normalFour (ContinuousLinearMap.id ℝ _) (F+a • normalizedAtom rate n)-
      normalFour (ContinuousLinearMap.id ℝ _) F=
      (((F n*‖poissonAtom rate n‖+a)^3-(F n*‖poissonAtom rate n‖)^3)) •
        normalFour (ContinuousLinearMap.id ℝ _) (normalizedAtom rate n) := by
  let r := ‖poissonAtom rate n‖
  have hr0 : r≠0 := norm_ne_zero_iff.mpr (poissonAtom_ne_zero rate hr n)
  have hd : dualityFour (F+a • normalizedAtom rate n)-dualityFour F=
      (((F n*r+a)^3-(F n*r)^3)) • dualityFour (normalizedAtom rate n) := by
    apply Lp.ext
    filter_upwards [dualityFour_ae (F+a • normalizedAtom rate n),dualityFour_ae F,
      dualityFour_ae (normalizedAtom rate n),Lp.coeFn_sub (dualityFour (F+a • normalizedAtom rate n)) (dualityFour F),
      Lp.coeFn_add F (a • normalizedAtom rate n),Lp.coeFn_smul a (normalizedAtom rate n),
      Lp.coeFn_smul (((F n*r+a)^3-(F n*r)^3)) (dualityFour (normalizedAtom rate n)),
      Lp.coeFn_smul r⁻¹ (poissonAtom rate n),
      indicatorConstLp_coeFn (μ := poissonLaw rate) (p := 4)
        (hs := measurableSet_singleton n) (hμs := by finiteness) (c := (1 : ℝ))]
      with k hf hu hn hs hadd has hcs hatom hat
    change normalizedAtom rate n k=r⁻¹*poissonAtom rate n k at hatom
    change poissonAtom rate n k=_ at hat
    simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hs hadd has hcs
    rw [hs,hf,hu,hcs,hn,hadd,has,hatom,hat]
    by_cases hk : k=n
    · subst k
      simp only [Set.indicator_of_mem (Set.mem_singleton n),mul_one]
      field_simp
    · simp [hk]
  simp only [normalFour,ContinuousLinearMap.id_apply]
  rw [← map_sub,hd,map_smul]

def localCoefficient (rate : ℝ≥0) (F : Lp ℝ 4 (poissonLaw rate)) (n : ℕ) : ℝ :=
  F n*‖poissonAtom rate n‖

theorem localCoefficient_fourth (rate : ℝ≥0) (F : Lp ℝ 4 (poissonLaw rate)) (n : ℕ) :
    (localCoefficient rate F n)^4=poissonWeight rate n*(F n)^4 := by
  rw [localCoefficient,mul_pow,atom_fourth]
  ring

theorem localCoefficient_abs_tendsto_zero (rate : ℝ≥0) (F : Lp ℝ 4 (poissonLaw rate)) :
    Tendsto (fun n => |localCoefficient rate F n|) atTop (𝓝 0) := by
  have ht := (quartic_weights_summable rate F).tendsto_atTop_zero
  have hc : Continuous (fun x : ℝ => x^(1/4 : ℝ)) := Real.continuous_rpow_const (by norm_num)
  have he (n : ℕ) : (poissonWeight rate n*(F n)^4)^(1/4 : ℝ)=|localCoefficient rate F n| := by
    rw [← localCoefficient_fourth]
    have hp : (localCoefficient rate F n)^4=|localCoefficient rate F n|^4 := by
      rw [← abs_pow,abs_of_nonneg (show 0 ≤ (localCoefficient rate F n)^4 by positivity)]
    rw [hp]
    simpa using Real.pow_rpow_inv_natCast (abs_nonneg (localCoefficient rate F n))
      (by norm_num : (4 : ℕ)≠0)
  simpa only [Function.comp_def,he,Real.zero_rpow (by norm_num : (1/4 : ℝ)≠0)] using
    (hc.tendsto (0 : ℝ)).comp ht

theorem cubic_shift_abs_le (x a : ℝ) (ha : 0≤a) :
    |(x+a)^3-x^3| ≤ a*(3*|x|^2+3*a*|x|+a^2) := by
  have h1 := abs_add_le (3*x^2+3*a*x) (a^2)
  have h2 := abs_add_le (3*x^2) (3*a*x)
  have he : (x+a)^3-x^3=a*(3*x^2+3*a*x+a^2) := by ring
  rw [he,abs_mul,abs_of_nonneg ha]
  have hb : |3*x^2+3*a*x+a^2| ≤ 3*|x|^2+3*a*|x|+a^2 := by
    simp only [abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ)≤3),
      abs_of_nonneg (sq_nonneg x),abs_of_nonneg (sq_nonneg a),abs_of_nonneg ha,sq_abs] at h1 h2 ⊢
    linarith
  exact mul_le_mul_of_nonneg_left hb ha

theorem normal_shift_norm_bound (rate : ℝ≥0) (hr : 0<rate)
    (F : Lp ℝ 4 (poissonLaw rate)) (n : ℕ) (a : ℝ) (ha : 0≤a) :
    ‖normalFour (ContinuousLinearMap.id ℝ _) (F+a • normalizedAtom rate n)-
      normalFour (ContinuousLinearMap.id ℝ _) F‖ ≤
      a*(3*|localCoefficient rate F n|^2+3*a*|localCoefficient rate F n|+a^2) := by
  rw [normal_atom_shift rate hr,norm_smul,Real.norm_eq_abs]
  exact (mul_le_of_le_one_right (abs_nonneg _) (normalized_normal_norm_le rate hr n)).trans
    (cubic_shift_abs_le (localCoefficient rate F n) a ha)

end OperatorDerivativeRewrite.Foundation.PoissonQuarticAtomPerturbation
