import Foundation.PoissonQuarticNowhereLipschitz

/-! The global one-third quartic inverse exponent is locally optimal at
every datum of the actual infinite Poisson L4 identity source. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.PoissonQuarticHolderEverywhere
open PoissonDifferenceCore BanachLpDualityFour BanachLpDualityFourInfinite
open BanachQuarticInverseObstruction PoissonQuarticAtomPerturbation PoissonQuarticNowhereLipschitz
private instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

def perturbationSize (rate : ℝ≥0) (F : Lp ℝ 4 (poissonLaw rate)) (n : ℕ) : ℝ :=
  |localCoefficient rate F n|+step n

theorem perturbationSize_pos (rate : ℝ≥0) (F : Lp ℝ 4 (poissonLaw rate)) (n : ℕ) :
    0<perturbationSize rate F n := add_pos_of_nonneg_of_pos (abs_nonneg _) (step_pos n)

theorem perturbationSize_tendsto_zero (rate : ℝ≥0) (F : Lp ℝ 4 (poissonLaw rate)) :
    Tendsto (perturbationSize rate F) atTop (𝓝 0) := by
  change Tendsto (fun n => |localCoefficient rate F n|+step n) atTop (𝓝 0)
  simpa only [add_zero] using
    (localCoefficient_abs_tendsto_zero rate F).add step_tendsto_zero

theorem normal_shift_cubic_bound (rate : ℝ≥0) (hr : 0<rate)
    (F : Lp ℝ 4 (poissonLaw rate)) (n : ℕ) :
    ‖normalFour (ContinuousLinearMap.id ℝ _)
      (F+perturbationSize rate F n • normalizedAtom rate n)-normalFour (ContinuousLinearMap.id ℝ _) F‖ ≤
      7*(perturbationSize rate F n)^3 := by
  let a := perturbationSize rate F n
  have ha : 0<a := perturbationSize_pos rate F n
  have hx : |localCoefficient rate F n|≤a := by dsimp [a,perturbationSize]; linarith [step_pos n]
  have hs := (sq_le_sq₀ (abs_nonneg _) ha.le).mpr hx
  have hm := mul_le_mul_of_nonneg_left hx (show 0≤3*a by positivity)
  have hb := normal_shift_norm_bound rate hr F n a ha.le
  have hg : 3*|localCoefficient rate F n|^2+3*a*|localCoefficient rate F n|+a^2 ≤ 7*a^2 := by
    nlinarith
  have hp := mul_le_mul_of_nonneg_left hg ha.le
  calc
    _ ≤ _ := hb
    _ ≤ a*(7*a^2) := hp
    _ = _ := by ring

theorem no_local_holder_at_source (rate : ℝ≥0) (hr : 0<rate)
    (F : Lp ℝ 4 (poissonLaw rate)) (q : ℝ) (hq : 1/3<q) (K r : ℝ) (hR : 0<r) :
    ∃ f : StrongDual ℝ (Lp ℝ 4 (poissonLaw rate)),
      ‖f-normalFour (ContinuousLinearMap.id ℝ _) F‖<r ∧
      K*‖f-normalFour (ContinuousLinearMap.id ℝ _) F‖^q <
        ‖(normalFourEquiv (ContinuousLinearMap.id ℝ _) 1 (by norm_num)
          (by intro w; simp)).symm f-
          (normalFourEquiv (ContinuousLinearMap.id ℝ _) 1 (by norm_num)
            (by intro w; simp)).symm (normalFour (ContinuousLinearMap.id ℝ _) F)‖ := by
  let C := max K 0
  have hC : 0≤C := le_max_right _ _
  have hKC : K≤C := le_max_left _ _
  have hq0 : 0≤q := by linarith
  have hexp : 0<3*q-1 := by linarith
  have ht := perturbationSize_tendsto_zero rate F
  have ht1 : Tendsto (fun n => 7*(perturbationSize rate F n)^3) atTop (𝓝 0) := by
    simpa using (ht.pow 3).const_mul 7
  have hcont : Continuous (fun x : ℝ => C*7^q*x^(3*q-1)) :=
    continuous_const.mul (Real.continuous_rpow_const hexp.le)
  have ht2 : Tendsto (fun n => C*7^q*(perturbationSize rate F n)^(3*q-1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.zero_rpow (ne_of_gt hexp),mul_zero] using
      (hcont.tendsto (0 : ℝ)).comp ht
  obtain ⟨n,hsmall,hlinear⟩ :=
    ((ht1.eventually (eventually_lt_nhds hR)).and
      (ht2.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)))).exists
  let a := perturbationSize rate F n
  have ha : 0<a := perturbationSize_pos rate F n
  let U := F+a • normalizedAtom rate n
  have hb := normal_shift_cubic_bound rate hr F n
  change ‖normalFour (ContinuousLinearMap.id ℝ _) U-normalFour (ContinuousLinearMap.id ℝ _) F‖≤7*a^3 at hb
  have hp := Real.rpow_le_rpow (norm_nonneg _) hb hq0
  have hm := mul_lt_mul_of_pos_right hlinear ha
  have he : (C*7^q*a^(3*q-1))*a=C*(7*a^3)^q := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ)≤7) (pow_nonneg ha.le 3),
      ← Real.rpow_natCast_mul ha.le 3 q]
    have hh : a^(3*q-1)*a=a^(3*q) := by
      calc
        _ = a^(3*q-1)*a^(1 : ℝ) := by rw [Real.rpow_one]
        _ = a^((3*q-1)+1) := (Real.rpow_add ha _ _).symm
        _ = _ := by congr 1; ring
    calc
      _ = C*7^q*(a^(3*q-1)*a) := by ring
      _ = _ := by rw [hh]; norm_num; ring
  simp only [one_mul] at hm
  change (C*7^q*a^(3*q-1))*a<a at hm
  rw [he] at hm
  refine ⟨normalFour (ContinuousLinearMap.id ℝ _) U,hb.trans_lt hsmall, ?_⟩
  rw [inverse_normalFour,inverse_normalFour]
  have hu : ‖U-F‖=a := by
    rw [show U-F=a • normalizedAtom rate n by dsimp [U]; abel,norm_smul,Real.norm_eq_abs,
      abs_of_pos ha,normalizedAtom_norm rate hr,mul_one]
  rw [hu]
  exact (mul_le_mul_of_nonneg_right hKC (Real.rpow_nonneg (norm_nonneg _) q)).trans_lt
    ((mul_le_mul_of_nonneg_left hp hC).trans_lt hm)

theorem no_local_holder_at_datum (rate : ℝ≥0) (hr : 0<rate)
    (f₀ : StrongDual ℝ (Lp ℝ 4 (poissonLaw rate))) (q : ℝ) (hq : 1/3<q) (K r : ℝ) (hR : 0<r) :
    ∃ f : StrongDual ℝ (Lp ℝ 4 (poissonLaw rate)), ‖f-f₀‖<r ∧
      K*‖f-f₀‖^q <
        ‖(normalFourEquiv (ContinuousLinearMap.id ℝ _) 1 (by norm_num)
          (by intro w; simp)).symm f-
          (normalFourEquiv (ContinuousLinearMap.id ℝ _) 1 (by norm_num)
            (by intro w; simp)).symm f₀‖ := by
  have he := no_local_holder_at_source rate hr
    ((normalFourEquiv (ContinuousLinearMap.id ℝ _) 1 (by norm_num)
      (by intro w; simp)).symm f₀) q hq K r hR
  simpa only [normalFour_inverse_solves] using he

end OperatorDerivativeRewrite.Foundation.PoissonQuarticHolderEverywhere
