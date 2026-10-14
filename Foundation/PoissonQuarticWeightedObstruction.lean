import Foundation.BanachQuarticWeightedStability
import Foundation.BanachQuarticDisjointObstruction

/-! No datum in the infinite Poisson L4 identity source satisfies the
quantitative weighted-source lower bound, even without zero coordinates. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.PoissonQuarticWeightedObstruction
open PoissonDifferenceCore BanachLpDualityFour BanachLpDualityFourContinuity
open BanachQuarticWeightedStability BanachQuarticDisjointObstruction
private instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
private instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

theorem weighted_atom (rate : ℝ≥0) (F : Lp ℝ 4 (poissonLaw rate)) (n : ℕ) :
    weightedSource (ContinuousLinearMap.id ℝ _) F (poissonAtom rate n)=
      indicatorConstLp 2 (measurableSet_singleton n) (by finiteness) (F n) := by
  apply Lp.ext
  filter_upwards [squareProduct_ae F (poissonAtom rate n),
    indicatorConstLp_coeFn (μ := poissonLaw rate) (p := 4)
      (hs := measurableSet_singleton n) (hμs := by finiteness) (c := (1 : ℝ)),
    indicatorConstLp_coeFn (μ := poissonLaw rate) (p := 2)
      (hs := measurableSet_singleton n) (hμs := by finiteness) (c := F n)] with k hp ha hb
  change (squareProduct F (poissonAtom rate n)) k=_
  change poissonAtom rate n k=_ at ha
  rw [hp,ha,hb]
  by_cases hk : k=n
  · subst k; simp
  · simp [hk]

theorem weighted_atom_fourth (rate : ℝ≥0) (F : Lp ℝ 4 (poissonLaw rate)) (n : ℕ) :
    ‖weightedSource (ContinuousLinearMap.id ℝ _) F (poissonAtom rate n)‖^4=
      (F n)^4*(poissonWeight rate n)^2 := by
  rw [weighted_atom,norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat,Real.norm_eq_abs,mul_pow]
  rw [← Real.rpow_mul_natCast (show 0 ≤ (poissonLaw rate).real {n} from ENNReal.toReal_nonneg)]
  norm_num
  rw [← abs_pow,abs_of_nonneg (show 0 ≤ (F n)^4 by positivity)]
  rfl

theorem atom_fourth (rate : ℝ≥0) (n : ℕ) : ‖poissonAtom rate n‖^4=poissonWeight rate n := by
  rw [poissonAtom,norm_indicatorConstLp (by norm_num) (by norm_num),norm_one,one_mul]
  simp only [ENNReal.toReal_ofNat]
  rw [← Real.rpow_mul_natCast (show 0 ≤ (poissonLaw rate).real {n} from ENNReal.toReal_nonneg)]
  norm_num
  rfl

theorem quartic_weights_summable (rate : ℝ≥0) (F : Lp ℝ 4 (poissonLaw rate)) :
    Summable (fun n => poissonWeight rate n*(F n)^4) := by
  have hi := quartic_integrable F
  change Integrable (fun n => (F n)^4) (ProbabilityTheory.poissonMeasure rate) at hi
  rw [ProbabilityTheory.integrable_poissonMeasure_iff] at hi
  simp only [Real.norm_eq_abs] at hi
  have hab (n : ℕ) : |(F n)^4|=(F n)^4 := abs_of_nonneg (by positivity)
  simp only [hab] at hi
  simpa only [poissonWeight,poissonLaw,ProbabilityTheory.poissonMeasure_real_singleton] using hi

theorem no_positive_weighted_lower (rate : ℝ≥0) (hr : 0<rate)
    (F : Lp ℝ 4 (poissonLaw rate)) (c : ℝ) (hc : 0<c) :
    ¬ (∀ w : Lp ℝ 4 (poissonLaw rate), c*‖w‖ ≤
      ‖weightedSource (ContinuousLinearMap.id ℝ _) F w‖) := by
  intro hweighted
  have hl (n : ℕ) : c^4 ≤ poissonWeight rate n*(F n)^4 := by
    have hh := pow_le_pow_left₀ (mul_nonneg hc.le (norm_nonneg _))
      (hweighted (poissonAtom rate n)) 4
    rw [mul_pow,atom_fourth,weighted_atom_fourth] at hh
    apply (mul_le_mul_iff_right₀ (poisson_weight_pos rate hr n)).mp
    nlinarith [hh]
  have ht := (quartic_weights_summable rate F).tendsto_atTop_zero
  have hz : c^4 ≤ (0 : ℝ) :=
    le_of_tendsto_of_tendsto tendsto_const_nhds ht (Eventually.of_forall hl)
  exact (not_le_of_gt (pow_pos hc 4)) hz

end OperatorDerivativeRewrite.Foundation.PoissonQuarticWeightedObstruction
