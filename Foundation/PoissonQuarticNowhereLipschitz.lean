import Foundation.PoissonQuarticAtomPerturbation

/-! The genuine complete quartic inverse on infinite Poisson L4 has no
local linear stability bound at any dual datum. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.PoissonQuarticNowhereLipschitz
open PoissonDifferenceCore BanachLpDualityFour BanachLpDualityFourInfinite
open BanachQuarticInverseObstruction PoissonQuarticAtomPerturbation
private instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

def step (n : ℕ) : ℝ := 1/((n : ℝ)+1)

theorem step_pos (n : ℕ) : 0<step n := by unfold step; positivity

theorem step_tendsto_zero : Tendsto step atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

def relativeBound (rate : ℝ≥0) (F : Lp ℝ 4 (poissonLaw rate)) (n : ℕ) : ℝ :=
  3*|localCoefficient rate F n|^2+3*step n*|localCoefficient rate F n|+(step n)^2

theorem relativeBound_nonneg (rate : ℝ≥0) (F : Lp ℝ 4 (poissonLaw rate)) (n : ℕ) :
    0≤relativeBound rate F n := by
  unfold relativeBound
  have hp := (step_pos n).le
  positivity

theorem relativeBound_tendsto_zero (rate : ℝ≥0) (F : Lp ℝ 4 (poissonLaw rate)) :
    Tendsto (relativeBound rate F) atTop (𝓝 0) := by
  have hx := localCoefficient_abs_tendsto_zero rate F
  have hs := step_tendsto_zero
  change Tendsto (fun n => 3*|localCoefficient rate F n|^2+
    3*step n*|localCoefficient rate F n|+(step n)^2) atTop (𝓝 0)
  simpa only [zero_pow (by decide : (2 : ℕ)≠0),mul_zero,zero_mul,add_zero] using
    (((hx.pow 2).const_mul 3).add (((hs.const_mul 3).mul hx))).add (hs.pow 2)

theorem no_local_linear_bound_at_source (rate : ℝ≥0) (hr : 0<rate)
    (F : Lp ℝ 4 (poissonLaw rate)) (K r : ℝ) (hR : 0<r) :
    ∃ f : StrongDual ℝ (Lp ℝ 4 (poissonLaw rate)),
      ‖f-normalFour (ContinuousLinearMap.id ℝ _) F‖<r ∧
      K*‖f-normalFour (ContinuousLinearMap.id ℝ _) F‖ <
        ‖(normalFourEquiv (ContinuousLinearMap.id ℝ _) 1 (by norm_num)
          (by intro w; simp)).symm f-
          (normalFourEquiv (ContinuousLinearMap.id ℝ _) 1 (by norm_num)
            (by intro w; simp)).symm (normalFour (ContinuousLinearMap.id ℝ _) F)‖ := by
  let C := max K 0
  have hC : 0≤C := le_max_right _ _
  have hKC : K≤C := le_max_left _ _
  have hg := relativeBound_tendsto_zero rate F
  have ht1 : Tendsto (fun n => step n*relativeBound rate F n) atTop (𝓝 0) := by
    simpa using step_tendsto_zero.mul hg
  have ht2 : Tendsto (fun n => C*relativeBound rate F n) atTop (𝓝 0) := by
    simpa using hg.const_mul C
  obtain ⟨n,hsmall,hlinear⟩ :=
    ((ht1.eventually (eventually_lt_nhds hR)).and
      (ht2.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)))).exists
  let U := F+step n • normalizedAtom rate n
  have hb := normal_shift_norm_bound rate hr F n (step n) (step_pos n).le
  change ‖normalFour (ContinuousLinearMap.id ℝ _) U-normalFour (ContinuousLinearMap.id ℝ _) F‖ ≤
    step n*relativeBound rate F n at hb
  refine ⟨normalFour (ContinuousLinearMap.id ℝ _) U, ?_, ?_⟩
  · exact hb.trans_lt hsmall
  · rw [inverse_normalFour,inverse_normalFour]
    have hu : ‖U-F‖=step n := by
      rw [show U-F=step n • normalizedAtom rate n by dsimp [U]; abel,
        norm_smul,Real.norm_eq_abs,abs_of_pos (step_pos n),normalizedAtom_norm rate hr,mul_one]
    rw [hu]
    have hm := mul_lt_mul_of_pos_right hlinear (step_pos n)
    have hc := mul_le_mul_of_nonneg_left hb hC
    have hk := mul_le_mul_of_nonneg_right hKC
      (norm_nonneg (normalFour (ContinuousLinearMap.id ℝ _) U-normalFour (ContinuousLinearMap.id ℝ _) F))
    nlinarith

theorem no_local_linear_bound_at_datum (rate : ℝ≥0) (hr : 0<rate)
    (f₀ : StrongDual ℝ (Lp ℝ 4 (poissonLaw rate))) (K r : ℝ) (hR : 0<r) :
    ∃ f : StrongDual ℝ (Lp ℝ 4 (poissonLaw rate)), ‖f-f₀‖<r ∧
      K*‖f-f₀‖ <
        ‖(normalFourEquiv (ContinuousLinearMap.id ℝ _) 1 (by norm_num)
          (by intro w; simp)).symm f-
          (normalFourEquiv (ContinuousLinearMap.id ℝ _) 1 (by norm_num)
            (by intro w; simp)).symm f₀‖ := by
  have he := no_local_linear_bound_at_source rate hr
    ((normalFourEquiv (ContinuousLinearMap.id ℝ _) 1 (by norm_num)
      (by intro w; simp)).symm f₀) K r hR
  simpa only [normalFour_inverse_solves] using he

end OperatorDerivativeRewrite.Foundation.PoissonQuarticNowhereLipschitz
