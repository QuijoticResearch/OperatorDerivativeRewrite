import Foundation.BanachFiniteSourceStability
import Foundation.PoissonQuarticNowhereLipschitz

/-! Fixed finite perturbation directions may be regular while the actual
ambient quartic inverse admits no uniform local linear stability. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.BanachFiniteDirectionStability
open BanachLpDualityFour BanachLpDualityFourContinuity BanachQuarticWeightedStability
open BanachFiniteSourceStability BanachLpDualityFourInfinite BanachQuarticInverseObstruction
open PoissonDifferenceCore
variable {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
private instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
private instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

theorem finite_direction_stability (δ : H →L[ℝ] Lp ℝ 4 μ) (hδ : Function.Injective δ)
    (u : H) (hu : ∀ᵐ ω ∂μ, δ u ω≠0) (E : Submodule ℝ H) [FiniteDimensional ℝ E] :
    ∃ K : ℝ, 0<K ∧ ∀ v : H, u-v∈E → ‖u-v‖ ≤ K*‖normalFour δ u-normalFour δ v‖ := by
  have hB := weighted_source_injective δ hδ u hu
  have hinj : Function.Injective ((weightedSource δ u).comp E.subtypeL) := by
    intro x y hxy
    apply Subtype.ext
    exact hB hxy
  obtain ⟨c,hc,hbound⟩ := finite_linear_lower_bound ((weightedSource δ u).comp E.subtypeL) hinj
  refine ⟨4/(3*c^2),by positivity, ?_⟩
  intro v hv
  have hl := hbound ⟨u-v,hv⟩
  change c*‖u-v‖ ≤ ‖weightedSource δ u (u-v)‖ at hl
  have hs := (sq_le_sq₀ (mul_nonneg hc.le (norm_nonneg _)) (norm_nonneg _)).mpr hl
  have hm := normalFour_weighted_monotone δ u v
  have hupper : (normalFour δ u-normalFour δ v) (u-v) ≤
      ‖normalFour δ u-normalFour δ v‖*‖u-v‖ :=
    (le_abs_self _).trans ((normalFour δ u-normalFour δ v).le_opNorm (u-v))
  by_cases hz : ‖u-v‖=0
  · rw [hz]; positivity
  have hn : 0<‖u-v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  have hb : (3/4 : ℝ)*c^2*‖u-v‖ ≤ ‖normalFour δ u-normalFour δ v‖ := by
    apply (mul_le_mul_iff_right₀ hn).mp
    nlinarith [hs]
  rw [show (4/(3*c^2))*‖normalFour δ u-normalFour δ v‖=
    (4*‖normalFour δ u-normalFour δ v‖)/(3*c^2) by ring]
  apply (le_div_iff₀ (by positivity : 0<3*c^2)).mpr
  nlinarith [hb]

def poissonConstant (rate : ℝ≥0) : Lp ℝ 4 (poissonLaw rate) := Lp.const 4 (poissonLaw rate) 1

theorem poisson_constant_finite_directions (rate : ℝ≥0)
    (E : Submodule ℝ (Lp ℝ 4 (poissonLaw rate))) [FiniteDimensional ℝ E] :
    ∃ K : ℝ, 0<K ∧ ∀ v : Lp ℝ 4 (poissonLaw rate), poissonConstant rate-v∈E →
      ‖poissonConstant rate-v‖ ≤ K*‖normalFour (ContinuousLinearMap.id ℝ _) (poissonConstant rate)-
        normalFour (ContinuousLinearMap.id ℝ _) v‖ := by
  apply finite_direction_stability (ContinuousLinearMap.id ℝ _) (fun x y h => h) (poissonConstant rate) _ E
  filter_upwards [Lp.coeFn_const (p := 4) (μ := poissonLaw rate) (1 : ℝ)] with n hn
  change poissonConstant rate n≠0
  rw [show poissonConstant rate n=(1 : ℝ) from hn]
  norm_num

theorem no_uniform_one_direction_bound (rate : ℝ≥0) (hr : 0<rate) (K : ℝ) :
    ¬ (∀ w v : Lp ℝ 4 (poissonLaw rate),
      poissonConstant rate-v∈Submodule.span ℝ ({w} : Set (Lp ℝ 4 (poissonLaw rate))) →
        ‖poissonConstant rate-v‖ ≤ K*‖normalFour (ContinuousLinearMap.id ℝ _) (poissonConstant rate)-
          normalFour (ContinuousLinearMap.id ℝ _) v‖) := by
  intro hbound
  obtain ⟨f,hsmall,hfail⟩ := PoissonQuarticNowhereLipschitz.no_local_linear_bound_at_source
    rate hr (poissonConstant rate) K 1 (by norm_num)
  let v := (normalFourEquiv (ContinuousLinearMap.id ℝ _) 1 (by norm_num) (by intro w; simp)).symm f
  have hs : normalFour (ContinuousLinearMap.id ℝ _) v=f := normalFour_inverse_solves _ _ _ _ f
  have hb := hbound (poissonConstant rate-v) v (Submodule.subset_span (Set.mem_singleton _))
  rw [hs,norm_sub_rev (normalFour (ContinuousLinearMap.id ℝ _) (poissonConstant rate)) f] at hb
  rw [inverse_normalFour] at hfail
  change K*‖f-normalFour (ContinuousLinearMap.id ℝ _) (poissonConstant rate)‖ < ‖v-poissonConstant rate‖ at hfail
  rw [norm_sub_rev (poissonConstant rate) v] at hb
  exact (not_le_of_gt hfail) hb

end OperatorDerivativeRewrite.Foundation.BanachFiniteDirectionStability
