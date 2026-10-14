import Foundation.BanachQuarticWeightedStability
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Finite-dimensional source injectivity and an actual nonzero-a.e. datum
imply quantitative weighted coercivity and quartic inverse stability. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.BanachFiniteSourceStability
open BanachLpDualityFour BanachLpDualityFourContinuity BanachQuarticWeightedStability
variable {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
private instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
private instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

theorem weighted_source_injective (δ : H →L[ℝ] Lp ℝ 4 μ) (hδ : Function.Injective δ)
    (u : H) (hu : ∀ᵐ ω ∂μ, δ u ω≠0) : Function.Injective (weightedSource δ u) := by
  have hk (w : H) (hw : weightedSource δ u w=0) : w=0 := by
    have hz : δ w=0 := by
      apply Lp.ext
      filter_upwards [squareProduct_ae (δ u) (δ w),hu,Lp.coeFn_zero ℝ 2 μ,Lp.coeFn_zero ℝ 4 μ]
        with ω hp hne hzero hzero4
      change (weightedSource δ u w) ω=(δ u) ω*(δ w) ω at hp
      rw [hw,hzero] at hp
      have hv : δ w ω=0 := (mul_eq_zero.mp hp.symm).resolve_left hne
      simpa only [hzero4,Pi.zero_apply] using hv
    apply hδ
    simpa only [map_zero] using hz
  intro w z hwz
  have hs : weightedSource δ u (w-z)=0 := by rw [map_sub,hwz,sub_self]
  exact sub_eq_zero.mp (hk (w-z) hs)

theorem finite_linear_lower_bound [FiniteDimensional ℝ H] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (T : H →L[ℝ] E) (hT : Function.Injective T) :
    ∃ c : ℝ, 0<c ∧ ∀ w : H, c*‖w‖ ≤ ‖T w‖ := by
  obtain ⟨K,hK,hbound⟩ := T.toLinearMap.injective_iff_antilipschitz.mp hT
  have hp : (0 : ℝ)<K := hK
  refine ⟨(K : ℝ)⁻¹,inv_pos.mpr hp, ?_⟩
  intro w
  have hk := hbound.le_mul_dist w 0
  have he : ‖w‖ ≤ (K : ℝ)*‖T w‖ := by simpa [dist_eq_norm,map_zero] using hk
  have hh := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hp.le)
  simpa only [← mul_assoc,inv_mul_cancel₀ (ne_of_gt hp),one_mul] using hh

theorem finite_weighted_lower [FiniteDimensional ℝ H] (δ : H →L[ℝ] Lp ℝ 4 μ)
    (hδ : Function.Injective δ) (u : H) (hu : ∀ᵐ ω ∂μ, δ u ω≠0) :
    ∃ c : ℝ, 0<c ∧ ∀ w : H, c*‖w‖ ≤ ‖weightedSource δ u w‖ :=
  finite_linear_lower_bound (weightedSource δ u) (weighted_source_injective δ hδ u hu)

theorem finite_datum_inverse_stability [FiniteDimensional ℝ H] (δ : H →L[ℝ] Lp ℝ 4 μ)
    (hδ : Function.Injective δ) (u : H) (hu : ∀ᵐ ω ∂μ, δ u ω≠0) :
    ∃ K : ℝ, 0<K ∧ ∀ v : H, ‖u-v‖ ≤ K*‖normalFour δ u-normalFour δ v‖ := by
  obtain ⟨c,hc,hweighted⟩ := finite_weighted_lower δ hδ u hu
  refine ⟨4/(3*c^2),by positivity, ?_⟩
  exact inverse_lipschitz_at_weighted_datum δ u c hc hweighted

end OperatorDerivativeRewrite.Foundation.BanachFiniteSourceStability
