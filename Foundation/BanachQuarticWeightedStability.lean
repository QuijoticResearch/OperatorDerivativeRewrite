import Foundation.BanachLpDualityFourInfinite
import Foundation.BochnerL2Dominated

/-! Weighted source nondegeneracy restores Lipschitz inverse stability for
the actual quartic normal map at a specified datum. -/
noncomputable section
open MeasureTheory
open scoped ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.BanachQuarticWeightedStability
open BanachLpDualityFour BanachLpDualityFourContinuity
variable {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
private instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
private instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

def weightedSource (δ : H →L[ℝ] Lp ℝ 4 μ) (u : H) : H →L[ℝ] Lp ℝ 2 μ :=
  (squareProduct (δ u)).comp δ

theorem cubic_weighted_monotone (a b : ℝ) :
    (3/4 : ℝ)*a^2*(a-b)^2 ≤ (a^3-b^3)*(a-b) := by
  have hp := mul_nonneg (sq_nonneg (a-b)) (sq_nonneg (b+a/2))
  nlinarith only [hp]

theorem normalFour_weighted_monotone (δ : H →L[ℝ] Lp ℝ 4 μ) (u v : H) :
    (3/4 : ℝ)*‖weightedSource δ u (u-v)‖^2 ≤ (normalFour δ u-normalFour δ v) (u-v) := by
  let F := weightedSource δ u (u-v)
  let a : Ω → ℝ := fun ω => (dualityFour (δ u)) ω*(δ (u-v)) ω
  let b : Ω → ℝ := fun ω => (dualityFour (δ v)) ω*(δ (u-v)) ω
  have ha : Integrable a μ := BanachLpAdjoint.integrable_mul δ (dualityFour (δ u)) (u-v)
  have hb : Integrable b μ := BanachLpAdjoint.integrable_mul δ (dualityFour (δ v)) (u-v)
  have hF : Integrable (fun ω => ‖F ω‖^2) μ := by
    simpa only [real_inner_self_eq_norm_sq] using
      L2.integrable_inner (𝕜 := ℝ) F F
  have hpoint : (fun ω => (3/4 : ℝ)*‖F ω‖^2) ≤ᵐ[μ] (fun ω => a ω-b ω) := by
    filter_upwards [squareProduct_ae (δ u) (δ (u-v)),dualityFour_ae (δ u),
      dualityFour_ae (δ v),Lp.coeFn_sub (δ u) (δ v)] with ω hF hu hv hs
    have hd : (δ (u-v)) ω=(δ u) ω-(δ v) ω := by simpa only [map_sub,Pi.sub_apply] using hs
    change (3/4 : ℝ)*‖(squareProduct (δ u) (δ (u-v))) ω‖^2 ≤ a ω-b ω
    dsimp [a,b]
    rw [hF,hu,hv,hd]
    simp only [sq_abs,mul_pow]
    nlinarith only [cubic_weighted_monotone ((δ u) ω) ((δ v) ω)]
  calc
    _ = ∫ ω, (3/4 : ℝ)*‖F ω‖^2 ∂μ := by rw [integral_const_mul,← BochnerL2Dominated.norm_sq_integral]
    _ ≤ ∫ ω, a ω-b ω ∂μ := integral_mono_ae (hF.const_mul _) (ha.sub hb) hpoint
    _ = _ := by
      rw [integral_sub ha hb]
      simp only [sub_apply,normalFour,BanachLpAdjoint.boundedBanachDerivative_apply]
      rfl

theorem inverse_lipschitz_at_weighted_datum (δ : H →L[ℝ] Lp ℝ 4 μ)
    (u : H) (c : ℝ) (hc : 0<c)
    (hweighted : ∀ w : H, c*‖w‖ ≤ ‖weightedSource δ u w‖) (v : H) :
    ‖u-v‖ ≤ (4/(3*c^2))*‖normalFour δ u-normalFour δ v‖ := by
  have hm := normalFour_weighted_monotone δ u v
  have hl := (sq_le_sq₀ (mul_nonneg hc.le (norm_nonneg _)) (norm_nonneg _)).mpr (hweighted (u-v))
  have hu : (normalFour δ u-normalFour δ v) (u-v) ≤
      ‖normalFour δ u-normalFour δ v‖*‖u-v‖ :=
    (le_abs_self _).trans ((normalFour δ u-normalFour δ v).le_opNorm (u-v))
  by_cases hz : ‖u-v‖=0
  · rw [hz]; positivity
  have hn : 0<‖u-v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  have hb : (3/4 : ℝ)*c^2*‖u-v‖ ≤ ‖normalFour δ u-normalFour δ v‖ := by
    apply (mul_le_mul_iff_right₀ hn).mp
    nlinarith [hl]
  have he : (4/(3*c^2))*‖normalFour δ u-normalFour δ v‖=
      (4*‖normalFour δ u-normalFour δ v‖)/(3*c^2) := by ring
  rw [he]
  apply (le_div_iff₀ (by positivity : 0<3*c^2)).mpr
  nlinarith [hb]

theorem normalFour_inverse_weighted_bound [CompleteSpace H]
    (δ : H →L[ℝ] Lp ℝ 4 μ) (d : ℝ) (hd : 0<d)
    (hδ : ∀ w : H, d*‖w‖ ≤ ‖δ w‖) (f₀ : StrongDual ℝ H)
    (c : ℝ) (hc : 0<c)
    (hweighted : ∀ w : H, c*‖w‖ ≤
      ‖weightedSource δ ((BanachLpDualityFourInfinite.normalFourEquiv δ d hd hδ).symm f₀) w‖)
    (f : StrongDual ℝ H) :
    ‖(BanachLpDualityFourInfinite.normalFourEquiv δ d hd hδ).symm f₀-
      (BanachLpDualityFourInfinite.normalFourEquiv δ d hd hδ).symm f‖ ≤
      (4/(3*c^2))*‖f₀-f‖ := by
  have he := inverse_lipschitz_at_weighted_datum δ
    ((BanachLpDualityFourInfinite.normalFourEquiv δ d hd hδ).symm f₀) c hc hweighted
    ((BanachLpDualityFourInfinite.normalFourEquiv δ d hd hδ).symm f)
  simpa only [BanachLpDualityFourInfinite.normalFour_inverse_solves] using he

end OperatorDerivativeRewrite.Foundation.BanachQuarticWeightedStability

