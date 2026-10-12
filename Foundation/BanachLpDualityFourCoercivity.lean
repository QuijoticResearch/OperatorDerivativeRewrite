import Foundation.BanachLpDualityFourExistence

/-!
# Quartic energy bounds without finite-dimensionality

These estimates concern the actual L4 norm and arbitrary continuous dual data.
They prepare the direct minimizing-sequence argument on a complete normed space.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace OperatorDerivativeRewrite.Foundation.BanachLpDualityFourCoercivity

open BanachLpDualityFour

variable {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [NormedSpace ℝ H]

private instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-- The zero sublevel of the affine quartic energy has an explicit norm bound. -/
theorem quarticPotential_sublevel_bound
    (δ : H →L[ℝ] Lp ℝ 4 μ) (c : ℝ) (hc : 0 < c)
    (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖) (f : StrongDual ℝ H)
    (u : H) (hu : (1 / 4 : ℝ) * ‖δ u‖ ^ 4 - f u ≤ 0) :
    ‖u‖ ≤ max 1 (4 * ‖f‖ / c ^ 4) := by
  have hk : 0 < c ^ 4 := pow_pos hc 4
  have hfu : f u ≤ ‖f‖ * ‖u‖ := (le_abs_self _).trans (f.le_opNorm u)
  have hδ4 : c ^ 4 * ‖u‖ ^ 4 ≤ ‖δ u‖ ^ 4 := by
    calc
      c ^ 4 * ‖u‖ ^ 4 = (c * ‖u‖) ^ 4 := by ring
      _ ≤ ‖δ u‖ ^ 4 := pow_le_pow_left₀ (by positivity) (hδ u) 4
  have hsub : c ^ 4 * ‖u‖ ^ 4 ≤ 4 * ‖f‖ * ‖u‖ := by nlinarith
  by_cases hr : ‖u‖ ≤ 1
  · exact hr.trans (le_max_left _ _)
  · have hr1 : 1 < ‖u‖ := lt_of_not_ge hr
    have hr0 : 0 < ‖u‖ := lt_trans zero_lt_one hr1
    apply le_trans _ (le_max_right _ _)
    apply (le_div_iff₀ hk).mpr
    apply (mul_le_mul_iff_right₀ hr0).mp
    have hp : ‖u‖ ^ 2 ≤ ‖u‖ ^ 4 := pow_le_pow_right₀ hr1.le (by decide : 2 ≤ 4)
    have hkp := mul_le_mul_of_nonneg_left hp hk.le
    nlinarith

/-- A global finite lower bound, proved before taking any infimum of the energy. -/
theorem quarticPotential_lower_bound
    (δ : H →L[ℝ] Lp ℝ 4 μ) (c : ℝ) (hc : 0 < c)
    (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖) (f : StrongDual ℝ H) (u : H) :
    -(‖f‖ * max 1 (4 * ‖f‖ / c ^ 4)) ≤ (1 / 4 : ℝ) * ‖δ u‖ ^ 4 - f u := by
  by_cases hu : (1 / 4 : ℝ) * ‖δ u‖ ^ 4 - f u ≤ 0
  · have hb := quarticPotential_sublevel_bound δ c hc hδ f u hu
    have hfu := (le_abs_self (f u)).trans (f.le_opNorm u)
    have hm := mul_le_mul_of_nonneg_left hb (norm_nonneg f)
    have hp := pow_nonneg (norm_nonneg (δ u)) 4
    nlinarith
  · have hR : 0 ≤ max 1 (4 * ‖f‖ / c ^ 4) := le_trans zero_le_one (le_max_left _ _)
    have hm := mul_nonneg (norm_nonneg f) hR
    linarith

theorem quarticPotential_bddBelow
    (δ : H →L[ℝ] Lp ℝ 4 μ) (c : ℝ) (hc : 0 < c)
    (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖) (f : StrongDual ℝ H) :
    BddBelow (Set.range (fun u : H => (1 / 4 : ℝ) * ‖δ u‖ ^ 4 - f u)) := by
  refine ⟨-(‖f‖ * max 1 (4 * ‖f‖ / c ^ 4)), ?_⟩
  rintro y ⟨u, rfl⟩
  exact quarticPotential_lower_bound δ c hc hδ f u

/-- The scalar quartic midpoint deficit, proved by a polynomial identity. -/
theorem scalar_quartic_midpoint (a b : ℝ) :
    ((a+b)/2)^4 + (a-b)^4/16 ≤ (a^4+b^4)/2 := by
  nlinarith [sq_nonneg (a^2-b^2)]

/-- Integrating the scalar deficit gives a genuine L4 midpoint estimate. -/
theorem quarticPotential_midpoint (δ : H →L[ℝ] Lp ℝ 4 μ) (u v : H) :
    (1/4:ℝ)*‖δ ((1/2:ℝ) • (u+v))‖^4 + (1/64:ℝ)*‖δ (u-v)‖^4 ≤
      ((1/4:ℝ)*‖δ u‖^4+(1/4:ℝ)*‖δ v‖^4)/2 := by
  let m := δ ((1/2:ℝ) • (u+v))
  let d := δ (u-v)
  have hm := quartic_integrable m
  have hd := quartic_integrable d
  have hu := quartic_integrable (δ u)
  have hv := quartic_integrable (δ v)
  have hmrepr : (fun ω => m ω) =ᵐ[μ] (fun ω => ((δ u) ω + (δ v) ω)/2) := by
    filter_upwards [Lp.coeFn_smul (1/2:ℝ) (δ u + δ v), Lp.coeFn_add (δ u) (δ v)]
      with ω hsm hadd
    dsimp [m]
    simp only [map_smul, map_add]
    rw [hsm]
    simp only [Pi.smul_apply, smul_eq_mul, hadd, Pi.add_apply]
    ring
  have hdrepr : (fun ω => d ω) =ᵐ[μ] (fun ω => (δ u) ω - (δ v) ω) := by
    filter_upwards [Lp.coeFn_sub (δ u) (δ v)] with ω hω
    simpa only [d, map_sub, Pi.sub_apply] using hω
  have hi : (∫ ω, (1/4:ℝ) * (m ω)^4 + (1/64:ℝ) * (d ω)^4 ∂μ) ≤
      ∫ ω, (1/8:ℝ) * ((δ u) ω)^4 + (1/8:ℝ) * ((δ v) ω)^4 ∂μ := by
    apply integral_mono_ae ((hm.const_mul _).add (hd.const_mul _))
      ((hu.const_mul _).add (hv.const_mul _))
    filter_upwards [hmrepr, hdrepr] with ω hmω hdω
    simp only [Pi.add_apply]
    rw [hmω, hdω]
    nlinarith [scalar_quartic_midpoint ((δ u) ω) ((δ v) ω)]
  simp only [integral_add (hm.const_mul _) (hd.const_mul _),
    integral_add (hu.const_mul _) (hv.const_mul _), integral_const_mul,
    quartic_integral_eq_norm] at hi
  dsimp [m, d] at hi
  nlinarith

/-- The actual lower bound on δ transfers the deficit to the source norm. -/
theorem quarticPotential_midpoint_lower (δ : H →L[ℝ] Lp ℝ 4 μ)
    (c : ℝ) (hc : 0 < c) (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖) (u v : H) :
    (1/4:ℝ)*‖δ ((1/2:ℝ) • (u+v))‖^4 + (c^4/64)*‖u-v‖^4 ≤
      ((1/4:ℝ)*‖δ u‖^4+(1/4:ℝ)*‖δ v‖^4)/2 := by
  have hp : c^4 * ‖u-v‖^4 ≤ ‖δ (u-v)‖^4 := by
    calc
      _ = (c*‖u-v‖)^4 := by ring
      _ ≤ _ := pow_le_pow_left₀ (mul_nonneg hc.le (norm_nonneg _)) (hδ (u-v)) 4
  have hm := quarticPotential_midpoint δ u v
  nlinarith

/-- A linear forcing term cancels exactly in the midpoint estimate. -/
theorem quarticEnergy_midpoint_lower (δ : H →L[ℝ] Lp ℝ 4 μ)
    (c : ℝ) (hc : 0 < c) (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖)
    (f : StrongDual ℝ H) (u v : H) :
    ((1/4:ℝ)*‖δ ((1/2:ℝ) • (u+v))‖^4 - f ((1/2:ℝ) • (u+v))) +
        (c^4/64)*‖u-v‖^4 ≤
      (((1/4:ℝ)*‖δ u‖^4-f u)+((1/4:ℝ)*‖δ v‖^4-f v))/2 := by
  have hm := quarticPotential_midpoint_lower δ c hc hδ u v
  have hf : f ((1/2:ℝ) • (u+v)) = (1/2:ℝ)*(f u+f v) := by
    simp only [map_smul, map_add, smul_eq_mul]
  rw [hf]
  nlinarith

end OperatorDerivativeRewrite.Foundation.BanachLpDualityFourCoercivity
