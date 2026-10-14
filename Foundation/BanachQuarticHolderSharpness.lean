import Foundation.BanachQuarticInverseObstruction

/-! Optimality of the one-third inverse Holder exponent at zero for the
actual complete-space quartic normal equation. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
set_option backward.isDefEq.respectTransparency false

namespace OperatorDerivativeRewrite.Foundation.BanachQuarticHolderSharpness
open BanachLpDualityFour BanachLpDualityFourInfinite BanachQuarticInverseObstruction
variable {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
private instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

theorem no_local_holder_bound (δ : H →L[ℝ] Lp ℝ 4 μ) (c : ℝ) (hc : 0 < c)
    (hδ : ∀ u : H, c*‖u‖ ≤ ‖δ u‖) (u : H) (hu : u ≠ 0)
    (q : ℝ) (hq : 1/3 < q) (K r : ℝ) (hr : 0 < r) :
    ∃ f : StrongDual ℝ H, ‖f‖ < r ∧
      K*‖f‖^q < ‖(normalFourEquiv δ c hc hδ).symm f -
        (normalFourEquiv δ c hc hδ).symm 0‖ := by
  have hup : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hepos : 0 < 3*q-1 := by linarith
  have ht1 : Tendsto (fun a : ℝ => a^3*‖normalFour δ u‖)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    have hcont : Continuous (fun a : ℝ => a^3*‖normalFour δ u‖) := by fun_prop
    simpa using (hcont.tendsto (0 : ℝ)).mono_left
      (show nhdsWithin 0 (Set.Ioi 0) ≤ 𝓝 (0 : ℝ) from inf_le_left)
  have ht2 : Tendsto (fun a : ℝ => K*a^(3*q-1)*‖normalFour δ u‖^q)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    have hcont : Continuous (fun a : ℝ => K*a^(3*q-1)*‖normalFour δ u‖^q) :=
      (continuous_const.mul (Real.continuous_rpow_const hepos.le)).mul continuous_const
    simpa only [Real.zero_rpow (ne_of_gt hepos), mul_zero, zero_mul] using
      (hcont.tendsto (0 : ℝ)).mono_left
        (show nhdsWithin 0 (Set.Ioi 0) ≤ 𝓝 (0 : ℝ) from inf_le_left)
  have hpos : ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < a := self_mem_nhdsWithin
  obtain ⟨a,ha,hsmall,hbound⟩ :=
    (hpos.and ((ht1.eventually (eventually_lt_nhds hr)).and
      (ht2.eventually (eventually_lt_nhds hup)))).exists
  have hp : a*a^(3*q-1) = a^(3*q) := by
    calc
      a*a^(3*q-1) = a^(1 : ℝ)*a^(3*q-1) := by rw [Real.rpow_one]
      _ = a^(1+(3*q-1)) := (Real.rpow_add ha _ _).symm
      _ = a^(3*q) := by congr 1; ring
  have he : a*(K*a^(3*q-1)*‖normalFour δ u‖^q) =
      K*(a^3*‖normalFour δ u‖)^q := by
    rw [Real.mul_rpow (pow_nonneg ha.le 3) (norm_nonneg _),
      ← Real.rpow_natCast_mul ha.le 3 q]
    calc
      _ = K*(a*a^(3*q-1))*‖normalFour δ u‖^q := by ring
      _ = _ := by rw [hp]; ring
  refine ⟨normalFour δ (a • u), ?_, ?_⟩
  · rw [normalFour_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos ha 3)]
    exact hsmall
  · rw [inverse_normalFour, inverse_zero, sub_zero, norm_smul, Real.norm_eq_abs,
      abs_of_pos ha, normalFour_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (pow_pos ha 3)]
    have hm := mul_lt_mul_of_pos_left hbound ha
    rw [he] at hm
    exact hm

end OperatorDerivativeRewrite.Foundation.BanachQuarticHolderSharpness
