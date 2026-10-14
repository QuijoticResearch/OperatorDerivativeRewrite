import Foundation.BanachLpDualityFourInfinite

/-! The complete-space quartic inverse has an unavoidable singularity at
zero: no local linear modulus on a nontrivial source. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option backward.isDefEq.respectTransparency false

namespace OperatorDerivativeRewrite.Foundation.BanachQuarticInverseObstruction
open BanachLpDualityFour BanachLpDualityFourInfinite

variable {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
private instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

theorem dualityFour_smul (a : ℝ) (F : Lp ℝ 4 μ) :
    dualityFour (a • F) = (a^3) • dualityFour F := by
  apply Lp.ext
  filter_upwards [dualityFour_ae (a • F), Lp.coeFn_smul a F,
    dualityFour_ae F, Lp.coeFn_smul (a^3) (dualityFour F)] with ω h1 h2 h3 h4
  rw [h1, h4]
  simp only [Pi.smul_apply, smul_eq_mul, h2, h3]
  ring

theorem normalFour_smul (δ : H →L[ℝ] Lp ℝ 4 μ) (a : ℝ) (u : H) :
    normalFour δ (a • u) = (a^3) • normalFour δ u := by
  simp only [normalFour, map_smul, dualityFour_smul]

theorem normalFour_zero (δ : H →L[ℝ] Lp ℝ 4 μ) : normalFour δ 0 = 0 := by
  simpa only [zero_smul, zero_pow (by decide : (3 : ℕ) ≠ 0)] using normalFour_smul δ 0 (0 : H)

variable [CompleteSpace H]

theorem inverse_normalFour (δ : H →L[ℝ] Lp ℝ 4 μ) (c : ℝ) (hc : 0 < c)
    (hδ : ∀ u : H, c*‖u‖ ≤ ‖δ u‖) (u : H) :
    (normalFourEquiv δ c hc hδ).symm (normalFour δ u) = u :=
  (normalFourEquiv δ c hc hδ).symm_apply_apply u

theorem inverse_zero (δ : H →L[ℝ] Lp ℝ 4 μ) (c : ℝ) (hc : 0 < c)
    (hδ : ∀ u : H, c*‖u‖ ≤ ‖δ u‖) :
    (normalFourEquiv δ c hc hδ).symm 0 = 0 := by
  rw [← normalFour_zero δ]
  exact inverse_normalFour δ c hc hδ 0

/-- Every dual neighborhood of zero violates every proposed linear modulus,
provided the complete source contains a nonzero vector. -/
theorem no_local_linear_bound (δ : H →L[ℝ] Lp ℝ 4 μ) (c : ℝ) (hc : 0 < c)
    (hδ : ∀ u : H, c*‖u‖ ≤ ‖δ u‖) (u : H) (hu : u ≠ 0)
    (K r : ℝ) (hr : 0 < r) :
    ∃ f : StrongDual ℝ H, ‖f‖ < r ∧
      K*‖f‖ < ‖(normalFourEquiv δ c hc hδ).symm f -
        (normalFourEquiv δ c hc hδ).symm 0‖ := by
  have hup : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have ht1 : Tendsto (fun a : ℝ => a^3*‖normalFour δ u‖)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    have hcont : Continuous (fun a : ℝ => a^3*‖normalFour δ u‖) := by fun_prop
    simpa using (hcont.tendsto (0 : ℝ)).mono_left
      (show nhdsWithin 0 (Set.Ioi 0) ≤ 𝓝 (0 : ℝ) from inf_le_left)
  have ht2 : Tendsto (fun a : ℝ => K*a^2*‖normalFour δ u‖)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    have hcont : Continuous (fun a : ℝ => K*a^2*‖normalFour δ u‖) := by fun_prop
    simpa using (hcont.tendsto (0 : ℝ)).mono_left
      (show nhdsWithin 0 (Set.Ioi 0) ≤ 𝓝 (0 : ℝ) from inf_le_left)
  have hpos : ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < a := self_mem_nhdsWithin
  obtain ⟨a,ha,hsmall,hlinear⟩ :=
    (hpos.and ((ht1.eventually (eventually_lt_nhds hr)).and
      (ht2.eventually (eventually_lt_nhds hup)))).exists
  refine ⟨normalFour δ (a • u), ?_, ?_⟩
  · rw [normalFour_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos ha 3)]
    exact hsmall
  · rw [inverse_normalFour, inverse_zero, sub_zero, norm_smul, Real.norm_eq_abs,
      abs_of_pos ha, normalFour_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (pow_pos ha 3)]
    have hm := mul_lt_mul_of_pos_left hlinear ha
    nlinarith [hm]

theorem inverse_not_lipschitz (δ : H →L[ℝ] Lp ℝ 4 μ) (c : ℝ) (hc : 0 < c)
    (hδ : ∀ u : H, c*‖u‖ ≤ ‖δ u‖) (u : H) (hu : u ≠ 0) (K : ℝ≥0) :
    ¬ LipschitzWith K (normalFourEquiv δ c hc hδ).symm := by
  intro hl
  obtain ⟨f,_,hf⟩ := no_local_linear_bound δ c hc hδ u hu K 1 (by norm_num)
  have hb := hl.norm_sub_le f 0
  rw [sub_zero] at hb
  exact (not_lt_of_ge hb) hf

end OperatorDerivativeRewrite.Foundation.BanachQuarticInverseObstruction
