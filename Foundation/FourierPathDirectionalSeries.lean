import Foundation.FourierPathDirectionalCharacters

/-! Genuine two-sided directional derivatives of infinite Fourier path series. -/
noncomputable section
open Filter
open scoped lp NNReal ENNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.FourierPathDirectionalSeries
open L1SeriesSynthesis HigherHeatDyadicLaws HigherHeatContinuousCylinders
open HigherHeatFourierBanach HigherHeatFourierTranslations HigherHeatFourierTranslationContinuity
open FourierPathDirectionalCharacters

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

theorem coefficient_quotient_tendsto (h : Path) (a b : Coeff)
    (hab : ∀ i, b i=a i*eigenvalue (frequency levels ξ h i)) :
    Tendsto (fun t : ℝ => t⁻¹ • (diagonal levels ξ (scalePath t h) a-a))
      (𝓝[≠] 0) (𝓝 b) := by
  let q (t : ℝ) : Coeff := t⁻¹ • (diagonal levels ξ (scalePath t h) a-a)
  have he (t : ℝ) (i : ℕ) : q t i=a i*quotient (frequency levels ξ h i) t := by
    change (t⁻¹:ℝ) • (a i*characterTest levels ξ i (scalePath t h)-a i)=_
    rw [character_along]
    simp only [quotient, Complex.real_smul, Complex.ofReal_inv]
    ring
  have hi (i : ℕ) : Tendsto (fun t => q t i) (𝓝[≠] 0) (𝓝 (b i)) := by
    simpa only [he, ← hab i] using (tendsto_const_nhds (x := a i)).mul
      (quotient_tendsto (frequency levels ξ h i))
  have hn (i : ℕ) : Tendsto (fun t => ‖q t i-b i‖) (𝓝[≠] 0) (𝓝 (0:ℝ)) := by
    simpa only [sub_self, norm_zero] using (hi i).sub_const (b i) |>.norm
  have hq (t : ℝ) (i : ℕ) : ‖q t i‖ ≤ ‖b i‖ := by
    rw [he, hab i, norm_mul, norm_mul, eigenvalue_norm]
    exact mul_le_mul_of_nonneg_left (quotient_bound _ _) (norm_nonneg _)
  have hb (t : ℝ) (i : ℕ) : ‖‖q t i-b i‖‖ ≤ 2*‖b i‖ := by
    rw [Real.norm_eq_abs, abs_norm]
    calc
      _ ≤ ‖q t i‖+‖b i‖ := norm_sub_le _ _
      _ ≤ ‖b i‖+‖b i‖ := add_le_add (hq t i) le_rfl
      _ = _ := by ring
  have ht := tendsto_tsum_of_dominated_convergence ((coeff_summable b).mul_left (2:ℝ)) hn
    (Eventually.of_forall hb)
  have hs : Tendsto (fun t => ∑' i, ‖q t i-b i‖) (𝓝[≠] 0) (𝓝 (0:ℝ)) := by simpa using ht
  have hnq (t : ℝ) : ‖q t-b‖=∑' i, ‖q t i-b i‖ := by rw [← coeff_norm]; rfl
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact hs.congr' (Eventually.of_forall fun t => (hnq t).symm)

theorem along_hasDerivAt (h : Path) (a b : Coeff)
    (hab : ∀ i, b i=a i*eigenvalue (frequency levels ξ h i)) :
    HasDerivAt (fun t => along levels ξ h t ((kernel levels ξ).mkQ a))
      ((kernel levels ξ).mkQ b) 0 := by
  have ht := (kernel levels ξ).mkQL.continuous.tendsto b |>.comp
    (coefficient_quotient_tendsto levels ξ h a b hab)
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [zero_add, along_zero]
  change Tendsto (fun t : ℝ => t⁻¹ • ((kernel levels ξ).mkQ
    (diagonal levels ξ (scalePath t h) a)-(kernel levels ξ).mkQ a)) _ _
  simpa only [Function.comp_def, ContinuousLinearMap.map_smul_of_tower, map_sub,
    Submodule.mkQL_apply] using ht

theorem realized_hasDerivAt (h ω : Path) (a b : Coeff)
    (hab : ∀ i, b i=a i*eigenvalue (frequency levels ξ h i)) :
    HasDerivAt (fun t => realize levels ξ ((kernel levels ξ).mkQ a) (addPath (scalePath t h) ω))
      (realize levels ξ ((kernel levels ξ).mkQ b) ω) 0 := by
  let L := (((BoundedContinuousFunction.evalCLM ℂ ω).comp (realize levels ξ)).restrictScalars ℝ)
  have hd := L.hasFDerivAt.comp_hasDerivAt 0 (along_hasDerivAt levels ξ h a b hab)
  change HasDerivAt (fun t => realize levels ξ
    (along levels ξ h t ((kernel levels ξ).mkQ a)) ω)
    (realize levels ξ ((kernel levels ξ).mkQ b) ω) 0 at hd
  simpa only [along, realize_translation] using hd

end OperatorDerivativeRewrite.Foundation.FourierPathDirectionalSeries
