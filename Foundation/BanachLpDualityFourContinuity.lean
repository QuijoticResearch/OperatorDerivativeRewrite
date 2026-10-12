import Foundation.BanachLpDualityFour
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Regularity and uniform monotonicity of the actual fourth-power duality map

The polynomial is realized using Mathlib's continuous Hölder multiplication
maps. No regularity or monotonicity property is imposed as an assumption.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace OperatorDerivativeRewrite.Foundation.BanachLpDualityFourContinuity

open BanachLpDualityFour

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

private instance : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := by
  apply ENNReal.HolderTriple.of_toReal
  norm_num [Real.holderTriple_iff]

private instance : ENNReal.HolderTriple (2 : ℝ≥0∞) 4 (4 / 3) := by
  apply ENNReal.HolderTriple.of_toReal
  norm_num [Real.holderTriple_iff, ENNReal.toReal_div]

private instance : ENNReal.HolderConjugate (4 / 3 : ℝ≥0∞) 4 := by
  apply ENNReal.HolderConjugate.of_toReal
  norm_num [Real.holderConjugate_iff, ENNReal.toReal_div]

private instance : Fact ((1 : ℝ≥0∞) ≤ (4 / 3 : ℝ≥0∞)) :=
  ⟨ENNReal.HolderTriple.le (4 / 3 : ℝ≥0∞) 4 1⟩

private instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
private instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-- Genuine multiplication `L⁴ × L⁴ → L²`. -/
def squareProduct : Lp ℝ 4 μ →L[ℝ] Lp ℝ 4 μ →L[ℝ] Lp ℝ 2 μ :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL μ 4 4 2

theorem squareProduct_ae (F G : Lp ℝ 4 μ) :
    squareProduct F G =ᵐ[μ] fun ω => F ω * G ω :=
  (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder F G

/-- Genuine multiplication `L² × L⁴ → L^(4/3)`. -/
def cubeProduct : Lp ℝ 2 μ →L[ℝ] Lp ℝ 4 μ →L[ℝ] Lp ℝ (4 / 3) μ :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL μ 2 4 (4 / 3)

theorem cubeProduct_ae (F : Lp ℝ 2 μ) (G : Lp ℝ 4 μ) :
    cubeProduct F G =ᵐ[μ] fun ω => F ω * G ω :=
  (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder F G

/-- The continuous polynomial realization equals the previously defined cube class. -/
theorem dualityFour_eq_cubeProduct (F : Lp ℝ 4 μ) :
    dualityFour F = cubeProduct (squareProduct F F) F := by
  apply Lp.ext
  filter_upwards [dualityFour_ae F, cubeProduct_ae (squareProduct F F) F,
    squareProduct_ae F F] with ω hc hp hs
  rw [hc, hp, hs]
  ring

/-- The actual cube map is smooth; in particular it is continuous and locally Lipschitz. -/
theorem contDiff_dualityFour : ContDiff ℝ ⊤ (dualityFour (μ := μ)) := by
  have hsq : ContDiff ℝ ⊤ (fun F : Lp ℝ 4 μ => squareProduct F F) :=
    squareProduct.contDiff.clm_apply contDiff_id
  have heq : dualityFour (μ := μ) = fun F => cubeProduct (squareProduct F F) F :=
    funext dualityFour_eq_cubeProduct
  rw [heq]
  exact (cubeProduct.contDiff.comp hsq).clm_apply contDiff_id

theorem continuous_dualityFour : Continuous (dualityFour (μ := μ)) :=
  contDiff_dualityFour.continuous

theorem locallyLipschitz_dualityFour : LocallyLipschitz (dualityFour (μ := μ)) :=
  (contDiff_dualityFour.of_le (by simp)).locallyLipschitz

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem contDiff_normalFour (δ : H →L[ℝ] Lp ℝ 4 μ) :
    ContDiff ℝ ⊤ (normalFour δ) :=
  (BanachLpAdjoint.boundedBanachDerivative δ).contDiff.comp
    (contDiff_dualityFour.comp δ.contDiff)

theorem continuous_normalFour (δ : H →L[ℝ] Lp ℝ 4 μ) :
    Continuous (normalFour δ) :=
  (contDiff_normalFour δ).continuous

theorem locallyLipschitz_normalFour (δ : H →L[ℝ] Lp ℝ 4 μ) :
    LocallyLipschitz (normalFour δ) :=
  ((contDiff_normalFour δ).of_le (by simp)).locallyLipschitz

/-- The sharp pointwise quartic monotonicity inequality. -/
theorem cubic_uniform_monotone (a b : ℝ) :
    (1 / 4 : ℝ) * (a - b) ^ 4 ≤ (a ^ 3 - b ^ 3) * (a - b) := by
  have hnonneg : 0 ≤ (3 / 4 : ℝ) * (a - b) ^ 2 * (a + b) ^ 2 := by
    positivity
  nlinarith only [hnonneg]



/-- Quantitative monotonicity holds in the actual image L⁴ norm. -/
theorem normalFour_uniform_monotone (δ : H →L[ℝ] Lp ℝ 4 μ) (u v : H) :
    (1 / 4 : ℝ) * ‖δ (u - v)‖ ^ 4 ≤
      (normalFour δ u - normalFour δ v) (u - v) := by
  let a : Ω → ℝ := fun ω => (dualityFour (δ u)) ω * (δ (u - v)) ω
  let b : Ω → ℝ := fun ω => (dualityFour (δ v)) ω * (δ (u - v)) ω
  have ha : Integrable a μ := BanachLpAdjoint.integrable_mul δ (dualityFour (δ u)) (u - v)
  have hb : Integrable b μ := BanachLpAdjoint.integrable_mul δ (dualityFour (δ v)) (u - v)
  have hpoint : (fun ω => (1 / 4 : ℝ) * ((δ (u - v)) ω) ^ 4) ≤ᵐ[μ]
      (fun ω => a ω - b ω) := by
    filter_upwards [dualityFour_ae (δ u), dualityFour_ae (δ v),
      Lp.coeFn_sub (δ u) (δ v)] with ω hu hv hsub
    dsimp [a, b]
    rw [hu, hv]
    have hδ : (δ (u - v)) ω = (δ u) ω - (δ v) ω := by
      simpa only [map_sub, Pi.sub_apply] using hsub
    rw [hδ]
    have h := cubic_uniform_monotone ((δ u) ω) ((δ v) ω)
    nlinarith only [h]
  calc
    (1 / 4 : ℝ) * ‖δ (u - v)‖ ^ 4 =
        ∫ ω, (1 / 4 : ℝ) * ((δ (u - v)) ω) ^ 4 ∂μ := by
      rw [integral_const_mul, quartic_integral_eq_norm]
    _ ≤ ∫ ω, a ω - b ω ∂μ :=
      integral_mono_ae ((quartic_integrable (δ (u - v))).const_mul _) (ha.sub hb) hpoint
    _ = (normalFour δ u - normalFour δ v) (u - v) := by
      rw [integral_sub ha hb]
      simp only [sub_apply, normalFour,
        BanachLpAdjoint.boundedBanachDerivative_apply]
      rfl

/-- A genuine lower bound on the original linear operator transfers the
quartic monotonicity estimate to its source norm. -/
theorem normalFour_uniform_monotone_lower
    (δ : H →L[ℝ] Lp ℝ 4 μ) (c : ℝ) (hc : 0 < c)
    (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖) (u v : H) :
    (c ^ 4 / 4) * ‖u - v‖ ^ 4 ≤
      (normalFour δ u - normalFour δ v) (u - v) := by
  calc
    (c ^ 4 / 4) * ‖u - v‖ ^ 4 = (1 / 4 : ℝ) * (c * ‖u - v‖) ^ 4 := by ring
    _ ≤ (1 / 4 : ℝ) * ‖δ (u - v)‖ ^ 4 := by
      gcongr
      exact hδ (u - v)
    _ ≤ (normalFour δ u - normalFour δ v) (u - v) :=
      normalFour_uniform_monotone δ u v

/-- Under the genuine lower bound, the normal map is injective. -/
theorem normalFour_injective
    (δ : H →L[ℝ] Lp ℝ 4 μ) (c : ℝ) (hc : 0 < c)
    (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖) :
    Function.Injective (normalFour δ) := by
  intro u v huv
  have h := normalFour_uniform_monotone_lower δ c hc hδ u v
  rw [huv, sub_self, zero_apply] at h
  have hzero : ‖u - v‖ ^ 4 = 0 := by
    nlinarith [pow_pos hc 4, pow_nonneg (norm_nonneg (u - v)) 4]
  have hn : ‖u - v‖ = 0 := (pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).mp hzero
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- Cubic inverse stability follows solely from uniform monotonicity. -/
theorem normalFour_inverse_cubic_bound
    (δ : H →L[ℝ] Lp ℝ 4 μ) (c : ℝ) (hc : 0 < c)
    (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖) (u v : H) :
    ‖u - v‖ ^ 3 ≤ (4 / c ^ 4) * ‖normalFour δ u - normalFour δ v‖ := by
  have hmon := normalFour_uniform_monotone_lower δ c hc hδ u v
  have hupper : (normalFour δ u - normalFour δ v) (u - v) ≤
      ‖normalFour δ u - normalFour δ v‖ * ‖u - v‖ :=
    (le_abs_self _).trans ((normalFour δ u - normalFour δ v).le_opNorm (u - v))
  by_cases hn : ‖u - v‖ = 0
  · rw [hn]
    simp only [zero_pow (by norm_num : (3 : ℕ) ≠ 0)]
    exact mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 4) (pow_nonneg hc.le 4))
      (norm_nonneg _)
  have hnpos : 0 < ‖u - v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
  have hdiv : c ^ 4 / 4 * ‖u - v‖ ^ 3 ≤ ‖normalFour δ u - normalFour δ v‖ := by
    apply (mul_le_mul_iff_left₀ hnpos).mp
    calc
      c ^ 4 / 4 * ‖u - v‖ ^ 3 * ‖u - v‖ = c ^ 4 / 4 * ‖u - v‖ ^ 4 := by ring
      _ ≤ ‖normalFour δ u - normalFour δ v‖ * ‖u - v‖ := hmon.trans hupper
  have hc4 : 0 < c ^ 4 := pow_pos hc 4
  apply (mul_le_mul_iff_right₀ hc4).mp
  calc
    c ^ 4 * ‖u - v‖ ^ 3 ≤ 4 * ‖normalFour δ u - normalFour δ v‖ := by linarith
    _ = c ^ 4 * ((4 / c ^ 4) * ‖normalFour δ u - normalFour δ v‖) := by
      field_simp

/-- The inverse relation is globally Hölder with exponent one third. -/
theorem normalFour_inverse_holder_bound
    (δ : H →L[ℝ] Lp ℝ 4 μ) (c : ℝ) (hc : 0 < c)
    (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖) (u v : H) :
    ‖u - v‖ ≤ ((4 / c ^ 4) * ‖normalFour δ u - normalFour δ v‖) ^ (1 / 3 : ℝ) := by
  have h := Real.rpow_le_rpow (pow_nonneg (norm_nonneg (u - v)) 3)
    (normalFour_inverse_cubic_bound δ c hc hδ u v) (by norm_num : 0 ≤ (1 / 3 : ℝ))
  have hroot : (‖u - v‖ ^ (3 : ℕ)) ^ (1 / 3 : ℝ) = ‖u - v‖ := by
    simpa using Real.pow_rpow_inv_natCast (norm_nonneg (u - v)) (by norm_num : (3 : ℕ) ≠ 0)
  rwa [hroot] at h

end OperatorDerivativeRewrite.Foundation.BanachLpDualityFourContinuity
