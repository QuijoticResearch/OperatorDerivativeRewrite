import Foundation.BanachLpAdjoint
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# The signed fourth-power duality map on actual scalar Lp spaces

This is a fixed-exponent first step toward nonlinear Banach recovery. It
uses the genuine equivalence classes and Mathlib's Lp power theorem.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace OperatorDerivativeRewrite.Foundation.BanachLpDualityFour

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Cubing a real L⁴ class gives a genuine L^(4/3) function. -/
theorem cube_memLp (F : Lp ℝ 4 μ) :
    MemLp (fun ω => (F ω) ^ 3) (4 / 3) μ := by
  have hp := (Lp.memLp F).norm_rpow_div (3 : ℝ≥0∞)
  have hpow : MemLp (fun ω => ‖F ω‖ ^ 3) (4 / 3) μ := by
    simpa using hp
  have hmeas : AEStronglyMeasurable (fun ω => (F ω) ^ 3) μ := by
    fun_prop
  apply (memLp_norm_iff hmeas).mp
  simpa only [norm_pow] using hpow

/-- The genuine signed fourth-power duality map on Lp equivalence classes. -/
def dualityFour (F : Lp ℝ 4 μ) : Lp ℝ (4 / 3) μ :=
  (cube_memLp F).toLp (fun ω => (F ω) ^ 3)

theorem dualityFour_ae (F : Lp ℝ 4 μ) :
    (fun ω => dualityFour F ω) =ᵐ[μ] (fun ω => (F ω) ^ 3) :=
  (cube_memLp F).coeFn_toLp

/-- The fourth moment is an actual finite real integral. -/
theorem quartic_integrable (F : Lp ℝ 4 μ) :
    Integrable (fun ω => (F ω) ^ 4) μ := by
  have hi := (Lp.memLp F).integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  convert hi using 1
  ext ω
  simp [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity :
    0 ≤ (F ω) ^ 4)]

/-- The duality pairing has genuine integrability, including when `F=0`. -/
theorem dualityFour_pairing_integrable (F : Lp ℝ 4 μ) :
    Integrable (fun ω => dualityFour F ω * F ω) μ := by
  have hpair : (fun ω => dualityFour F ω * F ω) =ᵐ[μ]
      (fun ω => (F ω) ^ 4) := by
    filter_upwards [dualityFour_ae F] with ω hω
    rw [hω]
    ring
  exact (integrable_congr hpair).2 (quartic_integrable F)

/-- Exact fourth-power pairing for the signed duality map. -/
theorem dualityFour_pairing (F : Lp ℝ 4 μ) :
    (∫ ω, dualityFour F ω * F ω ∂μ) =
      ∫ ω, (F ω) ^ 4 ∂μ := by
  apply integral_congr_ae
  filter_upwards [dualityFour_ae F] with ω hω
  rw [hω]
  ring

/-- Exact conjugate norm identity for the fourth-power duality map. -/
theorem dualityFour_norm (F : Lp ℝ 4 μ) :
    ‖dualityFour F‖ = ‖F‖ ^ 3 := by
  rw [Lp.norm_def, Lp.norm_def]
  rw [eLpNorm_congr_ae (dualityFour_ae F)]
  have hnorm : eLpNorm (fun ω => (F ω) ^ 3) (4 / 3) μ =
      eLpNorm (fun ω => ‖F ω‖ ^ (3 : ℝ)) (4 / 3) μ := by
    have hm : AEStronglyMeasurable (fun ω => ‖F ω‖ ^ (3 : ℝ)) μ :=
      ((Lp.memLp F).aestronglyMeasurable.norm.aemeasurable.pow_const 3).aestronglyMeasurable
    apply eLpNorm_congr_norm_ae (by fun_prop) hm
    filter_upwards [] with ω
    simp [norm_pow, Real.norm_eq_abs]
  rw [hnorm, eLpNorm_norm_rpow (F : Ω → ℝ)
    (Lp.memLp F).aestronglyMeasurable (by norm_num : 0 < (3 : ℝ))]
  have hq : (4 / 3 : ℝ≥0∞) * ENNReal.ofReal (3 : ℝ) = 4 := by
    norm_num only [ENNReal.ofReal_ofNat]
    exact ENNReal.div_mul_cancel (by norm_num) (by norm_num)
  rw [hq]
  calc
    (eLpNorm (F : Ω → ℝ) 4 μ ^ (3 : ℝ)).toReal =
        (eLpNorm (F : Ω → ℝ) 4 μ ^ (3 : ℕ)).toReal :=
      congrArg ENNReal.toReal (ENNReal.rpow_natCast _ 3)
    _ = (eLpNorm (F : Ω → ℝ) 4 μ).toReal ^ 3 := ENNReal.toReal_pow _ 3

/-- The quartic integral is exactly the fourth power of the L⁴ norm. -/
theorem quartic_integral_eq_norm (F : Lp ℝ 4 μ) :
    (∫ ω, (F ω) ^ 4 ∂μ) = ‖F‖ ^ 4 := by
  let I : ℝ := ∫ ω, (F ω) ^ 4 ∂μ
  have hI : 0 ≤ I := integral_nonneg fun ω => by positivity
  have hformula := (Lp.memLp F).eLpNorm_eq_integral_rpow_norm
    (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ∞)
  have hint : (∫ ω, ‖F ω‖ ^ (4 : ℝ≥0∞).toReal ∂μ) = I := by
    simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
    congr 1
    funext ω
    simp [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ (F ω) ^ 4)]
  rw [hint] at hformula
  have hnorm : ‖F‖ = I ^ (4 : ℝ)⁻¹ := by
    rw [Lp.norm_def, hformula]
    exact ENNReal.toReal_ofReal (Real.rpow_nonneg hI _)
  rw [hnorm]
  exact (Real.rpow_inv_natCast_pow hI (by norm_num : (4 : ℕ) ≠ 0)).symm

/-- The fourth-power pairing is the exact Banach duality identity. -/
theorem dualityFour_pairing_eq_norm (F : Lp ℝ 4 μ) :
    (∫ ω, dualityFour F ω * F ω ∂μ) = ‖F‖ ^ 4 := by
  rw [dualityFour_pairing, quartic_integral_eq_norm]

private instance : ENNReal.HolderConjugate (4 / 3 : ℝ≥0∞) 4 := by
  apply ENNReal.HolderConjugate.of_toReal
  have hq : (4 / 3 : ℝ≥0∞).toReal = (4 / 3 : ℝ) := by
    simp [ENNReal.toReal_div]
  simp only [hq, ENNReal.toReal_ofNat]
  rw [Real.holderConjugate_iff]
  constructor <;> norm_num

private instance : Fact ((1 : ℝ≥0∞) ≤ (4 / 3 : ℝ≥0∞)) :=
  ⟨ENNReal.HolderTriple.le (4 / 3 : ℝ≥0∞) 4 1⟩

private instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A concrete nonlinear normal map from an actual bounded `L⁴` operator.
Its existence as a function uses no minimization or surjectivity theorem. -/
def normalFour (δ : H →L[ℝ] Lp ℝ 4 μ) (u : H) : StrongDual ℝ H :=
  BanachLpAdjoint.boundedBanachDerivative δ (dualityFour (δ u))

/-- The exact energy identity for the nonlinear normal map. -/
theorem normalFour_pairing (δ : H →L[ℝ] Lp ℝ 4 μ) (u : H) :
    normalFour δ u u = ‖δ u‖ ^ 4 := by
  rw [normalFour, BanachLpAdjoint.boundedBanachDerivative_apply]
  exact dualityFour_pairing_eq_norm (δ u)

/-- A genuine lower bound on `δ` yields a quantitative coercive estimate.
This does not assert that the nonlinear normal equation has a solution. -/
theorem normalFour_coercive (δ : H →L[ℝ] Lp ℝ 4 μ)
    (c : ℝ) (hc : 0 < c) (hδ : ∀ u : H, c * ‖u‖ ≤ ‖δ u‖)
    (u : H) :
    c ^ 4 * ‖u‖ ^ 4 ≤ normalFour δ u u := by
  rw [normalFour_pairing]
  calc
    c ^ 4 * ‖u‖ ^ 4 = (c * ‖u‖) ^ 4 := by ring
    _ ≤ ‖δ u‖ ^ 4 := pow_le_pow_left₀ (mul_nonneg hc.le (norm_nonneg _)) (hδ u) 4

/-- Signed cubic powers are monotone, including at zero. -/
theorem cubic_monotone (a b : ℝ) :
    0 ≤ (a ^ 3 - b ^ 3) * (a - b) := by
  have hsq : 0 ≤ (a - b) ^ 2 := sq_nonneg _
  have hq : 0 ≤ (a + b / 2) ^ 2 + (3 / 4 : ℝ) * b ^ 2 := by
    have h1 := sq_nonneg (a + b / 2)
    have h2 := sq_nonneg b
    nlinarith
  calc
    0 ≤ (a - b) ^ 2 * ((a + b / 2) ^ 2 + (3 / 4 : ℝ) * b ^ 2) :=
      mul_nonneg hsq hq
    _ = (a ^ 3 - b ^ 3) * (a - b) := by ring

/-- The nonlinear normal map is monotone as an actual dual-valued map.
No strictness or surjectivity is asserted. -/
theorem normalFour_monotone (δ : H →L[ℝ] Lp ℝ 4 μ) (u v : H) :
    0 ≤ (normalFour δ u - normalFour δ v) (u - v) := by
  let a : Ω → ℝ := fun ω => (dualityFour (δ u)) ω * (δ (u - v)) ω
  let b : Ω → ℝ := fun ω => (dualityFour (δ v)) ω * (δ (u - v)) ω
  have ha : Integrable a μ := BanachLpAdjoint.integrable_mul δ (dualityFour (δ u)) (u - v)
  have hb : Integrable b μ := BanachLpAdjoint.integrable_mul δ (dualityFour (δ v)) (u - v)
  have hrepr : (fun ω => a ω - b ω) =ᵐ[μ]
      (fun ω => (((δ u) ω) ^ 3 - ((δ v) ω) ^ 3) *
        (((δ u) ω) - ((δ v) ω))) := by
    filter_upwards [dualityFour_ae (δ u), dualityFour_ae (δ v),
      Lp.coeFn_sub (δ u) (δ v)] with ω hu hv hsub
    dsimp [a, b]
    rw [hu, hv]
    have hδ : (δ (u - v)) ω = (δ u) ω - (δ v) ω := by
      simpa only [map_sub, Pi.sub_apply] using hsub
    rw [hδ]
    ring
  calc
    0 ≤ ∫ ω, a ω - b ω ∂μ := by
      apply integral_nonneg_of_ae
      filter_upwards [hrepr] with ω hω
      rw [hω]
      exact cubic_monotone _ _
    _ = (normalFour δ u - normalFour δ v) (u - v) := by
      rw [integral_sub ha hb]
      simp only [sub_apply, normalFour,
        BanachLpAdjoint.boundedBanachDerivative_apply]
      rfl

end OperatorDerivativeRewrite.Foundation.BanachLpDualityFour
