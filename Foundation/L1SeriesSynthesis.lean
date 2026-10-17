import Mathlib.Analysis.Normed.Lp.lpHolder

/-! Actual contractive synthesis maps from complex l1 coefficients into a complete normed space. -/
noncomputable section
open scoped lp ENNReal
namespace OperatorDerivativeRewrite.Foundation.L1SeriesSynthesis

abbrev Coeff := ℓ¹(ℕ, ℂ)

theorem coeff_summable (a : Coeff) : Summable (fun i => ‖a i‖) := by
  simpa using a.property.summable

theorem coeff_norm (a : Coeff) : (∑' i, ‖a i‖)=‖a‖ := by
  simpa using (lp.norm_eq_tsum_rpow (p := 1) (by norm_num) a).symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def term (φ : ℕ → E) (i : ℕ) : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight (φ i)

theorem term_norm_le (φ : ℕ → E) (hφ : ∀ i, ‖φ i‖ ≤ 1) (i : ℕ) : ‖term φ i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  change ‖z • φ i‖ ≤ 1*‖z‖
  rw [norm_smul]
  simpa only [one_mul, mul_one] using mul_le_mul_of_nonneg_left (hφ i) (norm_nonneg z)

def synthesis (φ : ℕ → E) (hφ : ∀ i, ‖φ i‖ ≤ 1) : Coeff →L[ℂ] E :=
  (lp.tsumCLM ℂ ℕ E).comp (lp.mapCLM 1 (term φ) zero_le_one (term_norm_le φ hφ))

theorem synthesis_apply (φ : ℕ → E) (hφ : ∀ i, ‖φ i‖ ≤ 1) (a : Coeff) :
    synthesis φ hφ a=∑' i, a i • φ i := rfl

theorem synthesis_norm_le (φ : ℕ → E) (hφ : ∀ i, ‖φ i‖ ≤ 1) : ‖synthesis φ hφ‖ ≤ 1 := by
  calc
    ‖synthesis φ hφ‖ ≤ ‖lp.tsumCLM ℂ ℕ E‖ *
        ‖lp.mapCLM 1 (term φ) zero_le_one (term_norm_le φ hφ)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*1 := mul_le_mul lp.norm_tsumCLM_le (lp.norm_mapCLM_le 1 _ _ _)
      (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem synthesis_bound (φ : ℕ → E) (hφ : ∀ i, ‖φ i‖ ≤ 1) (a : Coeff) :
    ‖synthesis φ hφ a‖ ≤ ‖a‖ := by
  simpa only [one_mul] using (synthesis φ hφ).le_of_opNorm_le (synthesis_norm_le φ hφ) a

theorem terms_summable (φ : ℕ → E) (hφ : ∀ i, ‖φ i‖ ≤ 1) (a : Coeff) :
    Summable (fun i => a i • φ i) := by
  apply (coeff_summable a).of_norm_bounded
  intro i
  rw [norm_smul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hφ i) (norm_nonneg (a i))

end OperatorDerivativeRewrite.Foundation.L1SeriesSynthesis
