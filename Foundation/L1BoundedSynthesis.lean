import Foundation.L1SeriesSynthesis

/-! The existing bounded l1 synthesis mechanism for arbitrary indices and scalar fields. -/
noncomputable section
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.L1BoundedSynthesis
variable {ι 𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E]

def term (φ : ι → E) (i : ι) : 𝕜 →L[𝕜] E :=
  (ContinuousLinearMap.id 𝕜 𝕜).smulRight (φ i)

omit [CompleteSpace E] in
theorem term_norm (φ : ι → E) (hφ : ∀ i, ‖φ i‖ ≤ 1) (i : ι) : ‖term φ i (𝕜 := 𝕜)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro c
  change ‖c • φ i‖ ≤ 1*‖c‖
  rw [norm_smul]
  simpa only [one_mul, mul_one] using mul_le_mul_of_nonneg_left (hφ i) (norm_nonneg c)

def synthesis (φ : ι → E) (hφ : ∀ i, ‖φ i‖ ≤ 1) : lp (fun _ : ι => 𝕜) 1 →L[𝕜] E :=
  (lp.tsumCLM 𝕜 ι E).comp (lp.mapCLM 1 (term φ) zero_le_one (term_norm φ hφ))

theorem synthesis_apply (φ : ι → E) (hφ : ∀ i, ‖φ i‖ ≤ 1) (u : lp (fun _ : ι => 𝕜) 1) :
    synthesis φ hφ u = ∑' i, u i • φ i := rfl

theorem synthesis_norm (φ : ι → E) (hφ : ∀ i, ‖φ i‖ ≤ 1) : ‖synthesis φ hφ (𝕜 := 𝕜)‖ ≤ 1 := by
  have h₁ : ‖lp.tsumCLM 𝕜 ι E‖ ≤ 1 := lp.norm_tsumCLM_le
  have h₂ : ‖lp.mapCLM 1 (term (𝕜 := 𝕜) φ) zero_le_one
      (term_norm (𝕜 := 𝕜) φ hφ)‖ ≤ 1 :=
    lp.norm_mapCLM_le 1 (term (𝕜 := 𝕜) φ) zero_le_one (term_norm (𝕜 := 𝕜) φ hφ)
  calc
    _ ≤ ‖lp.tsumCLM 𝕜 ι E‖ * ‖lp.mapCLM 1 (term (𝕜 := 𝕜) φ) zero_le_one
        (term_norm (𝕜 := 𝕜) φ hφ)‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*1 := mul_le_mul h₁ h₂ (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem synthesis_single [DecidableEq ι] (φ : ι → E) (hφ : ∀ i, ‖φ i‖ ≤ 1) (j : ι) (c : 𝕜) :
    synthesis φ hφ (lp.single 1 j c) = c • φ j := by
  classical
  rw [synthesis_apply, tsum_eq_single j]
  · simp
  · intro i hi
    simp [lp.single_apply, hi]

theorem terms_summable (φ : ι → E) (hφ : ∀ i, ‖φ i‖ ≤ 1)
    (u : lp (fun _ : ι => 𝕜) 1) : Summable (fun i => u i • φ i) := by
  have hs : Summable (fun i => ‖u i‖) := by simpa using u.property.summable
  apply hs.of_norm_bounded
  intro i
  rw [norm_smul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hφ i) (norm_nonneg (u i))

end OperatorDerivativeRewrite.Foundation.L1BoundedSynthesis
