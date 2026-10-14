import Foundation.IBMPathwiseFundamental
import Foundation.IBMMollifiedChainRule

/-! Nonlinear chain rules on the actually constructed smooth Gaussian scenery. -/
noncomputable section
open MeasureTheory
open scoped NNReal

namespace OperatorDerivativeRewrite.Foundation.IBMConstructedChainRule
open InfiniteGaussian IBMDyadicExtension IBMPointwiseEvaluation IBMPathwiseFundamental
attribute [local irreducible] IBMDyadicExtension.field

/-- Both spatial chain rules hold for the original-source C² modification,
on the same full-measure event for every scale, shift and spatial point. -/
theorem field_chain_rules (f f₁ f₂ : ℝ → ℝ)
    (hf : ∀ z, HasDerivAt f (f₁ z) z) (hf₁ : ∀ z, HasDerivAt f₁ (f₂ z) z) :
    ∀ᵐ ω ∂gaussianProduct, ∀ (n : ℕ) (a r : ℝ),
      HasDerivAt (fun q => f (a + field n 0 ω q))
        (f₁ (a + field n 0 ω r) * field n 1 ω r) r ∧
      deriv (deriv (fun q => f (a + field n 0 ω q))) r =
        f₂ (a + field n 0 ω r) * (field n 1 ω r)^2 +
          f₁ (a + field n 0 ω r) * field n 2 ω r := by
  filter_upwards [field_common_hasDerivAt] with ω hω
  intro n a r
  exact ⟨IBMMollifiedChainRule.g_hasDerivAt f f₁ _ _ a
      (fun q => (hω n q).1) hf r,
    IBMMollifiedChainRule.deriv_deriv_g f f₁ f₂ _ _ _ a
      (fun q => (hω n q).1) (fun q => (hω n q).2) hf hf₁ r⟩

def firstCoefficient (f₁ : ℝ → ℝ) (a : ℝ) (n : ℕ) (t : ℝ≥0)
    (ω : IBMSourceLaws.JointSample) : ℝ :=
  f₁ (a + value n 0 t ω) * value n 1 t ω

def secondCoefficient (f₁ f₂ : ℝ → ℝ) (a : ℝ) (n : ℕ) (t : ℝ≥0)
    (ω : IBMSourceLaws.JointSample) : ℝ :=
  f₂ (a + value n 0 t ω) * (value n 1 t ω)^2 +
    f₁ (a + value n 0 t ω) * value n 2 t ω

theorem firstCoefficient_measurable (f₁ : ℝ → ℝ) (hf₁ : Continuous f₁)
    (a : ℝ) (n : ℕ) (t : ℝ≥0) : Measurable (firstCoefficient f₁ a n t) :=
  (hf₁.measurable.comp (measurable_const.add (value_measurable n 0 t))).mul
    (value_measurable n 1 t)

theorem secondCoefficient_measurable (f₁ f₂ : ℝ → ℝ)
    (hf₁ : Continuous f₁) (hf₂ : Continuous f₂) (a : ℝ) (n : ℕ) (t : ℝ≥0) :
    Measurable (secondCoefficient f₁ f₂ a n t) :=
  ((hf₂.measurable.comp (measurable_const.add (value_measurable n 0 t))).mul
    ((value_measurable n 1 t).pow_const 2)).add
      ((hf₁.measurable.comp (measurable_const.add (value_measurable n 0 t))).mul
        (value_measurable n 2 t))

theorem bounded_value_mul_memLp (f : ℝ → ℝ) (hf : Continuous f) (C : ℝ)
    (hbound : ∀ z, |f z| ≤ C) (a : ℝ) (n : ℕ) (i : Fin 3) (t : ℝ≥0) :
    MemLp (fun ω => f (a + value n 0 t ω) * value n i t ω) 2 IBMSourceLaws.jointMeasure := by
  apply MemLp.mono' ((value_memLp n i t).norm.const_mul C)
    (((hf.measurable.comp (measurable_const.add (value_measurable n 0 t))).mul
      (value_measurable n i t)).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro ω
  simp only [Real.norm_eq_abs, Pi.mul_apply, Pi.add_apply, Function.comp_apply, abs_mul]
  exact mul_le_mul_of_nonneg_right (hbound _) (abs_nonneg _)

theorem firstCoefficient_memLp (f₁ : ℝ → ℝ) (hf₁ : Continuous f₁) (C : ℝ)
    (hbound : ∀ z, |f₁ z| ≤ C) (a : ℝ) (n : ℕ) (t : ℝ≥0) :
    MemLp (firstCoefficient f₁ a n t) 2 IBMSourceLaws.jointMeasure :=
  bounded_value_mul_memLp f₁ hf₁ C hbound a n 1 t

/-- Bounded first and second test derivatives give a genuine integrable
fixed-time bulk coefficient. No time-integrated or stochastic integral is asserted. -/
theorem secondCoefficient_integrable (f₁ f₂ : ℝ → ℝ)
    (hf₁ : Continuous f₁) (hf₂ : Continuous f₂) (C₁ C₂ : ℝ)
    (hbound₁ : ∀ z, |f₁ z| ≤ C₁) (hbound₂ : ∀ z, |f₂ z| ≤ C₂)
    (a : ℝ) (n : ℕ) (t : ℝ≥0) :
    Integrable (secondCoefficient f₁ f₂ a n t) IBMSourceLaws.jointMeasure := by
  have hs : Integrable (fun ω => (value n 1 t ω)^2) IBMSourceLaws.jointMeasure := by
    simpa only [Real.norm_eq_abs, sq_abs] using (value_memLp n 1 t).integrable_norm_pow'
  have hterm : Integrable (fun ω => f₂ (a + value n 0 t ω) * (value n 1 t ω)^2)
      IBMSourceLaws.jointMeasure := by
    apply Integrable.mono' (hs.const_mul C₂)
      (((hf₂.measurable.comp (measurable_const.add (value_measurable n 0 t))).mul
        ((value_measurable n 1 t).pow_const 2)).aestronglyMeasurable)
    apply Filter.Eventually.of_forall
    intro ω
    simp only [Real.norm_eq_abs, Pi.mul_apply, Pi.add_apply, Function.comp_apply,
      abs_mul, abs_pow, sq_abs]
    exact mul_le_mul_of_nonneg_right (hbound₂ _) (sq_nonneg _)
  exact hterm.add ((bounded_value_mul_memLp f₁ hf₁ C₁ hbound₁ a n 2 t).integrable (by norm_num))

end OperatorDerivativeRewrite.Foundation.IBMConstructedChainRule
