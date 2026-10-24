import Foundation.GaussianCore
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual Gaussian Bochner score integrals for half-Holder curves. The
centered difference gives a square-integrable terminal singularity. This file
does not assume or assert a heat-derivative or Clark--Ocone identification. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianHalfHolderScore
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def mass : ℝ := ∫ z : ℝ, 1+z^2 ∂GaussianCore.γ

theorem polynomial_integrable : Integrable (fun z : ℝ => 1+z^2) GaussianCore.γ := by
  have hi := (GaussianCore.polynomial_memLp (1+Polynomial.X^2) 1 (by simp)).integrable
    (by norm_num)
  apply hi.congr
  exact Filter.Eventually.of_forall (fun z => by simp)

theorem mass_nonneg : 0 ≤ mass := integral_nonneg (fun z => by positivity)

def score (f : ℝ → E) (b h : ℝ) : E :=
  h⁻¹ • ∫ z : ℝ, z • (f (b+h*z)-f b) ∂GaussianCore.γ

omit [CompleteSpace E] in
theorem score_zero (f : ℝ → E) (b : ℝ) : score f b 0 = 0 := by
  simp [score]

omit [CompleteSpace E] in
theorem score_stronglyMeasurable (f : ℝ → E) (hf : Continuous f) :
    StronglyMeasurable (fun p : ℝ × ℝ => score f p.1 p.2) := by
  have hi : StronglyMeasurable (fun p : (ℝ × ℝ) × ℝ =>
      p.2 • (f (p.1.1+p.1.2*p.2)-f p.1.1)) := by
    apply Continuous.stronglyMeasurable
    exact continuous_snd.smul ((hf.comp
      (continuous_fst.fst.add (continuous_fst.snd.mul continuous_snd))).sub
        (hf.comp continuous_fst.fst))
  exact measurable_snd.inv.stronglyMeasurable.smul hi.integral_prod_right'

omit [CompleteSpace E] in
theorem integrand_bound (f : ℝ → E) (C : ℝ) (hC : 0 ≤ C)
    (hH : ∀ x y, ‖f x-f y‖^2 ≤ C^2*|x-y|) (b h : ℝ) (hh : 0 ≤ h) (z : ℝ) :
    ‖z • (f (b+h*z)-f b)‖ ≤ C*Real.sqrt h*(1+z^2) := by
  have hd := hH (b+h*z) b
  rw [add_sub_cancel_left,abs_mul,abs_of_nonneg hh] at hd
  have hz : z^2*|z| ≤ (1+z^2)^2 := by
    nlinarith [sq_nonneg (z^2-|z|),sq_abs z]
  have he : (|z| * ‖f (b+h*z)-f b‖)^2 ≤ (C*Real.sqrt h*(1+z^2))^2 := by
    calc
      _ = z^2*‖f (b+h*z)-f b‖^2 := by rw [mul_pow,sq_abs]
      _ ≤ z^2*(C^2*(h*|z|)) := mul_le_mul_of_nonneg_left hd (sq_nonneg z)
      _ = (C^2*h)*(z^2*|z|) := by ring
      _ ≤ (C^2*h)*(1+z^2)^2 :=
        mul_le_mul_of_nonneg_left hz (mul_nonneg (sq_nonneg C) hh)
      _ = _ := by rw [mul_pow,mul_pow,Real.sq_sqrt hh]
  rw [norm_smul,Real.norm_eq_abs]
  have hm : 0 ≤ C*Real.sqrt h*(1+z^2) :=
    mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg h)) (by positivity)
  exact (sq_le_sq₀ (mul_nonneg (abs_nonneg z) (norm_nonneg _)) hm).mp he

theorem score_integrable (f : ℝ → E) (hf : Continuous f) (C : ℝ) (hC : 0 ≤ C)
    (hH : ∀ x y, ‖f x-f y‖^2 ≤ C^2*|x-y|) (b h : ℝ) (hh : 0 ≤ h) :
    Integrable (fun z : ℝ => z • (f (b+h*z)-f b)) GaussianCore.γ := by
  apply (polynomial_integrable.const_mul (C*Real.sqrt h)).mono'
    (continuous_id.smul ((hf.comp (continuous_const.add
      (continuous_const.mul continuous_id))).sub continuous_const)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (integrand_bound f C hC hH b h hh)

theorem score_norm (f : ℝ → E) (hf : Continuous f) (C : ℝ) (hC : 0 ≤ C)
    (hH : ∀ x y, ‖f x-f y‖^2 ≤ C^2*|x-y|) (b h : ℝ) (hh : 0 < h) :
    ‖score f b h‖ ≤ (C*mass)/Real.sqrt h := by
  have hi := score_integrable f hf C hC hH b h hh.le
  have hb : ‖∫ z : ℝ, z • (f (b+h*z)-f b) ∂GaussianCore.γ‖ ≤
      C*Real.sqrt h*mass := by
    apply (norm_integral_le_integral_norm _).trans
    rw [mass,← integral_const_mul]
    exact integral_mono hi.norm (polynomial_integrable.const_mul _)
      (integrand_bound f C hC hH b h hh.le)
  rw [score,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hh]
  calc
    _ ≤ h⁻¹*(C*Real.sqrt h*mass) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hh.le)
    _ = _ := by
      have hs := Real.sq_sqrt hh.le
      have hsp := Real.sqrt_pos.mpr hh
      field_simp
      rw [hs]
      ring

theorem score_energy (f : ℝ → E) (hf : Continuous f) (C : ℝ) (hC : 0 ≤ C)
    (hH : ∀ x y, ‖f x-f y‖^2 ≤ C^2*|x-y|) (b h : ℝ) (hh : 0 < h) :
    ‖score f b h‖^2 ≤ (C*mass)^2/h := by
  simpa only [div_pow,Real.sq_sqrt hh.le] using
    pow_le_pow_left₀ (norm_nonneg (score f b h)) (score_norm f hf C hC hH b h hh) 2

end OperatorDerivativeRewrite.Foundation.GaussianHalfHolderScore
