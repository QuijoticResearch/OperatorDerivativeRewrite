import Foundation.GaussianCore
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.Analysis.Convex.Integral

/-!
# Finite square entropy from an L⁴ hypothesis

The L⁴ assumption proves integrability of `f² log(f²)` on finite measure spaces.
Jensen then proves nonnegative square entropy on probability spaces. No
positivity of `f`, entropy-integrability assumption, or log-Sobolev inequality
is required. The value at zero is handled by Mathlib's continuous `r log r`.
-/

noncomputable section
open MeasureTheory Polynomial
open scoped ENNReal

namespace OperatorDerivativeRewrite.Foundation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Square entropy with the convention `0 * log 0 = 0`.
This real-valued definition represents finite entropy when both displayed
integrands are integrable. `integrable_sq_mul_log_of_memLp_four` establishes
that condition from L⁴ on finite measure spaces; finiteness is not asserted
for an arbitrary L² function by this definition alone. -/
def entropySq (μ : Measure Ω) (f : Ω → ℝ) : ℝ :=
  (∫ ω, (f ω) ^ 2 * Real.log ((f ω) ^ 2) ∂μ) -
    (∫ ω, (f ω) ^ 2 ∂μ) * Real.log (∫ ω, (f ω) ^ 2 ∂μ)

/-- A quadratic majorant for Mathlib's nonnegative entropy integrand. -/
theorem klFun_le_one_add_sq {r : ℝ} (hr : 0 ≤ r) :
    InformationTheory.klFun r ≤ 1 + r ^ 2 := by
  by_cases hzero : r = 0
  · simp [hzero, InformationTheory.klFun]
  have hpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hzero)
  have hlog := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hpos) hr
  unfold InformationTheory.klFun
  nlinarith

/-- L⁴ supplies a genuine integrable majorant for the square entropy integrand. -/
theorem integrable_sq_mul_log_of_memLp_four [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : MemLp f 4 μ) :
    Integrable (fun ω => (f ω) ^ 2 * Real.log ((f ω) ^ 2)) μ := by
  have hs : MemLp (fun ω => (f ω) ^ 2) 2 μ := by
    simpa only [pow_two] using mul_L4_memLp_two hf hf
  have hs_int : Integrable (fun ω => (f ω) ^ 2) μ :=
    (hf.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)).integrable_sq
  have hs4_int : Integrable (fun ω => ((f ω) ^ 2) ^ 2) μ := hs.integrable_sq
  have hk_int : Integrable (fun ω => InformationTheory.klFun ((f ω) ^ 2)) μ := by
    apply ((integrable_const (1 : ℝ)).add hs4_int).mono'
      (InformationTheory.continuous_klFun.comp_aestronglyMeasurable hs.aestronglyMeasurable)
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (InformationTheory.klFun_nonneg (sq_nonneg _))]
    exact klFun_le_one_add_sq (sq_nonneg _)
  convert (hk_int.sub (integrable_const (1 : ℝ))).add hs_int using 1
  ext ω
  simp only [Pi.add_apply, Pi.sub_apply, InformationTheory.klFun]
  ring

/-- Jensen's inequality for `r log r`, after proving both integrands integrable. -/
theorem entropySq_nonneg_of_memLp_four [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : MemLp f 4 μ) : 0 ≤ entropySq μ f := by
  have hs_int : Integrable (fun ω => (f ω) ^ 2) μ :=
    (hf.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)).integrable_sq
  have hlog_int := integrable_sq_mul_log_of_memLp_four hf
  have hj := Real.convexOn_mul_log.map_integral_le
    Real.continuous_mul_log.continuousOn isClosed_Ici
    (Filter.Eventually.of_forall fun ω => sq_nonneg (f ω)) hs_int hlog_int
  unfold entropySq
  exact sub_nonneg.mpr hj

/-- Square entropy depends only on the almost-everywhere class of the function. -/
theorem entropySq_congr {f g : Ω → ℝ} (h : f =ᵐ[μ] g) :
    entropySq μ f = entropySq μ g := by
  have hs : (fun ω => (f ω) ^ 2) =ᵐ[μ] (fun ω => (g ω) ^ 2) :=
    h.fun_comp (fun r : ℝ => r ^ 2)
  have hlog : (fun ω => (f ω) ^ 2 * Real.log ((f ω) ^ 2)) =ᵐ[μ]
      (fun ω => (g ω) ^ 2 * Real.log ((g ω) ^ 2)) :=
    hs.fun_comp (fun r : ℝ => r * Real.log r)
  unfold entropySq
  rw [integral_congr_ae hlog, integral_congr_ae hs]

@[simp]
theorem entropySq_zero : entropySq μ (fun _ : Ω => (0 : ℝ)) = 0 := by
  simp [entropySq]

/-- Every constant, including zero, has zero square entropy on a probability space. -/
@[simp]
theorem entropySq_const [IsProbabilityMeasure μ] (c : ℝ) :
    entropySq μ (fun _ : Ω => c) = 0 := by
  simp [entropySq]

namespace GaussianCore

/-- Every real polynomial has an integrable square entropy integrand under N(0,1). -/
theorem polynomial_sq_mul_log_integrable (p : ℝ[X]) :
    Integrable (fun x : ℝ => (p.eval x) ^ 2 * Real.log ((p.eval x) ^ 2)) γ :=
  integrable_sq_mul_log_of_memLp_four (polynomial_memLp p 4 (by norm_num))

end GaussianCore
end OperatorDerivativeRewrite.Foundation
