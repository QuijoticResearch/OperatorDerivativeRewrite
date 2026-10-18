import Foundation.HigherHeatPredictableL1
import Foundation.HigherHeatJetChannels

/-! Actual signed one-step predictable power integrals with explicit unbounded domains. -/
noncomputable section
open MeasureTheory Polynomial
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.HigherHeatPredictableJets
open HigherHeatSignedLaws HigherHeatPolynomialRealization HigherHeatFourierInnovations
open HigherHeatPredictableL1 HigherHeatJetChannels

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

theorem kernel_power_integrable (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (r : ℕ) :
    Integrable (fun z : ℝ => (z : ℂ)^r*(realKernel m hm t ht z : ℂ)) := by
  have hi : Integrable (fun z : ℝ =>
      ((((X^r : Polynomial ℝ).eval z)*realKernel m hm t ht z : ℝ):ℂ)) :=
    (polynomial_integrable m hm t ht (X^r)).ofReal
  simpa only [eval_pow, eval_X, Complex.ofReal_mul, Complex.ofReal_pow] using hi

theorem power_integrable (past : Ω → ℝ) (hp : Measurable past) (hi : Integrable past μ)
    (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (G : Ω → ℂ) (hGm : Measurable G) (hG : Integrable (fun w => (past w : ℂ)*G w) μ)
    (r : ℕ) : (extendedLaw μ past m hm t ht).Integrable
      (fun w : Ω × ℝ => G w.1*(w.2 : ℂ)^r) := by
  apply product_signed_integrable μ past hp hi m hm t ht G hGm
    (fun z : ℝ => (z : ℂ)^r) (by fun_prop) hG
  exact kernel_power_integrable m hm t ht r

theorem power_integral (past : Ω → ℝ) (hp : Measurable past) (hi : Integrable past μ)
    (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (G : Ω → ℂ) (hGm : Measurable G) (hG : Integrable (fun w => (past w : ℂ)*G w) μ)
    (r : ℕ) :
    (∫ᵛ w, G w.1*(w.2 : ℂ)^r ∂<•extendedLaw μ past m hm t ht) =
      (∫ w, (past w : ℂ)*G w ∂μ) * (kernelExpectation m hm t ht (X^r):ℂ) := by
  rw [product_integral μ past hp hi m hm t ht G hGm (fun z : ℝ => (z : ℂ)^r)
    (by fun_prop) hG (kernel_power_integrable m hm t ht r)]
  have he := complex_expectation m hm t ht (X^r)
  simp only [eval_pow, eval_X, Complex.ofReal_pow, ← realKernel_coe m hm t ht] at he
  rw [he]

theorem power_mean_zero (past : Ω → ℝ) (hp : Measurable past) (hi : Integrable past μ)
    (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (G : Ω → ℂ) (hGm : Measurable G) (hG : Integrable (fun w => (past w : ℂ)*G w) μ)
    (r : ℕ) (hr : 0 < r) (hrp : r < 2 * m) :
    (∫ᵛ w, G w.1*(w.2 : ℂ)^r ∂<•extendedLaw μ past m hm t ht) = 0 := by
  rw [power_integral μ past hp hi m hm t ht G hGm hG r,
    low_moment_zero m hm t ht r hr hrp, Complex.ofReal_zero, mul_zero]

theorem paired_integrable (past : Ω → ℝ) (hp : Measurable past) (hi : Integrable past μ)
    (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (G H : Ω → ℂ) (hGm : Measurable G) (hHm : Measurable H)
    (hGH : Integrable (fun w => (past w : ℂ)*(G w*H w)) μ) (r s : ℕ) :
    (extendedLaw μ past m hm t ht).Integrable (fun w : Ω × ℝ =>
      (G w.1*(w.2 : ℂ)^r)*(H w.1*(w.2 : ℂ)^s)) := by
  have he : (fun w : Ω × ℝ => (G w.1*(w.2 : ℂ)^r)*(H w.1*(w.2 : ℂ)^s)) =
      (fun w => (G w.1*H w.1)*(w.2 : ℂ)^(r + s)) := by
    funext w
    rw [pow_add]
    ring
  rw [he]
  exact power_integrable μ past hp hi m hm t ht (fun w => G w*H w) (hGm.mul hHm) hGH (r + s)

theorem paired_integral (past : Ω → ℝ) (hp : Measurable past) (hi : Integrable past μ)
    (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (G H : Ω → ℂ) (hGm : Measurable G) (hHm : Measurable H)
    (hGH : Integrable (fun w => (past w : ℂ)*(G w*H w)) μ)
    (r s : ℕ) (hr : 0 < r) (hrp : r < 2 * m) (hs : 0 < s) (hsp : s < 2 * m) :
    (∫ᵛ w, (G w.1*(w.2 : ℂ)^r)*(H w.1*(w.2 : ℂ)^s) ∂<•extendedLaw μ past m hm t ht) =
      if r + s = 2 * m then (cumulant m * (t : ℝ))*(∫ w, (past w : ℂ)*(G w*H w) ∂μ) else 0 := by
  have he : (fun w : Ω × ℝ => (G w.1*(w.2 : ℂ)^r)*(H w.1*(w.2 : ℂ)^s)) =
      (fun w => (G w.1*H w.1)*(w.2 : ℂ)^(r + s)) := by
    funext w
    rw [pow_add]
    ring
  rw [he, power_integral μ past hp hi m hm t ht (fun w => G w*H w) (hGm.mul hHm) hGH (r + s),
    middle_moment m hm t ht (r + s) (by omega) (by omega)]
  by_cases hrs : r + s = 2 * m <;> simp only [hrs, ↓reduceIte, mul_zero] <;> ring

end OperatorDerivativeRewrite.Foundation.HigherHeatPredictableJets
