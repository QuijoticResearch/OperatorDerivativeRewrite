import Foundation.GaussianPredictableFull

/-! Independence of the entire future-increment process from the raw past,
and genuine square-integrable multiplication without bounded past coefficients. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianPastFutureProducts
open InfiniteGaussian GaussianTimeProcess GaussianPredictableStep

def futureProcess (s : ℝ≥0) (ω : SampleSpace) : ℝ≥0 → ℝ :=
  fun r => process (s + r) ω - process s ω

def futureValue (s : ℝ≥0) (b : (ℝ≥0 → ℝ) → ℝ) (ω : SampleSpace) : ℝ :=
  b (futureProcess s ω)

theorem past_future_independent (s : ℝ≥0)
    {a : (Iic s → ℝ) → ℝ} {b : (ℝ≥0 → ℝ) → ℝ}
    (ha : Measurable a) (hb : Measurable b) :
    IndepFun (pastCoefficient process s a) (futureValue s b) gaussianProduct :=
  (process_isPreBrownian.indepFun_shift s).symm.comp ha hb

theorem past_future_sq_integrable (s : ℝ≥0)
    {a : (Iic s → ℝ) → ℝ} {b : (ℝ≥0 → ℝ) → ℝ}
    (ha : Measurable a) (hb : Measurable b)
    (hA : MemLp (pastCoefficient process s a) 2 gaussianProduct)
    (hB : MemLp (futureValue s b) 2 gaussianProduct) :
    Integrable (fun ω => (pastCoefficient process s a ω * futureValue s b ω) ^ 2)
      gaussianProduct := by
  have hi := (past_future_independent s ha hb).comp
    (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  convert hi.integrable_mul hA.integrable_sq hB.integrable_sq using 1
  ext ω
  simp only [Function.comp_def, id_eq, Pi.mul_apply, mul_pow]

theorem past_future_memLp (s : ℝ≥0)
    {a : (Iic s → ℝ) → ℝ} {b : (ℝ≥0 → ℝ) → ℝ}
    (ha : Measurable a) (hb : Measurable b)
    (hA : MemLp (pastCoefficient process s a) 2 gaussianProduct)
    (hB : MemLp (futureValue s b) 2 gaussianProduct) :
    MemLp (fun ω => pastCoefficient process s a ω * futureValue s b ω) 2 gaussianProduct :=
  (memLp_two_iff_integrable_sq (hA.aestronglyMeasurable.mul hB.aestronglyMeasurable)).mpr
    (past_future_sq_integrable s ha hb hA hB)

theorem past_future_sq_integral (s : ℝ≥0)
    {a : (Iic s → ℝ) → ℝ} {b : (ℝ≥0 → ℝ) → ℝ}
    (ha : Measurable a) (hb : Measurable b)
    (hA : MemLp (pastCoefficient process s a) 2 gaussianProduct)
    (hB : MemLp (futureValue s b) 2 gaussianProduct) :
    (∫ ω, (pastCoefficient process s a ω * futureValue s b ω) ^ 2 ∂gaussianProduct) =
      (∫ ω, pastCoefficient process s a ω ^ 2 ∂gaussianProduct) *
        ∫ ω, futureValue s b ω ^ 2 ∂gaussianProduct := by
  have hi := (past_future_independent s ha hb).comp
    (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have he := hi.integral_fun_mul_eq_mul_integral
    hA.integrable_sq.aestronglyMeasurable hB.integrable_sq.aestronglyMeasurable
  simpa only [Function.comp_def, id_eq, mul_pow] using he

/-- Whole future errors may be multiplied by an unbounded L2 past coefficient.
The factorization, not continuity of arbitrary L2 multiplication, justifies the limit. -/
theorem weighted_future_error_tendsto (s : ℝ≥0)
    {a : (Iic s → ℝ) → ℝ} {b : ℕ → (ℝ≥0 → ℝ) → ℝ}
    (ha : Measurable a) (hb : ∀ n, Measurable (b n))
    (hA : MemLp (pastCoefficient process s a) 2 gaussianProduct)
    (hB : ∀ n, MemLp (futureValue s (b n)) 2 gaussianProduct)
    (he : Tendsto (fun n => ∫ ω, futureValue s (b n) ω ^ 2 ∂gaussianProduct) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (pastCoefficient process s a ω * futureValue s (b n) ω) ^ 2
      ∂gaussianProduct) atTop (𝓝 0) := by
  simp_rw [past_future_sq_integral s ha (hb _) hA (hB _)]
  simpa only [mul_zero] using he.const_mul (∫ ω, pastCoefficient process s a ω ^ 2 ∂gaussianProduct)

end OperatorDerivativeRewrite.Foundation.GaussianPastFutureProducts
