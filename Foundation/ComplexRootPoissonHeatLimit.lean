import Foundation.ComplexRootPoissonTransform
import Foundation.ComplexRootHeatTransformLimit

/-! Genuine Poissonized complex probability transforms approach the biharmonic heat symbol. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.ComplexRootPoissonHeatLimit
open ComplexRootHeatTransformLimit ComplexRootTransformConsistency

theorem transform_limit (T : ℝ≥0) (ξ : ℝ) :
    Tendsto (fun n : ℕ => ∫ z, Complex.exp (Complex.I * (ξ : ℂ) * z)
      ∂ComplexRootPoissonLaw.law (n : ℝ≥0) (amplitude T n)) atTop
      (𝓝 ((Real.exp (-(T : ℝ)*ξ^4) : ℝ) : ℂ)) := by
  have he := (Real.continuous_exp.tendsto _).comp (scaled_factor_limit T ξ)
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp he
  have hid (n : ℕ) :
      (∫ z, Complex.exp (Complex.I * (ξ : ℂ) * z)
        ∂ComplexRootPoissonLaw.law (n : ℝ≥0) (amplitude T n)) =
      ((Real.exp ((n : ℝ)*(factor (amplitude T n * ξ)-1)) : ℝ) : ℂ) := by
    rw [ComplexRootPoissonTransform.transform_formula, Complex.ofReal_exp]
    congr 1
    simp only [factor, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_natCast,
      Complex.ofReal_one, NNReal.coe_natCast]
  simpa only [Function.comp_def, ← hid] using hc

theorem operator_symbol_limit (T : ℝ≥0) (ξ : ℝ) :
    Tendsto (fun n : ℕ => ∫ z, Complex.exp (Complex.I * ((2*Real.pi*ξ : ℝ) : ℂ) * z)
      ∂ComplexRootPoissonLaw.law (n : ℝ≥0) (amplitude T n)) atTop
      (𝓝 (HigherHeatL2.symbol 2 T ξ)) := by
  simpa only [HigherHeatL2.symbol, show 2*2=4 from rfl] using transform_limit T (2*Real.pi*ξ)

theorem rate_scaled_transform_limit (T : ℝ≥0) (ξ : ℝ) :
    Tendsto (fun n : ℕ => ∫ z, Complex.exp (Complex.I * (ξ : ℂ) * z)
      ∂ComplexRootPoissonLaw.law ((n : ℝ≥0)*T) (amplitude 1 n)) atTop
      (𝓝 ((Real.exp (-(T : ℝ)*ξ^4) : ℝ) : ℂ)) := by
  have hm : Tendsto (fun n : ℕ => (n : ℝ)*(T : ℝ)*(factor (amplitude 1 n * ξ)-1))
      atTop (𝓝 (-(T : ℝ)*ξ^4)) := by
    have hf : (fun n : ℕ => (n : ℝ)*(T : ℝ)*(factor (amplitude 1 n * ξ)-1)) =
        (fun n : ℕ => (T : ℝ)*((n : ℝ)*(factor (amplitude 1 n * ξ)-1))) := by
      funext n
      ring
    rw [hf]
    simpa only [NNReal.coe_one, one_mul, mul_neg, neg_mul] using
      (scaled_factor_limit 1 ξ).const_mul (T : ℝ)
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp
    ((Real.continuous_exp.tendsto _).comp hm)
  have hid (n : ℕ) :
      (∫ z, Complex.exp (Complex.I * (ξ : ℂ) * z)
        ∂ComplexRootPoissonLaw.law ((n : ℝ≥0)*T) (amplitude 1 n)) =
      ((Real.exp ((n : ℝ)*(T : ℝ)*(factor (amplitude 1 n * ξ)-1)) : ℝ) : ℂ) := by
    rw [ComplexRootPoissonTransform.transform_formula, Complex.ofReal_exp]
    congr 1
    simp only [factor, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_natCast,
      Complex.ofReal_one, NNReal.coe_natCast, NNReal.coe_mul]
  simpa only [Function.comp_def, ← hid] using hc

theorem rate_scaled_operator_symbol_limit (T : ℝ≥0) (ξ : ℝ) :
    Tendsto (fun n : ℕ => ∫ z, Complex.exp (Complex.I * ((2*Real.pi*ξ : ℝ) : ℂ) * z)
      ∂ComplexRootPoissonLaw.law ((n : ℝ≥0)*T) (amplitude 1 n)) atTop
      (𝓝 (HigherHeatL2.symbol 2 T ξ)) := by
  simpa only [HigherHeatL2.symbol, show 2*2=4 from rfl] using
    rate_scaled_transform_limit T (2*Real.pi*ξ)

end OperatorDerivativeRewrite.Foundation.ComplexRootPoissonHeatLimit
