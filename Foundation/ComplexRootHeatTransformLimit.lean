import Foundation.ComplexRootTransformConsistency
import Foundation.HigherHeatL2
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! A genuine complex probability-walk approximation of the actual biharmonic Fourier multiplier. -/
noncomputable section
open MeasureTheory Filter Asymptotics
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.ComplexRootHeatTransformLimit
open ComplexFourthRootWalk ComplexRootOneStepCalculus ComplexRootTransformConsistency

def amplitude (T : ℝ≥0) (n : ℕ) : ℝ := Real.sqrt (Real.sqrt (6*(T : ℝ)/n))

theorem amplitude_nonneg (T : ℝ≥0) (n : ℕ) : 0 ≤ amplitude T n := Real.sqrt_nonneg _

theorem amplitude_fourth (T : ℝ≥0) (n : ℕ) : (amplitude T n)^4 = 6*(T : ℝ)/n := by
  unfold amplitude
  calc
    _ = ((Real.sqrt (Real.sqrt (6*(T : ℝ)/n)))^2)^2 := by ring
    _ = (Real.sqrt (6*(T : ℝ)/n))^2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
    _ = _ := Real.sq_sqrt (by positivity)

theorem amplitude_tendsto (T : ℝ≥0) : Tendsto (amplitude T) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => Real.sqrt (Real.sqrt (6*(T : ℝ)/n))) atTop (𝓝 0)
  have h1 : Tendsto (fun n : ℕ => Real.sqrt (6*(T : ℝ)/n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp
        (tendsto_const_div_atTop_nhds_zero_nat (6*(T : ℝ)))
  have he := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h1
  simpa only [Function.comp_def, Real.sqrt_zero] using he

theorem scaled_factor_limit (T : ℝ≥0) (ξ : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ)*(factor (amplitude T n * ξ)-1))
      atTop (𝓝 (-(T : ℝ)*ξ^4)) := by
  have hx : Tendsto (fun n => amplitude T n * ξ) atTop (𝓝 0) := by
    simpa only [zero_mul] using (amplitude_tendsto T).mul_const ξ
  have ho : (fun n => factor (amplitude T n * ξ) - (1-(amplitude T n * ξ)^4/6))
      =o[atTop] (fun n => (amplitude T n * ξ)^4) := fourth_order_remainder.comp_tendsto hx
  have hden : (fun n => (amplitude T n * ξ)^4) =
      (fun n : ℕ => (6*(T : ℝ)*ξ^4) * (1/(n : ℝ))) := by
    funext n
    rw [mul_pow, amplitude_fourth]
    simp only [div_eq_mul_inv, one_mul]
    ring
  rw [hden] at ho
  have hs := ho.trans_isBigO
    (isBigO_const_mul_self (6*(T : ℝ)*ξ^4) (fun n : ℕ => 1/(n : ℝ)) atTop)
  have herr : Tendsto (fun n : ℕ => (n : ℝ) *
      (factor (amplitude T n * ξ) - (1-(amplitude T n * ξ)^4/6))) atTop (𝓝 0) := by
    simpa only [one_div, inv_inv, smul_eq_mul] using hs.tendsto_inv_smul_nhds_zero
  have hevent : (fun n : ℕ => (n : ℝ)*(factor (amplitude T n * ξ)-1)) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ)*(factor (amplitude T n * ξ) - (1-(amplitude T n * ξ)^4/6)) -
        (T : ℝ)*ξ^4) := by
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    have hnr : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [mul_pow, amplitude_fourth]
    field_simp [hnr]
    ring
  have hh := (herr.sub_const ((T : ℝ)*ξ^4)).congr' hevent.symm
  simpa only [zero_sub, neg_mul] using hh

theorem factor_limit (T : ℝ≥0) (ξ : ℝ) :
    Tendsto (fun n => (factor (amplitude T n * ξ))^n) atTop (𝓝 (Real.exp (-(T : ℝ)*ξ^4))) := by
  have hh := Real.tendsto_one_add_pow_exp_of_tendsto (scaled_factor_limit T ξ)
  have hefun : (fun n : ℕ => (1+(factor (amplitude T n * ξ)-1))^n) =
      (fun n => (factor (amplitude T n * ξ))^n) := by
    funext n
    congr 1
    ring
  rw [hefun] at hh
  exact hh

theorem transform_limit (T : ℝ≥0) (ξ : ℝ) :
    Tendsto (fun n => ∫ ω, Complex.exp (Complex.I * (ξ : ℂ) * terminal n (amplitude T n) ω)
      ∂probability n) atTop (𝓝 ((Real.exp (-(T : ℝ)*ξ^4) : ℝ) : ℂ)) := by
  have he := Complex.continuous_ofReal.continuousAt.tendsto.comp (factor_limit T ξ)
  have hh (n : ℕ) : (∫ ω, Complex.exp (Complex.I * (ξ : ℂ) * terminal n (amplitude T n) ω)
      ∂probability n) = (((factor (amplitude T n * ξ))^n : ℝ) : ℂ) := by
    rw [terminal_transform, stepTransform_formula]
    simp only [factor, Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_cos, Complex.ofReal_cosh]
  simpa only [Function.comp_def, ← hh] using he

theorem operator_symbol_limit (T : ℝ≥0) (ξ : ℝ) :
    Tendsto (fun n => ∫ ω, Complex.exp (Complex.I * ((2*Real.pi*ξ : ℝ) : ℂ) *
      terminal n (amplitude T n) ω) ∂probability n) atTop (𝓝 (HigherHeatL2.symbol 2 T ξ)) := by
  simpa only [HigherHeatL2.symbol, show 2*2=4 from rfl] using transform_limit T (2*Real.pi*ξ)

end OperatorDerivativeRewrite.Foundation.ComplexRootHeatTransformLimit
