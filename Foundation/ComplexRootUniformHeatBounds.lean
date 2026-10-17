import Foundation.ComplexRootPoissonHeatLimit
import Foundation.ComplexRootNormTransform

/-! Uniform compact-frequency bounds for the actual fourth-order process transforms. -/
noncomputable section
open Filter Set Asymptotics
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.ComplexRootUniformHeatBounds
open ComplexRootHeatTransformLimit ComplexRootTransformConsistency

theorem near_contraction : ∀ᶠ x : ℝ in 𝓝 0, factor x ≤ 1 := by
  have hr := fourth_order_remainder.bound (by norm_num : 0 < (1/12 : ℝ))
  filter_upwards [hr] with x hx
  have hx4 : 0 ≤ x^4 := by positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg hx4] at hx
  have he := (le_abs_self (factor x-(1-x^4/6))).trans hx
  nlinarith

theorem uniform_factor_bound (S : ℝ≥0) :
    ∀ᶠ n : ℕ in atTop, ∀ ξ : ℝ, |ξ| ≤ (S : ℝ) → factor (amplitude 1 n*ξ) ≤ 1 := by
  obtain ⟨δ,hδ,hbound⟩ := Metric.eventually_nhds_iff.mp near_contraction
  have ht : Tendsto (fun n => |amplitude 1 n*(S : ℝ)|) atTop (𝓝 0) := by
    simpa only [zero_mul, abs_zero] using ((amplitude_tendsto 1).mul_const (S : ℝ)).abs
  filter_upwards [ht.eventually (Iio_mem_nhds hδ)] with n hn
  intro ξ hξ
  apply hbound
  rw [Real.dist_eq, sub_zero]
  calc
    |amplitude 1 n*ξ| = amplitude 1 n*|ξ| := by
      rw [abs_mul, abs_of_nonneg (amplitude_nonneg 1 n)]
    _ ≤ amplitude 1 n*(S : ℝ) := mul_le_mul_of_nonneg_left hξ (amplitude_nonneg 1 n)
    _ = |amplitude 1 n*(S : ℝ)| :=
      (abs_of_nonneg (mul_nonneg (amplitude_nonneg 1 n) S.coe_nonneg)).symm
    _ < δ := hn

theorem exponential_real (t : ℝ≥0) (a ξ : ℝ) :
    Complex.exp ((t : ℂ)*MarkedHolomorphicExponential.symbol a ξ) =
      (Real.exp ((t : ℝ)*(factor (a*ξ)-1)) : ℂ) := by
  rw [ComplexRootNormTransform.symbol_real, Complex.ofReal_exp]
  congr 1
  unfold factor
  push_cast
  rfl

theorem uniform_transform_norm (T S : ℝ≥0) :
    ∀ᶠ n : ℕ in atTop, ∀ ξ : ℝ, |ξ| ≤ (S : ℝ) →
      ‖Complex.exp ((((n : ℝ≥0)*T : ℝ≥0) : ℂ)*
        MarkedHolomorphicExponential.symbol (amplitude 1 n) ξ)‖ ≤ 1 := by
  filter_upwards [uniform_factor_bound S] with n hn
  intro ξ hξ
  rw [exponential_real, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr (hn ξ hξ))

end OperatorDerivativeRewrite.Foundation.ComplexRootUniformHeatBounds
