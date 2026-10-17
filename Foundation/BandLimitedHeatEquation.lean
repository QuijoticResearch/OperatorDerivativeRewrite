import Foundation.BandLimitedEntireCalculus
import Mathlib.Analysis.Complex.RealDeriv

/-! A native classical fourth-order heat equation on the admissible spectral domain. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BandLimitedHeatEquation
open BandLimitedComplexExtension BandLimitedEntireCalculus

def heatProfile (t : ℝ) (φ : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  φ ξ*(Real.exp (-t*ξ^4) : ℂ)

theorem multiplier_bound (R : ℝ≥0) (t ξ : ℝ) (hξ : |ξ| ≤ (R : ℝ)) :
    ‖(Real.exp (-t*ξ^4) : ℂ)‖ ≤ Real.exp (|t| *(R : ℝ)^4) := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hp : ξ^4 ≤ (R : ℝ)^4 := by
    have he : |ξ|^4 = ξ^4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
    simpa only [he] using pow_le_pow_left₀ (abs_nonneg ξ) hξ 4
  exact (mul_le_mul_of_nonneg_right (neg_le_abs t) (by positivity : 0 ≤ ξ^4)).trans
    (mul_le_mul_of_nonneg_left hp (abs_nonneg t))

theorem heatProfile_integrable (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (t : ℝ) : Integrable (heatProfile t φ) (band R) := by
  apply hφ.mul_bdd (c := Real.exp (|t| *(R : ℝ)^4))
    (by fun_prop : Measurable (fun ξ : ℝ => (Real.exp (-t*ξ^4) : ℂ))).aestronglyMeasurable
  filter_upwards [frequency_bound R] with ξ hξ
  exact multiplier_bound R t ξ hξ

def timeProfile (t : ℝ) (φ : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  -(heatProfile t φ ξ*(ξ : ℂ)^4)

theorem timeProfile_integrable (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (t : ℝ) : Integrable (timeProfile t φ) (band R) := by
  have he : timeProfile t φ = -orderProfile 4 (heatProfile t φ) := by
    funext ξ
    simp [timeProfile, orderProfile, mul_pow, Complex.I_pow_four]
  rw [he]
  exact (orderProfile_integrable R _ (heatProfile_integrable R φ hφ t) 4).neg

theorem profile_hasDerivAt (t : ℝ) (φ : ℝ → ℂ) (ξ : ℝ) :
    HasDerivAt (fun s => heatProfile s φ ξ) (timeProfile t φ ξ) t := by
  have he := ((((hasDerivAt_id t).const_mul (-(ξ^4))).exp).ofReal_comp).const_mul (φ ξ)
  convert he using 1 <;>
    simp [heatProfile, timeProfile, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_pow, mul_comm, mul_left_comm]

theorem time_derivative (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (t₀ : ℝ) (z : ℂ) :
    HasDerivAt (fun t : ℝ => extension R (heatProfile t φ) z)
      (extension R (timeProfile t₀ φ) z) t₀ := by
  let s : Set ℝ := {t | |t| ≤ |t₀|+1}
  have hs : s ∈ 𝓝 t₀ := by
    have ht := (continuous_abs : Continuous (fun t : ℝ => |t|)).continuousAt.tendsto (x := t₀)
    exact (ht.eventually (Iio_mem_nhds (by linarith : |t₀| < |t₀|+1))).mono fun _ h => h.le
  have hi := heatProfile_integrable R φ hφ t₀
  have hi' := timeProfile_integrable R φ hφ t₀
  let C := Real.exp ((|t₀|+1)*(R : ℝ)^4)*Real.exp ((R : ℝ)*‖z‖)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := band R) (F := fun t ξ => heatProfile t φ ξ*Complex.exp (Complex.I*(ξ : ℂ)*z))
    (F' := fun t ξ => timeProfile t φ ξ*Complex.exp (Complex.I*(ξ : ℂ)*z)) hs
    (Eventually.of_forall fun t =>
      (integrand_integrable R _ (heatProfile_integrable R φ hφ t) z).aestronglyMeasurable)
    (integrand_integrable R _ hi z) (integrand_integrable R _ hi' z).aestronglyMeasurable
    (bound := fun ξ => ‖φ ξ‖*((R : ℝ)^4*C)) ?_ (hφ.norm.mul_const _) ?_).2
  · filter_upwards [frequency_bound R] with ξ hξ
    intro t ht
    have hp : ‖(ξ : ℂ)^4‖ ≤ (R : ℝ)^4 := by
      simpa only [norm_pow, Complex.norm_real, Real.norm_eq_abs] using
        pow_le_pow_left₀ (abs_nonneg ξ) hξ 4
    have hm := (multiplier_bound R t ξ hξ).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ht (pow_nonneg R.coe_nonneg 4)))
    have hz := (ComplexRootExponentialDomain.phase_norm_bound ξ z).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hξ (norm_nonneg z)))
    change ‖timeProfile t φ ξ*Complex.exp (Complex.I*(ξ : ℂ)*z)‖ ≤ _
    simp only [timeProfile, heatProfile, norm_mul, norm_neg]
    calc
      _ ≤ ‖φ ξ‖*Real.exp ((|t₀|+1)*(R : ℝ)^4)*(R : ℝ)^4*
          Real.exp ((R : ℝ)*‖z‖) :=
        mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hm (norm_nonneg _)) hp
          (norm_nonneg _) (by positivity)) hz (norm_nonneg _) (by positivity)
      _ = _ := by dsimp [C]; ring
  · exact Eventually.of_forall fun ξ t _ => (profile_hasDerivAt t φ ξ).mul_const _

theorem fourth_order_heat_equation (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (t : ℝ) (z : ℂ) :
    HasDerivAt (fun s : ℝ => extension R (heatProfile s φ) z)
      (-(iteratedDeriv 4 (extension R (heatProfile t φ)) z)) t := by
  have he : extension R (timeProfile t φ) z =
      -(iteratedDeriv 4 (extension R (heatProfile t φ)) z) := by
    rw [fourth_derivative_formula R _ (heatProfile_integrable R φ hφ t)]
    simp only [extension, timeProfile, neg_mul, integral_neg]
  rw [← he]
  exact time_derivative R φ hφ t z

end OperatorDerivativeRewrite.Foundation.BandLimitedHeatEquation
