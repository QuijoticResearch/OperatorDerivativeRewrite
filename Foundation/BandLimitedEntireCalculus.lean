import Foundation.BandLimitedComplexExtension
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Complex differentiation on the genuinely integrable compact-frequency test domain. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BandLimitedEntireCalculus
open BandLimitedComplexExtension

def derivativeProfile (φ : ℝ → ℂ) (ξ : ℝ) : ℂ := φ ξ*(Complex.I*(ξ : ℂ))

theorem derivativeProfile_integrable (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R)) :
    Integrable (derivativeProfile φ) (band R) := by
  apply hφ.mul_bdd (c := (R : ℝ))
    (by fun_prop : Measurable (fun ξ : ℝ => Complex.I*(ξ : ℂ))).aestronglyMeasurable
  filter_upwards [frequency_bound R] with ξ hξ
  simpa only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul] using hξ

theorem phase_derivative (φ : ℝ → ℂ) (ξ : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => φ ξ*Complex.exp (Complex.I*(ξ : ℂ)*w))
      (derivativeProfile φ ξ*Complex.exp (Complex.I*(ξ : ℂ)*z)) z := by
  have he := (((hasDerivAt_id z).const_mul (Complex.I*(ξ : ℂ))).cexp).const_mul (φ ξ)
  convert he using 1 <;> simp [derivativeProfile, mul_comm, mul_left_comm, mul_assoc]

theorem extension_hasDerivAt (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R)) (z₀ : ℂ) :
    HasDerivAt (extension R φ) (extension R (derivativeProfile φ) z₀) z₀ := by
  let s : Set ℂ := {z | ‖z‖ ≤ ‖z₀‖+1}
  have hs : s ∈ 𝓝 z₀ := by
    have ht := (continuous_norm : Continuous (fun z : ℂ => ‖z‖)).continuousAt.tendsto (x := z₀)
    exact (ht.eventually (Iio_mem_nhds (by linarith : ‖z₀‖ < ‖z₀‖+1))).mono fun _ h => h.le
  have hφ' := derivativeProfile_integrable R φ hφ
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := band R) (F := fun z ξ => φ ξ*Complex.exp (Complex.I*(ξ : ℂ)*z))
    (F' := fun z ξ => derivativeProfile φ ξ*Complex.exp (Complex.I*(ξ : ℂ)*z)) hs
    (Eventually.of_forall fun z => hφ.aestronglyMeasurable.mul
      (by fun_prop : Measurable
        (fun ξ : ℝ => Complex.exp (Complex.I*(ξ : ℂ)*z))).aestronglyMeasurable)
    (integrand_integrable R φ hφ z₀) (integrand_integrable R _ hφ' z₀).aestronglyMeasurable
    (bound := fun ξ => (R : ℝ)*‖φ ξ‖*Real.exp ((R : ℝ)*(‖z₀‖+1))) ?_
    ((hφ.norm.const_mul (R : ℝ)).mul_const _) ?_).2
  · filter_upwards [frequency_bound R] with ξ hξ
    intro z hz
    have hξn : ‖Complex.I*(ξ : ℂ)‖ ≤ (R : ℝ) := by simpa using hξ
    have hD : ‖derivativeProfile φ ξ‖ ≤ (R : ℝ)*‖φ ξ‖ := by
      rw [derivativeProfile, norm_mul]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hξn (norm_nonneg (φ ξ))
    have hphase := (ComplexRootExponentialDomain.phase_norm_bound ξ z).trans
      (Real.exp_le_exp.mpr (mul_le_mul hξ hz (norm_nonneg _) R.coe_nonneg))
    change ‖derivativeProfile φ ξ*Complex.exp (Complex.I*(ξ : ℂ)*z)‖ ≤
      (R : ℝ)*‖φ ξ‖*Real.exp ((R : ℝ)*(‖z₀‖+1))
    rw [norm_mul]
    exact mul_le_mul hD hphase (norm_nonneg _) (mul_nonneg R.coe_nonneg (norm_nonneg _))
  · exact Eventually.of_forall fun ξ z _ => phase_derivative φ ξ z

theorem extension_differentiable (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R)) :
    Differentiable ℂ (extension R φ) := fun z => (extension_hasDerivAt R φ hφ z).differentiableAt

theorem derivative_formula (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R)) (z : ℂ) :
    deriv (extension R φ) z = extension R (derivativeProfile φ) z :=
  (extension_hasDerivAt R φ hφ z).deriv

def orderProfile (k : ℕ) (φ : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  φ ξ*(Complex.I*(ξ : ℂ))^k

theorem orderProfile_zero (φ : ℝ → ℂ) : orderProfile 0 φ = φ := by
  funext ξ
  simp [orderProfile]

theorem orderProfile_succ (k : ℕ) (φ : ℝ → ℂ) :
    orderProfile (k+1) φ = derivativeProfile (orderProfile k φ) := by
  funext ξ
  simp only [orderProfile, derivativeProfile, pow_succ]
  ring

theorem orderProfile_integrable (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (k : ℕ) : Integrable (orderProfile k φ) (band R) := by
  induction k with
  | zero => simpa only [orderProfile_zero] using hφ
  | succ k ih => rw [orderProfile_succ]; exact derivativeProfile_integrable R _ ih

theorem iterated_derivative_formula (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (k : ℕ) : iteratedDeriv k (extension R φ) = extension R (orderProfile k φ) := by
  induction k with
  | zero => rw [iteratedDeriv_zero, orderProfile_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih, orderProfile_succ]
    funext z
    exact derivative_formula R _ (orderProfile_integrable R φ hφ k) z

theorem fourth_derivative_formula (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R)) :
    iteratedDeriv 4 (extension R φ) = extension R (fun ξ => φ ξ*(ξ : ℂ)^4) := by
  rw [iterated_derivative_formula R φ hφ]
  congr 1
  funext ξ
  simp [orderProfile, mul_pow, Complex.I_pow_four]

end OperatorDerivativeRewrite.Foundation.BandLimitedEntireCalculus
