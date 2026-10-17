import Foundation.BandLimitedProcessExpectation
import Foundation.ComplexRootUniformHeatBounds

/-! Actual stochastic expectations converge on a justified compact-frequency test domain. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BandLimitedHeatLimit
open BandLimitedComplexExtension ComplexRootHeatTransformLimit

def kernel (a κ : ℝ) (t : ℝ≥0) (η : ℝ) : ℂ :=
  Complex.exp ((t : ℂ)*(MarkedHolomorphicExponential.symbol a (η+κ)-
    MarkedHolomorphicExponential.symbol a κ))

theorem exponential_limit (T : ℝ≥0) (ξ : ℝ) :
    Tendsto (fun n : ℕ => Complex.exp ((((n : ℝ≥0)*T : ℝ≥0) : ℂ)*
      MarkedHolomorphicExponential.symbol (amplitude 1 n) ξ)) atTop
      (𝓝 ((Real.exp (-(T : ℝ)*ξ^4) : ℝ) : ℂ)) := by
  simpa only [ComplexRootPoissonTransform.transform, MarkedHolomorphicExponential.symbol] using
    ComplexRootPoissonHeatLimit.rate_scaled_transform_limit T ξ

theorem kernel_ratio (a κ : ℝ) (t : ℝ≥0) (η : ℝ) :
    kernel a κ t η = Complex.exp ((t : ℂ)*MarkedHolomorphicExponential.symbol a (η+κ)) /
      Complex.exp ((t : ℂ)*MarkedHolomorphicExponential.symbol a κ) := by
  rw [kernel, ← Complex.exp_sub]
  congr 1
  ring

theorem kernel_limit (T : ℝ≥0) (κ η : ℝ) :
    Tendsto (fun n : ℕ => kernel (amplitude 1 n) κ ((n : ℝ≥0)*T) η) atTop
      (𝓝 ((Real.exp (-(T : ℝ)*((η+κ)^4-κ^4)) : ℝ) : ℂ)) := by
  have h0 : ((Real.exp (-(T : ℝ)*κ^4) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have he := (exponential_limit T (η+κ)).div (exponential_limit T κ) h0
  have hv : ((Real.exp (-(T : ℝ)*(η+κ)^4) : ℝ) : ℂ) /
      ((Real.exp (-(T : ℝ)*κ^4) : ℝ) : ℂ) =
      ((Real.exp (-(T : ℝ)*((η+κ)^4-κ^4)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_div, ← Real.exp_sub]
    congr 2
    ring
  rw [hv] at he
  change Tendsto (fun n : ℕ =>
    Complex.exp ((((n : ℝ≥0)*T : ℝ≥0) : ℂ)*
      MarkedHolomorphicExponential.symbol (amplitude 1 n) (η+κ)) /
    Complex.exp ((((n : ℝ≥0)*T : ℝ≥0) : ℂ)*
      MarkedHolomorphicExponential.symbol (amplitude 1 n) κ)) atTop _ at he
  simpa only [kernel_ratio] using he

theorem uniform_kernel_bound (T R : ℝ≥0) (κ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ η : ℝ, |η| ≤ (R : ℝ) →
      ‖kernel (amplitude 1 n) κ ((n : ℝ≥0)*T) η‖ ≤ C := by
  let S : ℝ≥0 := R+⟨|κ|,abs_nonneg κ⟩
  let v : ℂ := ((Real.exp (-(T : ℝ)*κ^4) : ℝ) : ℂ)
  let C : ℝ := ‖v⁻¹‖+1
  have h0 : v ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have hi := ((exponential_limit T κ).inv₀ h0).norm
  have hC : ∀ᶠ n : ℕ in atTop, ‖(Complex.exp ((((n : ℝ≥0)*T : ℝ≥0) : ℂ)*
      MarkedHolomorphicExponential.symbol (amplitude 1 n) κ))⁻¹‖ ≤ C :=
    (hi.eventually (Iio_mem_nhds (by dsimp [C]; linarith))).mono fun _ hn => hn.le
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  filter_upwards [ComplexRootUniformHeatBounds.uniform_transform_norm T S,hC] with n hn hc
  intro η hη
  have hS : |η+κ| ≤ (S : ℝ) := by
    change |η+κ| ≤ (R : ℝ)+|κ|
    exact (abs_add_le _ _).trans (add_le_add hη (le_refl |κ|))
  rw [kernel_ratio, div_eq_mul_inv, norm_mul]
  simpa only [one_mul] using mul_le_mul (hn (η+κ) hS) hc (norm_nonneg _) zero_le_one

theorem kernel_measurable (a κ : ℝ) (t : ℝ≥0) : Measurable (kernel a κ t) := by
  unfold kernel
  simp_rw [ComplexRootNormTransform.symbol_real]
  fun_prop

theorem frequency_integral_limit (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (T : ℝ≥0) (κ : ℝ) :
    Tendsto (fun n : ℕ => ∫ η, φ η*kernel (amplitude 1 n) κ ((n : ℝ≥0)*T) η ∂band R)
      atTop (𝓝 (∫ η, φ η*(Real.exp (-(T : ℝ)*((η+κ)^4-κ^4)) : ℂ) ∂band R)) := by
  obtain ⟨C,hC,hbound⟩ := uniform_kernel_bound T R κ
  refine tendsto_integral_filter_of_dominated_convergence (fun η => ‖φ η‖*C) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun n => hφ.aestronglyMeasurable.mul
      (kernel_measurable (amplitude 1 n) κ ((n : ℝ≥0)*T)).aestronglyMeasurable
  · filter_upwards [hbound] with n hn
    filter_upwards [frequency_bound R] with η hη
    change ‖φ η*kernel (amplitude 1 n) κ ((n : ℝ≥0)*T) η‖ ≤ ‖φ η‖*C
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hn η hη) (norm_nonneg _)
  · exact hφ.norm.mul_const C
  · exact Eventually.of_forall fun η => (kernel_limit T κ η).const_mul (φ η)

theorem tilted_expectation_limit (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (T : ℝ≥0) (κ : ℝ) :
    Tendsto (fun n : ℕ => ∫ᵛ z, extension R φ z ∂[ContinuousLinearMap.mul ℝ ℂ;
      ComplexRootTiltedLaw.law (amplitude 1 n) κ ((n : ℝ≥0)*T)]) atTop
      (𝓝 (∫ η, φ η*(Real.exp (-(T : ℝ)*((η+κ)^4-κ^4)) : ℂ) ∂band R)) := by
  simpa only [BandLimitedProcessExpectation.tilted_mean R φ hφ, kernel] using
    frequency_integral_limit R φ hφ T κ

theorem symbol_zero (a : ℝ) : MarkedHolomorphicExponential.symbol a 0 = 0 := by
  simp [MarkedHolomorphicExponential.symbol, ComplexFourthRootWalk.stepTransform]

theorem process_expectation_limit (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (T : ℝ≥0) :
    Tendsto (fun n : ℕ => ∫ ω, extension R φ
      (MarkedRenewalMartingale.process (amplitude 1 n) ((n : ℝ≥0)*T) ω)
        ∂MarkedRootRenewalProcess.probability) atTop
      (𝓝 (∫ η, φ η*(Real.exp (-(T : ℝ)*η^4) : ℂ) ∂band R)) := by
  simpa only [BandLimitedProcessExpectation.process_mean R φ hφ, kernel, symbol_zero,
    add_zero, sub_zero, zero_pow (by norm_num : (4 : ℕ) ≠ 0)] using
    frequency_integral_limit R φ hφ T 0

theorem starting_argument (R : ℝ≥0) (φ : ℝ → ℂ) (z w : ℂ) :
    extension R φ (z+w) = extension R (fun η => φ η*Complex.exp (Complex.I*(η : ℂ)*z)) w := by
  unfold extension
  apply integral_congr_ae
  filter_upwards with η
  rw [mul_add, Complex.exp_add]
  ring

theorem starting_state_limit (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (T : ℝ≥0) (z : ℂ) :
    Tendsto (fun n : ℕ => ∫ ω, extension R φ
      (z+MarkedRenewalMartingale.process (amplitude 1 n) ((n : ℝ≥0)*T) ω)
        ∂MarkedRootRenewalProcess.probability) atTop
      (𝓝 (∫ η, (φ η*Complex.exp (Complex.I*(η : ℂ)*z))*
        (Real.exp (-(T : ℝ)*η^4) : ℂ) ∂band R)) := by
  simpa only [starting_argument] using process_expectation_limit R
    (fun η => φ η*Complex.exp (Complex.I*(η : ℂ)*z)) (integrand_integrable R φ hφ z) T

theorem operator_symbol (T : ℝ≥0) (η : ℝ) :
    (Real.exp (-(T : ℝ)*η^4) : ℂ) = HigherHeatL2.symbol 2 T (η/(2*Real.pi)) := by
  have hp : 2*Real.pi ≠ (0 : ℝ) := by positivity
  have he : 2*Real.pi*(η/(2*Real.pi)) = η := by field_simp
  simp only [HigherHeatL2.symbol, show 2*2=4 from rfl, he]

theorem operator_expectation_limit (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (T : ℝ≥0) :
    Tendsto (fun n : ℕ => ∫ ω, extension R φ
      (MarkedRenewalMartingale.process (amplitude 1 n) ((n : ℝ≥0)*T) ω)
        ∂MarkedRootRenewalProcess.probability) atTop
      (𝓝 (∫ η, φ η*HigherHeatL2.symbol 2 T (η/(2*Real.pi)) ∂band R)) := by
  simpa only [← operator_symbol] using process_expectation_limit R φ hφ T

end OperatorDerivativeRewrite.Foundation.BandLimitedHeatLimit
