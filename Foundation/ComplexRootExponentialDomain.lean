import Foundation.ComplexRootPoissonPolynomialDomain
import Foundation.ComplexRootTiltedLaw

/-! A genuine measurable exponential-growth domain for the actual complex stochastic laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.ComplexRootExponentialDomain

def radial (B : ℝ) (z : ℂ) : ℂ := (Real.exp (B*‖z‖) : ℂ)

theorem radial_walk_bound (a B : ℝ) (hB : 0 ≤ B) (n : ℕ)
    (ω : ComplexFourthRootWalk.Sample n) :
    ‖radial B (ComplexFourthRootWalk.terminal n a ω)‖ ≤ (Real.exp (B*(2*|a|)))^n := by
  simp only [radial, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ B*((n : ℝ)*(2*|a|)) := mul_le_mul_of_nonneg_left
      (ComplexRootPoissonPolynomialDomain.terminal_norm_bound n a ω) hB
    _ = _ := by ring

theorem radial_integrable (r : ℝ≥0) (a B : ℝ) (hB : 0 ≤ B) :
    Integrable (radial B) (ComplexRootPoissonLaw.law r a) :=
  ComplexRootPoissonGrowth.growth_integrable r a _ (by unfold radial; fun_prop)
    (Real.exp (B*(2*|a|))) (radial_walk_bound a B hB)

theorem radial_real_integrable (r : ℝ≥0) (a B : ℝ) (hB : 0 ≤ B) :
    Integrable (fun z : ℂ => Real.exp (B*‖z‖)) (ComplexRootPoissonLaw.law r a) := by
  have hi := (radial_integrable r a B hB).re
  simpa only [radial, RCLike.re_eq_complex_re, Complex.ofReal_re] using hi

theorem integrable_of_exp_bound (r : ℝ≥0) (a : ℝ) (F : ℂ → ℂ) (hF : Measurable F)
    (A B : ℝ) (hB : 0 ≤ B) (hbound : ∀ z, ‖F z‖ ≤ A * Real.exp (B * ‖z‖)) :
    Integrable F (ComplexRootPoissonLaw.law r a) :=
  ((radial_real_integrable r a B hB).const_mul A).mono' hF.aestronglyMeasurable
    (Eventually.of_forall hbound)

theorem process_integrable (t : ℝ≥0) (a : ℝ) (F : ℂ → ℂ) (hF : Measurable F)
    (A B : ℝ) (hB : 0 ≤ B) (hbound : ∀ z, ‖F z‖ ≤ A * Real.exp (B * ‖z‖)) :
    Integrable (fun ω : MarkedRootRenewalProcess.StateSample =>
      F (MarkedRenewalMartingale.process a t ω)) MarkedRootRenewalProcess.probability := by
  have hi : Integrable F (MarkedRootRenewalProcess.probability.map
      (MarkedRenewalMartingale.process a t)) := by
    rw [MarkedRenewalMartingale.process_law]
    exact integrable_of_exp_bound t a F hF A B hB hbound
  exact (integrable_map_measure hF.aestronglyMeasurable
    (MarkedRenewalMartingale.process_measurable a t).aemeasurable).mp hi

theorem phase_norm_bound (ξ : ℝ) (z : ℂ) :
    ‖Complex.exp (Complex.I*(ξ : ℂ)*z)‖ ≤ Real.exp (|ξ| * ‖z‖) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ‖Complex.I*(ξ : ℂ)*z‖ := Complex.re_le_norm _
    _ = _ := by simp [Real.norm_eq_abs]

theorem tilted_integrable (r : ℝ≥0) (a ξ : ℝ) (F : ℂ → ℂ) (hF : Measurable F)
    (A B : ℝ) (hB : 0 ≤ B) (hbound : ∀ z, ‖F z‖ ≤ A * Real.exp (B * ‖z‖)) :
    (ComplexRootTiltedLaw.law a ξ r).Integrable F := by
  have hA : 0 ≤ A := (norm_nonneg (F 0)).trans (by simpa using hbound 0)
  let C := ‖Complex.exp (-(r : ℂ)*MarkedHolomorphicExponential.symbol a ξ)‖
  have hρ (z : ℂ) : ‖ComplexRootTiltedLaw.density a ξ r z‖ ≤ C*Real.exp (|ξ| * ‖z‖) := by
    rw [ComplexRootTiltedLaw.density, norm_mul]
    exact mul_le_mul_of_nonneg_left (phase_norm_bound ξ z) (norm_nonneg _)
  have hi : Integrable (fun z => F z*ComplexRootTiltedLaw.density a ξ r z)
      (ComplexRootPoissonLaw.law r a) := by
    apply integrable_of_exp_bound r a _ (hF.mul (ComplexRootTiltedLaw.density_measurable a ξ r))
      (A*C) (B+|ξ|) (by positivity)
    intro z
    change ‖F z*ComplexRootTiltedLaw.density a ξ r z‖ ≤ (A*C)*Real.exp ((B+|ξ|)*‖z‖)
    rw [norm_mul]
    calc
      _ ≤ (A*Real.exp (B*‖z‖))*(C*Real.exp (|ξ| * ‖z‖)) :=
        mul_le_mul (hbound z) (hρ z) (norm_nonneg _)
          (mul_nonneg hA (Real.exp_nonneg _))
      _ = _ := by rw [add_mul, Real.exp_add]; ring
  exact ComplexDensityUnbounded.integrable_density _ _
    (ComplexRootTiltedLaw.density_integrable a ξ r) F hF hi

end OperatorDerivativeRewrite.Foundation.ComplexRootExponentialDomain
