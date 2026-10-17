import Foundation.MarkedHolomorphicExponential

/-! Genuine unbounded exponential martingales carrying the higher-order heat symbol. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.MarkedExponentialMartingale
open MarkedRootRenewalProcess (StateSample probability)
open MarkedRenewalMartingale MarkedHolomorphicExponential

def normalized (a ξ : ℝ) (t : ℝ≥0) (ω : StateSample) : ℂ :=
  Complex.exp (-(t : ℂ)*symbol a ξ)*phase a ξ t ω

theorem normalized_adapted (a ξ : ℝ) : StronglyAdapted (history a) (normalized a ξ) := by
  intro t
  exact stronglyMeasurable_const.mul (phase_adapted a ξ t)

theorem normalized_integrable (a ξ : ℝ) (t : ℝ≥0) :
    Integrable (normalized a ξ t) probability :=
  (phase_integrable a ξ t).const_mul _

theorem normalized_condExp (a ξ : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    probability[normalized a ξ t | history a s] =ᵐ[probability] normalized a ξ s := by
  have he := condExp_smul (μ := probability) (Complex.exp (-(t : ℂ)*symbol a ξ))
    (phase a ξ t) (history a s)
  have hp := phase_condExp a ξ s t hst
  have ht : ((t-s : ℝ≥0) : ℂ) = (t : ℂ)-(s : ℂ) := by
    rw [NNReal.coe_sub hst]
    push_cast
    rfl
  have hh : Complex.exp (-(t : ℂ)*symbol a ξ)*
      Complex.exp (((t-s : ℝ≥0) : ℂ)*symbol a ξ) =
        Complex.exp (-(s : ℂ)*symbol a ξ) := by
    rw [← Complex.exp_add,ht]
    congr 1
    ring
  filter_upwards [he,hp] with ω he hp
  change probability[normalized a ξ t | history a s] ω =
    Complex.exp (-(t : ℂ)*symbol a ξ)*probability[phase a ξ t | history a s] ω at he
  rw [he,hp]
  change _ = Complex.exp (-(s : ℂ)*symbol a ξ)*phase a ξ s ω
  calc
    _ = (Complex.exp (-(t : ℂ)*symbol a ξ)*
        Complex.exp (((t-s : ℝ≥0) : ℂ)*symbol a ξ))*phase a ξ s ω := by ring
    _ = _ := by rw [hh]

theorem normalized_martingale (a ξ : ℝ) :
    Martingale (normalized a ξ) (history a) probability :=
  ⟨normalized_adapted a ξ,fun s t hst => normalized_condExp a ξ s t hst⟩

theorem normalized_mean (a ξ : ℝ) (t : ℝ≥0) :
    (∫ ω, normalized a ξ t ω ∂probability) = 1 := by
  change (∫ ω, Complex.exp (-(t : ℂ)*symbol a ξ)*phase a ξ t ω ∂probability) = _
  rw [integral_const_mul,phase_mean,← Complex.exp_add]
  have he : -(t : ℂ)*symbol a ξ+(t : ℂ)*symbol a ξ = 0 := by ring
  rw [he,Complex.exp_zero]

theorem normalized_zero (a ξ : ℝ) (ω : StateSample) : normalized a ξ 0 ω = 1 := by
  simp [normalized,phase,process,MarkedRootRenewalProcess.process_zero]

end OperatorDerivativeRewrite.Foundation.MarkedExponentialMartingale
