import Foundation.ComplexDensityPushforward
import Foundation.MarkedExponentialTilt

/-! Actual tilted compound-root coordinate laws, identified by all measurable sets. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.ComplexRootTiltedLaw
open MarkedRootRenewalProcess (StateSample probability)
open MarkedRenewalMartingale MarkedHolomorphicExponential MarkedExponentialMartingale

def density (a ξ : ℝ) (t : ℝ≥0) (z : ℂ) : ℂ :=
  Complex.exp (-(t : ℂ)*symbol a ξ) * Complex.exp (Complex.I*(ξ : ℂ)*z)

def law (a ξ : ℝ) (t : ℝ≥0) : VectorMeasure ℂ ℂ :=
  (ComplexRootPoissonLaw.law t a).withDensityᵥ (density a ξ t)

theorem density_measurable (a ξ : ℝ) (t : ℝ≥0) : Measurable (density a ξ t) := by
  unfold density
  fun_prop

theorem density_integrable (a ξ : ℝ) (t : ℝ≥0) :
    Integrable (density a ξ t) (ComplexRootPoissonLaw.law t a) :=
  (ComplexRootPoissonTransform.exponential_integrable t a ξ).const_mul _

theorem law_mass (a ξ : ℝ) (t : ℝ≥0) : law a ξ t univ = 1 := by
  rw [law, withDensityᵥ_apply (density_integrable a ξ t) MeasurableSet.univ,
    Measure.restrict_univ]
  change (∫ z, Complex.exp (-(t : ℂ)*symbol a ξ) *
    Complex.exp (Complex.I*(ξ : ℂ)*z) ∂ComplexRootPoissonLaw.law t a) = 1
  rw [integral_const_mul, ComplexRootPoissonTransform.transform, ← Complex.exp_add]
  simp [symbol]

theorem law_finite_variation (a ξ : ℝ) (t : ℝ≥0) :
    IsFiniteMeasure (law a ξ t).variation :=
  ComplexDensityIntegral.finite_variation _ _ (density_integrable a ξ t)

theorem own_horizon_coordinate (a ξ : ℝ) (t : ℝ≥0) :
    (MarkedExponentialTilt.source a ξ (fun _ => t)).map (process a t) = law a ξ t := by
  have hi : Integrable (density a ξ t) (probability.map (process a t)) := by
    rw [process_law]
    exact density_integrable a ξ t
  have hm := ComplexDensityPushforward.map_density probability (process a t)
    (process_measurable a t) (density a ξ t) (density_measurable a ξ t) hi
  rw [process_law] at hm
  exact hm

theorem later_horizon_coordinate (a ξ : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    (MarkedExponentialTilt.source a ξ (fun _ => t)).map (process a s) = law a ξ s := by
  rw [← own_horizon_coordinate a ξ s]
  apply VectorMeasure.ext
  intro A hA
  rw [VectorMeasure.map_apply _ (process_measurable a s) hA,
    VectorMeasure.map_apply _ (process_measurable a s) hA,
    MarkedExponentialTilt.source, MarkedExponentialTilt.source,
    withDensityᵥ_apply (normalized_integrable a ξ t) ((process_measurable a s) hA),
    withDensityᵥ_apply (normalized_integrable a ξ s) ((process_measurable a s) hA)]
  have hpre : MeasurableSet[history a s] ((process a s) ⁻¹' A) :=
    (process_adapted a s).measurable hA
  calc
    _ = ∫ ω in (process a s) ⁻¹' A,
        probability[normalized a ξ t | history a s] ω ∂probability :=
      (setIntegral_condExp ((history a).le s) (normalized_integrable a ξ t) hpre).symm
    _ = _ := integral_congr_ae (ae_restrict_of_ae (normalized_condExp a ξ s t hst))

end OperatorDerivativeRewrite.Foundation.ComplexRootTiltedLaw
