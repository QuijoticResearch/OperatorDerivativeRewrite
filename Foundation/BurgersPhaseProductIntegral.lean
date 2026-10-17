import Foundation.BurgersRepairedTracePairing
import Mathlib.MeasureTheory.Integral.Prod

/-! Absolute integrability and both Fubini orders for the phase-dependent
base-pressure/repaired-trace pairing on a finite axial interval. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Interval Topology
namespace OperatorDerivativeRewrite.Foundation.BurgersPhaseProductIntegral
open HelicalVorticityDiagnostics HelicalRadialGaussianBridge HelicalPressureProjection
open HelicalWeightedPressureIBP GaussianPlaneParity BurgersGaussianPressureResponse
open BurgersRepairedTracePairing
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure physicalGaussian := by unfold physicalGaussian; infer_instance

def phaseMeasure (a b : ℝ) : Measure ℝ := volume.restrict (Ioc a b)

instance phaseMeasure_finite (a b : ℝ) : IsFiniteMeasure (phaseMeasure a b) := by
  constructor
  rw [phaseMeasure, Measure.restrict_apply_univ, Real.volume_Ioc]
  exact ENNReal.ofReal_lt_top

def planeTerm (ν γ : ℝ) (i : Fin 6) (q : ℝ × ℝ) : ℝ :=
  ![(profile q.1 q.2)^2*(q.1*P ν γ 0 q),
    (profile q.1 q.2)^2*(q.2*P ν γ 0 q),
    (profile q.1 q.2)^2*q.1, (profile q.1 q.2)^2*q.2,
    (profile q.1 q.2)^2*(radial q.1 q.2*P ν γ 0 q),
    (profile q.1 q.2)^2*radial q.1 q.2] i

def timeTerm (ε ν : ℝ) (i : Fin 6) (θ : ℝ) : ℝ :=
  ![4*ε*Real.sin θ, -4*ε*Real.cos θ,
    -32*ε*ν^2*θ^2*Real.sin θ, 32*ε*ν^2*θ^2*Real.cos θ,
    4*ε^2, -32*ε^2*ν^2*θ^2] i

theorem planeTerm_integrable (ν γ : ℝ) (i : Fin 6) :
    Integrable (planeTerm ν γ i) (volume.prod volume) := by
  have hP := (pressure_domain ν γ 0).pressure_memLp
  have hx := (x_weights_integrable hP).1
  have hy := (y_weights_integrable hP).1
  have h1 := (PressureDomainLinearCalculus.constant_domain 1).pressure_memLp
  have hcx := (x_weights_integrable h1).1
  have hcy := (y_weights_integrable h1).1
  simp only [mul_one] at hcx hcy
  fin_cases i
  · exact weighted_integrable hx
  · exact weighted_integrable hy
  · exact weighted_integrable hcx
  · exact weighted_integrable hcy
  · exact weighted_integrable (radial_pressure_integrable ν γ 0)
  · exact weighted_integrable (physical_radial_memLp.integrable (by norm_num))

theorem timeTerm_integrable (ε ν a b : ℝ) (hab : a ≤ b) (i : Fin 6) :
    Integrable (timeTerm ε ν i) (phaseMeasure a b) := by
  have hc : Continuous (timeTerm ε ν i) := by
    change Continuous (fun θ => timeTerm ε ν i θ)
    fin_cases i <;> dsimp [timeTerm] <;> fun_prop
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hc.intervalIntegrable a b)

theorem pressure_phase_split (ν γ θ : ℝ) (q : ℝ × ℝ) :
    P ν γ θ q = P ν γ 0 q - 8*ν^2*θ^2 := by
  dsimp [P, StrainedBurgersVortex.pressure]
  ring

theorem integrand_sum (ε ν γ : ℝ) (q : ℝ × ℝ) (θ : ℝ) :
    integrand ε ν γ q θ = ∑ i : Fin 6, planeTerm ν γ i q * timeTerm ε ν i θ := by
  rw [integrand, corrected_trace, pressure_phase_split]
  simp [planeTerm, timeTerm, Fin.sum_univ_succ, linearTrace, phase]
  ring

theorem joint_integrable (ε ν γ a b : ℝ) (hab : a ≤ b) :
    Integrable (fun z : (ℝ × ℝ) × ℝ => integrand ε ν γ z.1 z.2)
      ((volume.prod volume).prod (phaseMeasure a b)) := by
  have hs : Integrable
      (fun z : (ℝ × ℝ) × ℝ => ∑ i : Fin 6, planeTerm ν γ i z.1 * timeTerm ε ν i z.2)
      ((volume.prod volume).prod (phaseMeasure a b)) := by
    apply integrable_finsetSum
    intro i _
    exact (planeTerm_integrable ν γ i).mul_prod (timeTerm_integrable ε ν a b hab i)
  exact hs.congr (Eventually.of_forall fun z => (integrand_sum ε ν γ z.1 z.2).symm)

theorem product_integral_exact (ε ν γ a b : ℝ) (hab : a ≤ b) :
    (∫ z : (ℝ × ℝ) × ℝ, integrand ε ν γ z.1 z.2
      ∂(volume.prod volume).prod (phaseMeasure a b)) =
        (b-a)*(Real.pi/2)*ε^2*(γ^2*Real.log (9/8 : ℝ)-4*ν^2) := by
  rw [integral_prod_symm _ (joint_integrable ε ν γ a b hab)]
  change (∫ θ in Ioc a b, crossSection ε ν γ θ) = _
  rw [← intervalIntegral.integral_of_le hab, axial_integral_exact]

theorem period_product_exact (ε ν γ : ℝ) :
    (∫ z : (ℝ × ℝ) × ℝ, integrand ε ν γ z.1 z.2
      ∂(volume.prod volume).prod (phaseMeasure 0 (2*Real.pi))) =
        Real.pi^2*ε^2*(γ^2*Real.log (9/8 : ℝ)-4*ν^2) := by
  rw [product_integral_exact ε ν γ 0 (2*Real.pi) (by positivity)]
  ring

theorem phase_first_exact (ε ν γ : ℝ) :
    (∫ q : ℝ × ℝ, (∫ θ in (0 : ℝ)..(2*Real.pi), integrand ε ν γ q θ)
      ∂volume.prod volume) = Real.pi^2*ε^2*(γ^2*Real.log (9/8 : ℝ)-4*ν^2) := by
  simp_rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2*Real.pi by positivity)]
  exact (integral_prod _ (joint_integrable ε ν γ 0 (2*Real.pi) (by positivity))).symm.trans
    (period_product_exact ε ν γ)

end OperatorDerivativeRewrite.Foundation.BurgersPhaseProductIntegral
