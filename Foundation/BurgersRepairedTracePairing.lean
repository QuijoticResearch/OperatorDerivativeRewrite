import Foundation.GaussianPlaneParity
import Foundation.BurgersGaussianPressureResponse

/-! Integrate the actual phase-dependent base pressure against the native
repaired vorticity trace. This is a base-pressure pairing, not induced helical pressure. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Interval Topology
namespace OperatorDerivativeRewrite.Foundation.BurgersRepairedTracePairing
open HelicalVorticityDiagnostics HelicalRadialGaussianBridge HelicalPressureProjection
open HelicalWeightedPressureIBP GaussianPlaneParity BurgersGaussianPressureResponse
set_option backward.isDefEq.respectTransparency false

theorem pressure_even (ν γ z : ℝ) (q : ℝ × ℝ) : P ν γ z (-q) = P ν γ z q := by
  simp [P, StrainedBurgersVortex.pressure, GaussianSwirlVelocity.pressure]

theorem radial_pressure_integrable (ν γ z : ℝ) :
    Integrable (fun q => radial q.1 q.2 * P ν γ z q) physicalGaussian :=
  physical_radial_memLp.integrable_mul (pressure_domain ν γ z).pressure_memLp

theorem actual_radial_pairing (ν γ z : ℝ) :
    (∫ q, radial q.1 q.2 * P ν γ z q ∂physicalGaussian) =
      physicalResponse (pressureClass ν γ z) :=
  (radial_laplacian_integral (pressure_domain ν γ z)).trans
    (pressure_response (pressure_domain ν γ z)).symm

def integrand (ε ν γ : ℝ) (q : ℝ × ℝ) (θ : ℝ) : ℝ :=
  P ν γ θ q * Matrix.trace (correctedJacobian ε q.1 q.2 θ * correctedJacobian ε q.1 q.2 θ)

theorem integrand_expansion (ε ν γ θ : ℝ) : (fun q => integrand ε ν γ q θ) =
    fun q => ε*(P ν γ θ q*linearTrace q.1 q.2 θ) +
      (4*ε^2)*((profile q.1 q.2)^2*(radial q.1 q.2*P ν γ θ q)) := by
  funext q
  rw [integrand, corrected_trace]
  ring

theorem integrand_integrable (ε ν γ θ : ℝ) :
    Integrable (fun q => integrand ε ν γ q θ) (volume.prod volume) := by
  rw [integrand_expansion]
  exact ((weighted_linearTrace_integrable (pressure_domain ν γ θ).pressure_memLp θ).const_mul ε).add
    ((weighted_integrable (radial_pressure_integrable ν γ θ)).const_mul (4*ε^2))

def crossSection (ε ν γ θ : ℝ) : ℝ := ∫ q, integrand ε ν γ q θ ∂volume.prod volume

theorem crossSection_exact (ε ν γ θ : ℝ) : crossSection ε ν γ θ =
    (Real.pi/2)*ε^2*(γ^2*Real.log (9/8 : ℝ)-4*ν^2) := by
  rw [crossSection, integrand_expansion,
    integral_add
      ((weighted_linearTrace_integrable (pressure_domain ν γ θ).pressure_memLp θ).const_mul ε)
      ((weighted_integrable (radial_pressure_integrable ν γ θ)).const_mul (4*ε^2)),
    integral_const_mul,
    weighted_linearTrace_zero (pressure_domain ν γ θ).pressure_memLp (pressure_even ν γ θ),
    mul_zero, zero_add, integral_const_mul,
    weighted_integral _ (radial_pressure_integrable ν γ θ),
    actual_radial_pairing, response_exact]
  ring

theorem crossSection_intervalIntegrable (ε ν γ a b : ℝ) :
    IntervalIntegrable (crossSection ε ν γ) volume a b := by
  have he : crossSection ε ν γ =
      fun _ => (Real.pi/2)*ε^2*(γ^2*Real.log (9/8 : ℝ)-4*ν^2) :=
    funext (crossSection_exact ε ν γ)
  rw [he]
  exact intervalIntegrable_const

theorem axial_integral_exact (ε ν γ a b : ℝ) :
    (∫ θ in a..b, crossSection ε ν γ θ) =
      (b-a)*(Real.pi/2)*ε^2*(γ^2*Real.log (9/8 : ℝ)-4*ν^2) := by
  simp_rw [crossSection_exact]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem period_integral_exact (ε ν γ : ℝ) :
    (∫ θ in (0 : ℝ)..(2*Real.pi), crossSection ε ν γ θ) =
      Real.pi^2*ε^2*(γ^2*Real.log (9/8 : ℝ)-4*ν^2) := by
  rw [axial_integral_exact]
  ring

end OperatorDerivativeRewrite.Foundation.BurgersRepairedTracePairing
