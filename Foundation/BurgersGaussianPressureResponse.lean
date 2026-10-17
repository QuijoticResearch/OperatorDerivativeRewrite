import Foundation.PressureDomainLinearCalculus
import Foundation.GaussianSwirlLaplace
import Foundation.BurgersAxialPressureFlux

/-! Exact radial Gaussian observation of the actual strained Burgers pressure.
This scalar cross-section observation is distinct from the full Hessian contraction. -/
noncomputable section
open MeasureTheory Set Filter
namespace OperatorDerivativeRewrite.Foundation.BurgersGaussianPressureResponse
open HelicalRadialGaussianBridge HelicalPressureProjection HelicalWeightedPressureIBP
open PressureDomainLinearCalculus
set_option backward.isDefEq.respectTransparency false

def P (ν γ z : ℝ) (q : ℝ × ℝ) : ℝ := StrainedBurgersVortex.pressure ν γ q.1 q.2 z
def Dx (ν γ : ℝ) (q : ℝ × ℝ) : ℝ := γ^2*GaussianSwirlPressureDomain.Dx q-4*ν^2*q.1
def Dy (ν γ : ℝ) (q : ℝ × ℝ) : ℝ := γ^2*GaussianSwirlPressureDomain.Dy q-4*ν^2*q.2
def Dxx (ν γ : ℝ) (q : ℝ × ℝ) : ℝ := γ^2*GaussianSwirlPressureDomain.Dxx q-4*ν^2
def Dyy (ν γ : ℝ) (q : ℝ × ℝ) : ℝ := γ^2*GaussianSwirlPressureDomain.Dyy q-4*ν^2

theorem pressure_domain (ν γ z : ℝ) : PressureDomain (P ν γ z)
    (Dx ν γ) (Dy ν γ) (Dxx ν γ) (Dyy ν γ) := by
  have h := linearCombination 1 (-8*ν^2*z^2)
    (linearCombination (γ^2) (-2*ν^2) GaussianSwirlPressureDomain.pressure_domain radius_domain)
    (constant_domain 1)
  convert h using 1 <;> (try funext q) <;>
    dsimp [P, Dx, Dy, Dxx, Dyy, StrainedBurgersVortex.pressure,
      GaussianSwirlPressureDomain.P, GaussianSwirlPressureDomain.radiusSq] <;> ring

def pressureClass (ν γ z : ℝ) : PhysicalL2 := pressureL2 (pressure_domain ν γ z)

theorem class_representation (ν γ z : ℝ) : pressureClass ν γ z =
    (γ^2) • pressureL2 GaussianSwirlPressureDomain.pressure_domain +
      (-2*ν^2) • pressureL2 radius_domain +
        (-8*ν^2*z^2) • pressureL2 (constant_domain 1) := by
  apply Lp.ext
  filter_upwards [pressureL2_ae (pressure_domain ν γ z),
    Lp.coeFn_add ((γ^2) • pressureL2 GaussianSwirlPressureDomain.pressure_domain +
      (-2*ν^2) • pressureL2 radius_domain) ((-8*ν^2*z^2) • pressureL2 (constant_domain 1)),
    Lp.coeFn_add ((γ^2) • pressureL2 GaussianSwirlPressureDomain.pressure_domain)
      ((-2*ν^2) • pressureL2 radius_domain),
    Lp.coeFn_smul (γ^2) (pressureL2 GaussianSwirlPressureDomain.pressure_domain),
    Lp.coeFn_smul (-2*ν^2) (pressureL2 radius_domain),
    Lp.coeFn_smul (-8*ν^2*z^2) (pressureL2 (constant_domain 1)),
    pressureL2_ae GaussianSwirlPressureDomain.pressure_domain,
    pressureL2_ae radius_domain, pressureL2_ae (constant_domain 1)]
    with q hc ha hb hs ht hu hp hr h1
  change pressureL2 (pressure_domain ν γ z) q = _
  rw [hc, ha]
  simp only [Pi.add_apply, hb, hs, ht, hu, Pi.smul_apply, smul_eq_mul, hp, hr, h1]
  dsimp [P, StrainedBurgersVortex.pressure, GaussianSwirlPressureDomain.P,
    GaussianSwirlPressureDomain.radiusSq]
  ring

theorem response_exact (ν γ z : ℝ) : physicalResponse (pressureClass ν γ z) =
    γ^2*Real.log (9/8 : ℝ)/4-ν^2 := by
  rw [class_representation]
  simp only [physicalResponse, inner_add_right, inner_smul_right]
  change γ^2*physicalResponse (pressureL2 GaussianSwirlPressureDomain.pressure_domain) +
    (-2*ν^2)*physicalResponse (pressureL2 radius_domain) +
      (-8*ν^2*z^2)*physicalResponse (pressureL2 (constant_domain 1)) = _
  rw [GaussianSwirlLaplace.swirl_response_exact, radius_response, constant_response]
  ring

theorem response_axial_independent (ν γ z w : ℝ) :
    physicalResponse (pressureClass ν γ z) = physicalResponse (pressureClass ν γ w) := by
  rw [response_exact, response_exact]

theorem negative_iff (ν γ z : ℝ) : physicalResponse (pressureClass ν γ z) < 0 ↔
    γ^2*Real.log (9/8 : ℝ)/4 < ν^2 := by rw [response_exact, sub_neg]

theorem positive_iff (ν γ z : ℝ) : 0 < physicalResponse (pressureClass ν γ z) ↔
    ν^2 < γ^2*Real.log (9/8 : ℝ)/4 := by rw [response_exact, sub_pos]

theorem zero_iff (ν γ z : ℝ) : physicalResponse (pressureClass ν γ z) = 0 ↔
    γ^2*Real.log (9/8 : ℝ)/4 = ν^2 := by rw [response_exact, sub_eq_zero]

def neutralViscosity : ℝ := Real.sqrt (Real.log (9/8 : ℝ)/4)

theorem neutralViscosity_pos : 0 < neutralViscosity :=
  Real.sqrt_pos.mpr (div_pos (Real.log_pos (by norm_num)) (by norm_num))

theorem neutralViscosity_square : neutralViscosity^2 = Real.log (9/8 : ℝ)/4 :=
  Real.sq_sqrt (le_of_lt (div_pos (Real.log_pos (by norm_num)) (by norm_num)))

theorem neutral_response (z : ℝ) : physicalResponse (pressureClass neutralViscosity 1 z) = 0 := by
  rw [response_exact, neutralViscosity_square]
  norm_num

theorem neutral_actual_contraction_neg (x y z : ℝ) :
    BurgersAxialPressureFlux.contraction neutralViscosity 1 x y z < 0 :=
  BurgersAxialPressureFlux.contraction_neg _ _ _ _ _ (ne_of_gt neutralViscosity_pos) (by norm_num)

theorem smaller_viscosity_positive (z : ℝ) :
    0 < physicalResponse (pressureClass (neutralViscosity/2) 1 z) := by
  rw [response_exact]
  simp only [one_pow, one_mul, div_pow, neutralViscosity_square]
  have hp : 0 < Real.log (9/8 : ℝ) := Real.log_pos (by norm_num)
  nlinarith

theorem positive_response_negative_contraction (x y z : ℝ) :
    0 < neutralViscosity/2 ∧
      0 < physicalResponse (pressureClass (neutralViscosity/2) 1 z) ∧
        BurgersAxialPressureFlux.contraction (neutralViscosity/2) 1 x y z < 0 := by
  have hp : 0 < neutralViscosity/2 := div_pos neutralViscosity_pos (by norm_num)
  exact ⟨hp, smaller_viscosity_positive z,
    BurgersAxialPressureFlux.contraction_neg _ _ _ _ _ (ne_of_gt hp) (by norm_num)⟩

theorem unit_viscosity_negative (z : ℝ) : physicalResponse (pressureClass 1 1 z) < 0 := by
  rw [response_exact]
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 9/8 by norm_num)
  norm_num at *
  linarith

theorem leadingPressure_exact (ε ν γ z : ℝ) : leadingPressure ε (pressureClass ν γ z) =
    Real.pi^2*ε^2*(γ^2*Real.log (9/8 : ℝ)-4*ν^2) := by
  rw [leadingPressure_formula, response_exact]
  ring

end OperatorDerivativeRewrite.Foundation.BurgersGaussianPressureResponse
