import Foundation.CauchyPoissonCoreInvariant
/-! The actual Cauchy generator plus sine drift is not Hermitian under its
Poisson-kernel core-balance law when q is nonzero. The two positive-frequency
modes give exact cross-pairings 0 and -2q. This obstructs a symmetric realization
through this core, not a nonreversible invariant semigroup or entropy theorem. -/
noncomputable section
open MeasureTheory Complex
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonNonSymmetry
open OperatorDerivativeRewrite.Foundation
open CauchyPoissonCoreInvariant

theorem circle_star_mul (θ : ℝ) :
    starRingEnd ℂ (circleMap (0:ℂ) 1 θ) * circleMap (0:ℂ) 1 θ = 1 := by
  rw [Complex.conj_mul']
  simp

theorem forward_point (r θ : ℝ) :
    starRingEnd ℂ (circleMap (0:ℂ) 1 θ) *
      (-2*(circleMap (0:ℂ) 1 θ)^2 + (r:ℂ)*
        (circleMap (0:ℂ) 1 θ-(circleMap (0:ℂ) 1 θ)^3)) =
      -2*circleMap (0:ℂ) 1 θ+(r:ℂ)*(1-(circleMap (0:ℂ) 1 θ)^2) := by
  have hz := circle_star_mul θ
  calc
    _ = (-2*circleMap (0:ℂ) 1 θ+(r:ℂ)*(1-(circleMap (0:ℂ) 1 θ)^2))*
      (starRingEnd ℂ (circleMap (0:ℂ) 1 θ)*circleMap (0:ℂ) 1 θ) := by ring
    _ = _ := by rw [hz,mul_one]

theorem backward_point (r θ : ℝ) :
    starRingEnd ℂ (-circleMap (0:ℂ) 1 θ + (r:ℂ)/2*(1-(circleMap (0:ℂ) 1 θ)^2)) *
      (circleMap (0:ℂ) 1 θ)^2 =
      -circleMap (0:ℂ) 1 θ + (r:ℂ)/2*((circleMap (0:ℂ) 1 θ)^2-1) := by
  simp only [map_add,map_neg,map_mul,map_div₀,map_ofNat,map_sub,map_one,map_pow,
    Complex.conj_ofReal]
  have hz := circle_star_mul θ
  calc
    _ = -(starRingEnd ℂ (circleMap (0:ℂ) 1 θ)*circleMap (0:ℂ) 1 θ)*circleMap (0:ℂ) 1 θ +
      (r:ℂ)/2*((circleMap (0:ℂ) 1 θ)^2-
        (starRingEnd ℂ (circleMap (0:ℂ) 1 θ)*circleMap (0:ℂ) 1 θ)^2) := by ring
    _ = _ := by rw [hz]; ring

theorem forward_integral (q : ℝ) (hq : |q| < 1) :
    (∫ θ, starRingEnd ℂ (circleMap (0:ℂ) 1 θ) *
      (-2*(circleMap (0:ℂ) 1 θ)^2 + ((2*q/(1-q^2):ℝ):ℂ)*
        (circleMap (0:ℂ) 1 θ-(circleMap (0:ℂ) 1 θ)^3)) ∂law q) = 0 := by
  have h0 : Integrable (fun _ : ℝ => (1:ℂ)) (law q) := by
    simpa only [pow_zero] using law_mode_integrable q hq 0
  have h1 : Integrable (fun θ => circleMap (0:ℂ) 1 θ) (law q) := by
    simpa only [pow_one] using law_mode_integrable q hq 1
  have h2 := law_mode_integrable q hq 2
  have hm0 : (∫ _ : ℝ, (1:ℂ) ∂law q) = 1 := by
    simpa only [pow_zero] using law_moment_nat q hq 0
  have hm1 : (∫ θ, circleMap (0:ℂ) 1 θ ∂law q) = (q:ℂ) := by
    simpa only [pow_one] using law_moment_nat q hq 1
  simp_rw [forward_point]
  have ha : Integrable (fun θ => -2*circleMap (0:ℂ) 1 θ) (law q) := h1.const_mul (-2:ℂ)
  have hb : Integrable (fun θ => ((2*q/(1-q^2):ℝ):ℂ)*(1-(circleMap (0:ℂ) 1 θ)^2)) (law q) :=
    (h0.sub h2).const_mul _
  rw [integral_add ha hb, integral_const_mul,
    integral_const_mul, integral_sub h0 h2, hm0,hm1,law_moment_nat q hq 2]
  have hs := stationary_positive_mode q hq 0
  norm_num at hs
  push_cast
  linear_combination 2*hs

theorem backward_integral (q : ℝ) (hq : |q| < 1) :
    (∫ θ, starRingEnd ℂ (-circleMap (0:ℂ) 1 θ +
      ((2*q/(1-q^2):ℝ):ℂ)/2*(1-(circleMap (0:ℂ) 1 θ)^2)) *
      (circleMap (0:ℂ) 1 θ)^2 ∂law q) = -2*(q:ℂ) := by
  have h0 : Integrable (fun _ : ℝ => (1:ℂ)) (law q) := by
    simpa only [pow_zero] using law_mode_integrable q hq 0
  have h1 : Integrable (fun θ => circleMap (0:ℂ) 1 θ) (law q) := by
    simpa only [pow_one] using law_mode_integrable q hq 1
  have h2 := law_mode_integrable q hq 2
  have hm0 : (∫ _ : ℝ, (1:ℂ) ∂law q) = 1 := by
    simpa only [pow_zero] using law_moment_nat q hq 0
  have hm1 : (∫ θ, circleMap (0:ℂ) 1 θ ∂law q) = (q:ℂ) := by
    simpa only [pow_one] using law_moment_nat q hq 1
  simp_rw [backward_point]
  have ha : Integrable (fun θ => -circleMap (0:ℂ) 1 θ) (law q) := h1.neg
  have hb : Integrable (fun θ => ((2*q/(1-q^2):ℝ):ℂ)/2*((circleMap (0:ℂ) 1 θ)^2-1)) (law q) :=
    (h2.sub h0).const_mul _
  rw [integral_add ha hb, integral_neg,
    integral_const_mul, integral_sub h2 h0, hm0,hm1,law_moment_nat q hq 2]
  have hs := stationary_positive_mode q hq 0
  norm_num at hs
  push_cast
  linear_combination -hs


open FiniteFourierDifferentialTrace FiniteFourierSynthesis FiniteStableGamma.Core
open CauchySineDrift BrownianEnergyRepair.Torus

def mode (n : ℕ) : Fourier := AddMonoidAlgebra.single (axisWave n) 1

def drift (r : ℝ) (f : Fourier) : Fourier :=
  generator (stableSymbol 1) f + (r:ℂ) • transport f

theorem mode_value (n : ℕ) (θ : ℝ) :
    synthesis ![θ,0,0] (mode n) = (circleMap (0:ℂ) 1 θ)^n := by
  rw [mode,synthesis_single,one_mul,axis_character_nat]

theorem drift_mode_one (r θ : ℝ) :
    synthesis ![θ,0,0] (drift r (mode 1)) =
      -circleMap (0:ℂ) 1 θ + (r:ℂ)/2*(1-(circleMap (0:ℂ) 1 θ)^2) := by
  have h := generator_positive_mode r 0 θ
  simpa [drift,mode] using h

theorem drift_mode_two (r θ : ℝ) :
    synthesis ![θ,0,0] (drift r (mode 2)) =
      -2*(circleMap (0:ℂ) 1 θ)^2 + (r:ℂ)*
        (circleMap (0:ℂ) 1 θ-(circleMap (0:ℂ) 1 θ)^3) := by
  have h := generator_positive_mode r 1 θ
  convert h using 1 <;> simp [drift,mode] <;> ring

theorem actual_forward_pairing (q : ℝ) (hq : |q| < 1) :
    (∫ θ, starRingEnd ℂ (synthesis ![θ,0,0] (mode 1)) *
      synthesis ![θ,0,0] (drift (2*q/(1-q^2)) (mode 2)) ∂law q) = 0 := by
  simp_rw [mode_value,pow_one,drift_mode_two]
  exact forward_integral q hq

theorem actual_backward_pairing (q : ℝ) (hq : |q| < 1) :
    (∫ θ, starRingEnd ℂ (synthesis ![θ,0,0] (drift (2*q/(1-q^2)) (mode 1))) *
      synthesis ![θ,0,0] (mode 2) ∂law q) = -2*(q:ℂ) := by
  simp_rw [mode_value,drift_mode_one]
  exact backward_integral q hq

theorem not_hermitian_core (q : ℝ) (hq : |q| < 1) (hne : q ≠ 0) :
    ¬ (∀ f g : Fourier,
      (∫ θ, starRingEnd ℂ (synthesis ![θ,0,0] f) *
        synthesis ![θ,0,0] (drift (2*q/(1-q^2)) g) ∂law q) =
      (∫ θ, starRingEnd ℂ (synthesis ![θ,0,0] (drift (2*q/(1-q^2)) f)) *
        synthesis ![θ,0,0] g ∂law q)) := by
  intro h
  have hx := h (mode 1) (mode 2)
  rw [actual_forward_pairing q hq,actual_backward_pairing q hq] at hx
  have hz : (q:ℂ) = 0 := by linear_combination hx/2
  exact hne (Complex.ofReal_eq_zero.mp hz)

end OperatorDerivativeRewrite.Foundation.CauchyPoissonNonSymmetry
