import Foundation.StrainedBurgersVortex

/-! The actual strained vortex has zero gradient-square trace but a nonzero
axial pressure contraction and boundary flux. All integrals below are axial
interval integrals, not whole-space or periodic pressure identities. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
namespace OperatorDerivativeRewrite.Foundation.BurgersAxialPressureFlux
open StrainedBurgersVortex
set_option backward.isDefEq.respectTransparency false

def hessian (ν γ x y z : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![deriv (fun t => pressureGradient ν γ t y z 0) x,
      deriv (fun t => pressureGradient ν γ x t z 0) y,
      deriv (fun t => pressureGradient ν γ x y t 0) z],
    ![deriv (fun t => pressureGradient ν γ t y z 1) x,
      deriv (fun t => pressureGradient ν γ x t z 1) y,
      deriv (fun t => pressureGradient ν γ x y t 1) z],
    ![deriv (fun t => pressureGradient ν γ t y z 2) x,
      deriv (fun t => pressureGradient ν γ x t z 2) y,
      deriv (fun t => pressureGradient ν γ x y t 2) z] ]

theorem hessian_zz (ν γ x y z : ℝ) : hessian ν γ x y z 2 2 = -16*ν^2 := by
  simp only [hessian, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  simp_rw [pressureGradient_eq]
  simpa using ((hasDerivAt_id z).const_mul (-16*ν^2)).deriv

theorem hessian_xx (ν γ x y z : ℝ) : hessian ν γ x y z 0 0 =
    γ^2*(GaussianSwirlVelocity.angularProfile (x^2+y^2)^2 +
      4*x^2*GaussianSwirlVelocity.angularProfile (x^2+y^2)*
        GaussianSwirlVelocity.angularDerivative (x^2+y^2)) - 4*ν^2 := by
  simp only [hessian, Matrix.cons_val_zero, Matrix.head_cons, Matrix.tail_cons]
  simp_rw [pressureGradient_eq]
  have hd := ((GaussianSwirlVelocity.pressure_xx x y).const_mul (γ^2)).sub
    ((hasDerivAt_id x).const_mul (4*ν^2))
  have hh : HasDerivAt (fun t => γ^2*t*GaussianSwirlVelocity.angularProfile (t^2+y^2)^2-
      4*ν^2*t)
      (γ^2*(GaussianSwirlVelocity.angularProfile (x^2+y^2)^2+
        4*x^2*GaussianSwirlVelocity.angularProfile (x^2+y^2)*
          GaussianSwirlVelocity.angularDerivative (x^2+y^2))-4*ν^2) x := by
    convert hd using 1 <;> (try funext t) <;> (try dsimp) <;> ring
  exact hh.deriv

theorem hessian_yy (ν γ x y z : ℝ) : hessian ν γ x y z 1 1 =
    γ^2*(GaussianSwirlVelocity.angularProfile (x^2+y^2)^2 +
      4*y^2*GaussianSwirlVelocity.angularProfile (x^2+y^2)*
        GaussianSwirlVelocity.angularDerivative (x^2+y^2)) - 4*ν^2 := by
  simp only [hessian, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
  simp_rw [pressureGradient_eq]
  have hd := ((GaussianSwirlVelocity.pressure_yy x y).const_mul (γ^2)).sub
    ((hasDerivAt_id y).const_mul (4*ν^2))
  have hh : HasDerivAt (fun t => γ^2*t*GaussianSwirlVelocity.angularProfile (x^2+t^2)^2-
      4*ν^2*t)
      (γ^2*(GaussianSwirlVelocity.angularProfile (x^2+y^2)^2+
        4*y^2*GaussianSwirlVelocity.angularProfile (x^2+y^2)*
          GaussianSwirlVelocity.angularDerivative (x^2+y^2))-4*ν^2) y := by
    convert hd using 1 <;> (try funext t) <;> (try dsimp) <;> ring
  exact hh.deriv

/-- Full pressure-Poisson compatibility for the actual strained velocity. -/
theorem pressure_poisson (ν γ x y z : ℝ) : Matrix.trace (hessian ν γ x y z) =
    -Matrix.trace (jacobian ν γ x y z * jacobian ν γ x y z) := by
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, jacobian,
    hessian_xx, hessian_yy, hessian_zz]
  ring

def vorticityJacobian (ν γ x y z : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![deriv (fun t => vorticity ν γ t y z 0) x,
      deriv (fun t => vorticity ν γ x t z 0) y,
      deriv (fun t => vorticity ν γ x y t 0) z],
    ![deriv (fun t => vorticity ν γ t y z 1) x,
      deriv (fun t => vorticity ν γ x t z 1) y,
      deriv (fun t => vorticity ν γ x y t 1) z],
    ![deriv (fun t => vorticity ν γ t y z 2) x,
      deriv (fun t => vorticity ν γ x t z 2) y,
      deriv (fun t => vorticity ν γ x y t 2) z] ]

theorem trace_square_zero (ν γ x y z : ℝ) :
    Matrix.trace (vorticityJacobian ν γ x y z * vorticityJacobian ν γ x y z) = 0 := by
  unfold vorticityJacobian
  simp_rw [vorticity_eq]
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]

def contraction (ν γ x y z : ℝ) : ℝ :=
  dotProduct (vorticity ν γ x y z) ((hessian ν γ x y z).mulVec (vorticity ν γ x y z))

theorem contraction_eq (ν γ x y z : ℝ) : contraction ν γ x y z =
    -16*ν^2*γ^2*(Real.exp (-(x^2+y^2)))^2 := by
  simp [contraction, vorticity_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hessian_zz]
  ring

theorem contraction_neg (ν γ x y z : ℝ) (hν : ν ≠ 0) (hγ : γ ≠ 0) :
    contraction ν γ x y z < 0 := by
  rw [contraction_eq]
  have hp : 0 < 16*ν^2*γ^2*(Real.exp (-(x^2+y^2)))^2 := by positivity
  nlinarith

def axialFlux (ν γ x y z : ℝ) : ℝ :=
  (vorticity ν γ x y z 2)^2 * pressureGradient ν γ x y z 2

theorem axialFlux_eq (ν γ x y z : ℝ) : axialFlux ν γ x y z =
    -16*ν^2*γ^2*z*(Real.exp (-(x^2+y^2)))^2 := by
  simp [axialFlux, vorticity_eq, pressureGradient_eq]
  ring

theorem axial_integral_boundary (ν γ x y a b : ℝ) :
    (∫ z in a..b, contraction ν γ x y z) = axialFlux ν γ x y b - axialFlux ν γ x y a := by
  simp_rw [contraction_eq, axialFlux_eq]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem unit_slab_contraction (ν γ x y : ℝ) :
    (∫ z in (0 : ℝ)..1, contraction ν γ x y z) = contraction ν γ x y 0 := by
  simp_rw [contraction_eq]
  simp

theorem trace_does_not_cancel_slab (ν γ x y : ℝ) (hν : ν ≠ 0) (hγ : γ ≠ 0) :
    (∫ z in (0 : ℝ)..1, contraction ν γ x y z) ≠
      ∫ z in (0 : ℝ)..1, pressure ν γ x y z *
        Matrix.trace (vorticityJacobian ν γ x y z * vorticityJacobian ν γ x y z) := by
  simp_rw [trace_square_zero, mul_zero]
  rw [intervalIntegral.integral_zero, unit_slab_contraction]
  exact ne_of_lt (contraction_neg ν γ x y 0 hν hγ)

theorem axial_unbounded_above (ν γ : ℝ) (hν : ν ≠ 0) (M : ℝ) :
    ∃ z : ℝ, M < velocity ν γ 0 0 z 2 := by
  refine ⟨(M+1)/(4*ν), ?_⟩
  have he : 4*ν*((M+1)/(4*ν)) = M+1 := by field_simp
  simpa only [velocity, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, he] using
    (lt_add_one M)

theorem axial_unit_not_periodic (ν γ z : ℝ) (hν : ν ≠ 0) :
    velocity ν γ 0 0 (z+1) ≠ velocity ν γ 0 0 z := by
  intro h
  have he := congrFun h 2
  simp only [velocity, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at he
  apply hν
  nlinarith

end OperatorDerivativeRewrite.Foundation.BurgersAxialPressureFlux
