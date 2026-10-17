import Foundation.GaussianSwirlProfileMoments

/-! A stationary viscous Burgers vortex with strain rate 4 nu. All coordinate
derivatives are genuine; no spatial decay, finite energy or periodicity is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace OperatorDerivativeRewrite.Foundation.StrainedBurgersVortex
open GaussianSwirlVelocity GaussianSwirlProfileMoments
set_option backward.isDefEq.respectTransparency false

def velocity (ν γ x y z : ℝ) : Fin 3 → ℝ :=
  ![-2*ν*x-γ*y*angularProfile (x^2+y^2),
    -2*ν*y+γ*x*angularProfile (x^2+y^2), 4*ν*z]

def pressure (ν γ x y z : ℝ) : ℝ :=
  γ^2 * GaussianSwirlVelocity.pressure x y - 2*ν^2*(x^2+y^2) - 8*ν^2*z^2

theorem velocity_smooth (ν γ : ℝ) :
    ContDiff ℝ ∞ (fun q : Fin 3 → ℝ => velocity ν γ (q 0) (q 1) (q 2)) := by
  have hp : ContDiff ℝ ∞ (fun q : Fin 3 → ℝ => angularProfile ((q 0)^2+(q 1)^2)) :=
    angularProfile_smooth.comp (by fun_prop)
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [velocity] <;> fun_prop

theorem pressure_smooth (ν γ : ℝ) :
    ContDiff ℝ ∞ (fun q : Fin 3 → ℝ => pressure ν γ (q 0) (q 1) (q 2)) := by
  have hp : ContDiff ℝ ∞ (fun q : Fin 3 → ℝ => radialPressure ((q 0)^2+(q 1)^2)) :=
    radialPressure_smooth.comp (by fun_prop)
  dsimp [pressure, GaussianSwirlVelocity.pressure]
  fun_prop

def jacobian (ν γ x y _z : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![-2*ν-2*γ*x*y*angularDerivative (x^2+y^2),
      -γ*angularProfile (x^2+y^2)-2*γ*y^2*angularDerivative (x^2+y^2),0],
    ![γ*angularProfile (x^2+y^2)+2*γ*x^2*angularDerivative (x^2+y^2),
      -2*ν+2*γ*x*y*angularDerivative (x^2+y^2),0], ![0,0,4*ν]]

theorem velocity_x (ν γ x y z : ℝ) (i : Fin 3) :
    HasDerivAt (fun t => velocity ν γ t y z i) (jacobian ν γ x y z i 0) x := by
  fin_cases i
  · have h := ((hasDerivAt_id x).const_mul (-2*ν)).add
      ((profile_x x y).const_mul (-γ*y))
    convert h using 1 <;> (try funext t) <;> simp [velocity, jacobian] <;> ring
  · have h := (((hasDerivAt_id x).mul (profile_x x y)).const_mul γ).add_const (-2*ν*y)
    convert h using 1 <;> (try funext t) <;> simp [velocity, jacobian] <;> ring
  · simpa [velocity, jacobian] using hasDerivAt_const x (4*ν*z)

theorem velocity_y (ν γ x y z : ℝ) (i : Fin 3) :
    HasDerivAt (fun t => velocity ν γ x t z i) (jacobian ν γ x y z i 1) y := by
  fin_cases i
  · have h := (((hasDerivAt_id y).mul (profile_y x y)).const_mul (-γ)).add_const (-2*ν*x)
    convert h using 1 <;> (try funext t) <;> simp [velocity, jacobian] <;> ring
  · have h := ((hasDerivAt_id y).const_mul (-2*ν)).add
      ((profile_y x y).const_mul (γ*x))
    convert h using 1 <;> (try funext t) <;> simp [velocity, jacobian] <;> ring
  · simpa [velocity, jacobian] using hasDerivAt_const y (4*ν*z)

theorem velocity_z (ν γ x y z : ℝ) (i : Fin 3) :
    HasDerivAt (fun t => velocity ν γ x y t i) (jacobian ν γ x y z i 2) z := by
  fin_cases i
  · simpa [velocity, jacobian] using hasDerivAt_const z
      (-2*ν*x-γ*y*angularProfile (x^2+y^2))
  · simpa [velocity, jacobian] using hasDerivAt_const z
      (-2*ν*y+γ*x*angularProfile (x^2+y^2))
  · simpa [velocity, jacobian] using (hasDerivAt_id z).const_mul (4*ν)

theorem divergence_zero (ν γ x y z : ℝ) : Matrix.trace (jacobian ν γ x y z) = 0 := by
  simp [jacobian, Matrix.trace, Fin.sum_univ_succ]
  ring

def laplacian (ν γ x y z : ℝ) : Fin 3 → ℝ := fun i =>
  deriv (fun t => jacobian ν γ t y z i 0) x +
    deriv (fun t => jacobian ν γ x t z i 1) y +
      deriv (fun t => jacobian ν γ x y t i 2) z

theorem laplacian_eq (ν γ x y z : ℝ) : laplacian ν γ x y z =
    ![2*γ*y*Real.exp (-(x^2+y^2)), -2*γ*x*Real.exp (-(x^2+y^2)), 0] := by
  have h00 : HasDerivAt (fun t => jacobian ν γ t y z 0 0)
      (-2*γ*y*(angularDerivative (x^2+y^2)+2*x^2*angularSecond (x^2+y^2))) x := by
    have h := (((hasDerivAt_id x).mul (derivative_x x y)).const_mul (-2*γ*y)).const_add (-2*ν)
    convert h using 1 <;> (try funext t) <;> dsimp [jacobian] <;> ring
  have h01 : HasDerivAt (fun t => jacobian ν γ x t z 0 1)
      (-6*γ*y*angularDerivative (x^2+y^2)-4*γ*y^3*angularSecond (x^2+y^2)) y := by
    have h := ((profile_y x y).const_mul (-γ)).add
      (((hasDerivAt_pow 2 y).mul (derivative_y x y)).const_mul (-2*γ))
    convert h using 1 <;> (try funext t) <;> simp [jacobian] <;> ring
  have h10 : HasDerivAt (fun t => jacobian ν γ t y z 1 0)
      (6*γ*x*angularDerivative (x^2+y^2)+4*γ*x^3*angularSecond (x^2+y^2)) x := by
    have h := ((profile_x x y).const_mul γ).add
      (((hasDerivAt_pow 2 x).mul (derivative_x x y)).const_mul (2*γ))
    convert h using 1 <;> (try funext t) <;> simp [jacobian] <;> ring
  have h11 : HasDerivAt (fun t => jacobian ν γ x t z 1 1)
      (2*γ*x*(angularDerivative (x^2+y^2)+2*y^2*angularSecond (x^2+y^2))) y := by
    have h := (((hasDerivAt_id y).mul (derivative_y x y)).const_mul (2*γ*x)).const_add (-2*ν)
    convert h using 1 <;> (try funext t) <;> dsimp [jacobian] <;> ring
  have hz (i : Fin 3) : deriv (fun t => jacobian ν γ x y t i 2) z = 0 := by
    fin_cases i <;> simp [jacobian]
  have he := angular_second_identity (x^2+y^2)
  ext i
  fin_cases i
  · change deriv (fun t => jacobian ν γ t y z 0 0) x +
      deriv (fun t => jacobian ν γ x t z 0 1) y +
      deriv (fun t => jacobian ν γ x y t 0 2) z = 2*γ*y*Real.exp (-(x^2+y^2))
    rw [h00.deriv, h01.deriv, hz, ← neg_neg (Real.exp (-(x^2+y^2))), ← he]
    ring
  · change deriv (fun t => jacobian ν γ t y z 1 0) x +
      deriv (fun t => jacobian ν γ x t z 1 1) y +
      deriv (fun t => jacobian ν γ x y t 1 2) z = -2*γ*x*Real.exp (-(x^2+y^2))
    rw [h10.deriv, h11.deriv, hz, ← neg_neg (Real.exp (-(x^2+y^2))), ← he]
    ring
  · simp [laplacian, jacobian]

def pressureGradient (ν γ x y z : ℝ) : Fin 3 → ℝ :=
  ![deriv (fun t => pressure ν γ t y z) x,
    deriv (fun t => pressure ν γ x t z) y, deriv (fun t => pressure ν γ x y t) z]

theorem pressureGradient_eq (ν γ x y z : ℝ) : pressureGradient ν γ x y z =
    ![γ^2*x*angularProfile (x^2+y^2)^2-4*ν^2*x,
      γ^2*y*angularProfile (x^2+y^2)^2-4*ν^2*y, -16*ν^2*z] := by
  have hx : HasDerivAt (fun t => pressure ν γ t y z)
      (γ^2*x*angularProfile (x^2+y^2)^2-4*ν^2*x) x := by
    have h := (((GaussianSwirlVelocity.pressure_x x y).const_mul (γ^2)).sub
      (((hasDerivAt_pow 2 x).add_const (y^2)).const_mul (2*ν^2))).sub_const (8*ν^2*z^2)
    convert h using 1 <;> (try funext t) <;> simp [pressure] <;> ring
  have hy : HasDerivAt (fun t => pressure ν γ x t z)
      (γ^2*y*angularProfile (x^2+y^2)^2-4*ν^2*y) y := by
    have h := (((GaussianSwirlVelocity.pressure_y x y).const_mul (γ^2)).sub
      (((hasDerivAt_pow 2 y).const_add (x^2)).const_mul (2*ν^2))).sub_const (8*ν^2*z^2)
    convert h using 1 <;> (try funext t) <;> simp [pressure] <;> ring
  have hz : HasDerivAt (fun t => pressure ν γ x y t) (-16*ν^2*z) z := by
    have h := ((hasDerivAt_pow 2 z).const_mul (-8*ν^2)).const_add
      (γ^2*GaussianSwirlVelocity.pressure x y-2*ν^2*(x^2+y^2))
    convert h using 1 <;> (try funext t) <;> simp [pressure] <;> ring
  simp only [pressureGradient, hx.deriv, hy.deriv, hz.deriv]

def acceleration (ν γ x y z : ℝ) : Fin 3 → ℝ :=
  fun i => ∑ j, velocity ν γ x y z j * jacobian ν γ x y z i j

theorem stationary_navier_stokes (ν γ x y z : ℝ) :
    acceleration ν γ x y z + pressureGradient ν γ x y z = ν • laplacian ν γ x y z := by
  rw [pressureGradient_eq, laplacian_eq]
  simp only [← angular_curl_identity (x^2+y^2)]
  ext i
  fin_cases i <;>
    simp [acceleration, velocity, jacobian, Fin.sum_univ_succ] <;> ring

def vorticity (ν γ x y z : ℝ) : Fin 3 → ℝ :=
  ![jacobian ν γ x y z 2 1-jacobian ν γ x y z 1 2,
    jacobian ν γ x y z 0 2-jacobian ν γ x y z 2 0,
    jacobian ν γ x y z 1 0-jacobian ν γ x y z 0 1]

theorem vorticity_eq (ν γ x y z : ℝ) : vorticity ν γ x y z =
    ![0, 0, γ*Real.exp (-(x^2+y^2))] := by
  simp only [← angular_curl_identity (x^2+y^2)]
  ext i
  fin_cases i <;>
    simp [vorticity, jacobian] <;> ring

end OperatorDerivativeRewrite.Foundation.StrainedBurgersVortex
