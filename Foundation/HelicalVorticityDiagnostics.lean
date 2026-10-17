import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! Actual coordinate derivatives of the proposed helical vortex ansatz. -/
noncomputable section
open scoped Matrix
namespace OperatorDerivativeRewrite.Foundation.HelicalVorticityDiagnostics
set_option backward.isDefEq.respectTransparency false

def profile (x y : ℝ) : ℝ := Real.exp (-(x^2+y^2))
def helical (ε x y z : ℝ) : Fin 3 → ℝ :=
  ![ε*profile x y*Real.cos z, ε*profile x y*Real.sin z, profile x y]

def jacobian (ε x y z : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![deriv (fun t => helical ε t y z 0) x, deriv (fun t => helical ε x t z 0) y,
      deriv (fun t => helical ε x y t 0) z;
     deriv (fun t => helical ε t y z 1) x, deriv (fun t => helical ε x t z 1) y,
      deriv (fun t => helical ε x y t 1) z;
     deriv (fun t => helical ε t y z 2) x, deriv (fun t => helical ε x t z 2) y,
      deriv (fun t => helical ε x y t 2) z]

theorem profile_x (x y : ℝ) : HasDerivAt (fun t => profile t y) (-2*x*profile x y) x := by
  have h := ((hasDerivAt_pow 2 x).add_const (y^2)).neg.exp
  convert h using 1 <;> simp [profile] <;> ring

theorem profile_y (x y : ℝ) : HasDerivAt (profile x) (-2*y*profile x y) y := by
  unfold profile
  have h := ((hasDerivAt_pow 2 y).const_add (x^2)).neg.exp
  convert h using 1 <;> simp <;> ring

theorem jacobian_eq (ε x y z : ℝ) :
    jacobian ε x y z=!![-2*ε*x*profile x y*Real.cos z, -2*ε*y*profile x y*Real.cos z,
      -ε*profile x y*Real.sin z;
     -2*ε*x*profile x y*Real.sin z, -2*ε*y*profile x y*Real.sin z, ε*profile x y*Real.cos z;
     -2*x*profile x y, -2*y*profile x y, 0] := by
  have hx := profile_x x y
  have hy := profile_y x y
  have hxc : HasDerivAt (fun t => ε*profile t y*Real.cos z) (-2*ε*x*profile x y*Real.cos z) x := by
    convert (hx.const_mul ε).mul_const (Real.cos z) using 1 <;> ring
  have hyc : HasDerivAt (fun t => ε*profile x t*Real.cos z) (-2*ε*y*profile x y*Real.cos z) y := by
    convert (hy.const_mul ε).mul_const (Real.cos z) using 1 <;> ring
  have hzc : HasDerivAt (fun t => ε*profile x y*Real.cos t) (-ε*profile x y*Real.sin z) z := by
    convert (Real.hasDerivAt_cos z).const_mul (ε*profile x y) using 1 <;> ring
  have hxs : HasDerivAt (fun t => ε*profile t y*Real.sin z) (-2*ε*x*profile x y*Real.sin z) x := by
    convert (hx.const_mul ε).mul_const (Real.sin z) using 1 <;> ring
  have hys : HasDerivAt (fun t => ε*profile x t*Real.sin z) (-2*ε*y*profile x y*Real.sin z) y := by
    convert (hy.const_mul ε).mul_const (Real.sin z) using 1 <;> ring
  have hzs : HasDerivAt (fun t => ε*profile x y*Real.sin t) (ε*profile x y*Real.cos z) z :=
    (Real.hasDerivAt_sin z).const_mul (ε*profile x y)
  change !![deriv (fun t => ε*profile t y*Real.cos z) x,
      deriv (fun t => ε*profile x t*Real.cos z) y,
      deriv (fun t => ε*profile x y*Real.cos t) z;
    deriv (fun t => ε*profile t y*Real.sin z) x,
      deriv (fun t => ε*profile x t*Real.sin z) y,
      deriv (fun t => ε*profile x y*Real.sin t) z;
    deriv (fun t => profile t y) x, deriv (profile x) y, deriv (fun _ : ℝ => profile x y) z]=_
  rw [hxc.deriv, hyc.deriv, hzc.deriv, hxs.deriv, hys.deriv, hzs.deriv,
    hx.deriv, hy.deriv, deriv_const]

def divergence (ε x y z : ℝ) : ℝ := Matrix.trace (jacobian ε x y z)

theorem divergence_eq (ε x y z : ℝ) :
    divergence ε x y z=-2*ε*profile x y*(x*Real.cos z+y*Real.sin z) := by
  rw [divergence, jacobian_eq]
  norm_num [Matrix.trace, Fin.sum_univ_three]
  ring

theorem divergence_witness (ε : ℝ) (hε : ε ≠ 0) : divergence ε 1 0 0 ≠ 0 := by
  rw [divergence_eq]
  norm_num [profile]
  exact hε

theorem not_divergence_free (ε : ℝ) (hε : ε ≠ 0) :
    ¬ ∀ x y z : ℝ, divergence ε x y z=0 := by
  intro h
  exact divergence_witness ε hε (h 1 0 0)

theorem trace_square (ε x y z : ℝ) :
    Matrix.trace (jacobian ε x y z*jacobian ε x y z)=
      4*ε^2*(profile x y)^2*(x*Real.cos z+y*Real.sin z)^2+
      4*ε*(profile x y)^2*(x*Real.sin z-y*Real.cos z) := by
  rw [jacobian_eq]
  norm_num [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_three]
  ring

def linearTrace (x y z : ℝ) : ℝ := 4*(profile x y)^2*(x*Real.sin z-y*Real.cos z)
def quadraticTrace (x y z : ℝ) : ℝ := 4*(profile x y)^2*(x*Real.cos z+y*Real.sin z)^2

theorem trace_expansion (ε x y z : ℝ) :
    Matrix.trace (jacobian ε x y z*jacobian ε x y z)=
      ε*linearTrace x y z+ε^2*quadraticTrace x y z := by
  rw [trace_square]
  unfold linearTrace quadraticTrace
  ring

theorem straight_trace_zero (x y z : ℝ) :
    Matrix.trace (jacobian 0 x y z*jacobian 0 x y z)=0 := by
  rw [trace_square]
  ring

theorem linearTrace_period_average (x y : ℝ) :
    (∫ z in (0:ℝ)..(2*Real.pi), linearTrace x y z)=0 := by
  unfold linearTrace
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub
      ((Real.continuous_sin.const_mul x).intervalIntegrable _ _)
      ((Real.continuous_cos.const_mul y).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_sin, integral_cos]
  simp

theorem fixed_pressure_linear_average (p x y : ℝ) :
    (∫ z in (0:ℝ)..(2*Real.pi), p*linearTrace x y z)=0 := by
  rw [intervalIntegral.integral_const_mul, linearTrace_period_average, mul_zero]

def corrected (ε x y z : ℝ) : Fin 3 → ℝ :=
  ![ε*profile x y*Real.cos z, ε*profile x y*Real.sin z,
    profile x y+2*ε*profile x y*(x*Real.sin z-y*Real.cos z)]

def correctedDivergence (ε x y z : ℝ) : ℝ :=
  deriv (fun t => corrected ε t y z 0) x+
    deriv (fun t => corrected ε x t z 1) y+deriv (fun t => corrected ε x y t 2) z

/-- An axial term of the same first order restores the solenoidal constraint. -/
theorem corrected_divergence_zero (ε x y z : ℝ) : correctedDivergence ε x y z=0 := by
  have hx := ((profile_x x y).const_mul ε).mul_const (Real.cos z)
  have hy := ((profile_y x y).const_mul ε).mul_const (Real.sin z)
  have hz := ((((Real.hasDerivAt_sin z).const_mul x).sub
    ((Real.hasDerivAt_cos z).const_mul y)).const_mul (2*ε*profile x y)).const_add (profile x y)
  change HasDerivAt (fun t : ℝ => profile x y+2*ε*profile x y*(x*Real.sin t-y*Real.cos t))
    (2*ε*profile x y*(x*Real.cos z-y*(-Real.sin z))) z at hz
  change deriv (fun t => ε*profile t y*Real.cos z) x+
    deriv (fun t => ε*profile x t*Real.sin z) y+
      deriv (fun t => profile x y+2*ε*profile x y*(x*Real.sin t-y*Real.cos t)) z=0
  rw [hx.deriv, hy.deriv, hz.deriv]
  ring

theorem axial_correction_nonzero (ε : ℝ) (hε : ε ≠ 0) :
    corrected ε 0 1 0 2 ≠ helical ε 0 1 0 2 := by
  norm_num [corrected, helical, profile]
  intro he
  have hp := Real.exp_pos (-1)
  apply hε
  nlinarith

theorem helical_smooth (ε : ℝ) :
    ContDiff ℝ ⊤ (fun p : Fin 3 → ℝ => helical ε (p 0) (p 1) (p 2)) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ⊤ (fun p : Fin 3 → ℝ => ε*profile (p 0) (p 1)*Real.cos (p 2))
    unfold profile
    fun_prop
  · change ContDiff ℝ ⊤ (fun p : Fin 3 → ℝ => ε*profile (p 0) (p 1)*Real.sin (p 2))
    unfold profile
    fun_prop
  · change ContDiff ℝ ⊤ (fun p : Fin 3 → ℝ => profile (p 0) (p 1))
    unfold profile
    fun_prop

theorem corrected_smooth (ε : ℝ) :
    ContDiff ℝ ⊤ (fun p : Fin 3 → ℝ => corrected ε (p 0) (p 1) (p 2)) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ⊤ (fun p : Fin 3 → ℝ => ε*profile (p 0) (p 1)*Real.cos (p 2))
    unfold profile
    fun_prop
  · change ContDiff ℝ ⊤ (fun p : Fin 3 → ℝ => ε*profile (p 0) (p 1)*Real.sin (p 2))
    unfold profile
    fun_prop
  · change ContDiff ℝ ⊤ (fun p : Fin 3 → ℝ => profile (p 0) (p 1)+
      2*ε*profile (p 0) (p 1)*(p 0*Real.sin (p 2)-p 1*Real.cos (p 2)))
    unfold profile
    fun_prop

end OperatorDerivativeRewrite.Foundation.HelicalVorticityDiagnostics
