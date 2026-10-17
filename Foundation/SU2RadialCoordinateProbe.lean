import Foundation.SU2TraceHessianModel
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Ordinary radial-coordinate probes; no identification with a lattice Hessian is assumed. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.SU2RadialCoordinateProbe
set_option backward.isDefEq.respectTransparency false

def radius (r t : ℝ) : ℝ := Real.sqrt (r^2+t^2)
def transverse (r t : ℝ) : ℝ := 1-Real.cos (radius r t/2)
def transverseSlope (r t : ℝ) : ℝ := t*(Real.sin (radius r t/2)/(2*radius r t))

theorem radius_pos {r : ℝ} (hr : 0 < r) (t : ℝ) : 0 < radius r t := by
  apply Real.sqrt_pos.2
  nlinarith [sq_nonneg t]

theorem radius_zero {r : ℝ} (hr : 0 < r) : radius r 0=r := by
  simpa [radius] using Real.sqrt_sq hr.le

theorem radius_hasDerivAt {r : ℝ} (hr : 0 < r) (t : ℝ) :
    HasDerivAt (radius r) (t/radius r t) t := by
  have hp : r^2+t^2 ≠ 0 := by nlinarith [sq_nonneg t]
  have hh := ((hasDerivAt_const t (r^2)).add ((hasDerivAt_id t).pow 2)).sqrt hp
  convert hh using 1 <;> first | rfl | (dsimp [radius]; ring)

theorem transverse_hasDerivAt {r : ℝ} (hr : 0 < r) (t : ℝ) :
    HasDerivAt (transverse r) (transverseSlope r t) t := by
  have hi := (radius_hasDerivAt hr t).div_const 2
  have hh := (hasDerivAt_const t (1:ℝ)).sub
    ((Real.hasDerivAt_cos (radius r t/2)).comp t hi)
  convert hh using 1 <;> first | rfl | (dsimp [transverseSlope]; ring)

theorem transverseSlope_hasDerivAt_zero {r : ℝ} (hr : 0 < r) :
    HasDerivAt (transverseSlope r) (Real.sin (r/2)/(2*r)) 0 := by
  have hd := radius_hasDerivAt hr 0
  have hn := (Real.hasDerivAt_sin (radius r 0/2)).comp 0 (hd.div_const 2)
  have hden := hd.const_mul 2
  have hq := hn.div hden (by have := radius_pos hr 0; positivity)
  have hh := (hasDerivAt_id (0:ℝ)).mul hq
  change HasDerivAt (transverseSlope r) _ 0 at hh
  simpa [transverseSlope, radius_zero hr] using hh

theorem transverse_second_derivative {r : ℝ} (hr : 0 < r) :
    deriv (deriv (transverse r)) 0=Real.sin (r/2)/(2*r) := by
  have he : deriv (transverse r)=transverseSlope r :=
    funext (fun t => (transverse_hasDerivAt hr t).deriv)
  rw [he]
  exact (transverseSlope_hasDerivAt_zero hr).deriv

theorem longitudinal_second_derivative (r : ℝ) :
    deriv (deriv (fun t : ℝ => 1-Real.cos ((r+t)/2))) 0=Real.cos (r/2)/4 := by
  have he : (fun t : ℝ => 1-Real.cos ((r+t)/2))=
      SU2TraceHessianModel.axisCurve (r/2) := by
    funext t
    rw [SU2TraceHessianModel.axisCurve_eq]
    congr 2 <;> ring
  rw [he]
  exact SU2TraceHessianModel.axisCurve_second_derivative (r/2)

def radialTensor (c s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal (fun i => if i=2 then c else s)
def axial : Matrix (Fin 3) (Fin 3) ℝ := radialTensor (2/3) (-1/3)
def scalarCoefficient (c s : ℝ) : ℝ := (c+2*s)/3

theorem radialTensor_trace (c s : ℝ) : Matrix.trace (radialTensor c s)=c+2*s := by
  norm_num [radialTensor, Matrix.trace, Fin.sum_univ_three]
  ring

theorem axial_trace : Matrix.trace axial=0 := by
  norm_num [axial, radialTensor_trace]

theorem scalarCoefficient_trace (c s : ℝ) :
    scalarCoefficient c s=Matrix.trace (radialTensor c s)/3 := by
  rw [radialTensor_trace]; rfl

theorem radialTensor_decomposition (c s : ℝ) :
    radialTensor c s=scalarCoefficient c s • (1 : Matrix (Fin 3) (Fin 3) ℝ)+
      (c-s) • axial := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [radialTensor, axial, scalarCoefficient, Matrix.diagonal] <;> ring

theorem scalar_correction_eq_transverse_iff (c s : ℝ) :
    scalarCoefficient c s-1=s-1 ↔ c=s := by
  unfold scalarCoefficient
  constructor <;> intro h <;> linarith

theorem scalar_transverse_residual (c s : ℝ) :
    scalarCoefficient c s-s=(c-s)/3 := by
  unfold scalarCoefficient
  ring

theorem identity_trace_curvature :
    deriv (deriv (SU2TraceHessianModel.axisCurve 0)) 0=1/4 := by
  rw [SU2TraceHessianModel.axisCurve_second_derivative]
  norm_num

theorem identity_trace_curvature_not_negative :
    deriv (deriv (SU2TraceHessianModel.axisCurve 0)) 0 ≠ -(1/4:ℝ) := by
  rw [identity_trace_curvature]
  norm_num

end OperatorDerivativeRewrite.Foundation.SU2RadialCoordinateProbe
