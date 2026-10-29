import Foundation.SU2FourCurveJetTransfer
import Foundation.SU2HemisphereJets

/-! Actual axis matrix curves and their normalized Pauli two-jets. -/
noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.SU2AxisMatrixJets
open QuaternionSU2Representation SU2TraceHessianModel SU2MatrixExponentialBridge
open SU2JointPlaquetteCubic SU2ProductCurveHessian SU2ExponentialMembership ChristoffelSkewCancellation

def axisVector (a : Fin 3) (r : ℝ) : Fin 3 → ℝ :=
  if a=0 then ![0,0,2*r] else if a=1 then ![2*r,0,0] else ![0,2*r,0]

theorem axisVector_scale (a : Fin 3) (r : ℝ) : axisVector a r=r • axisVector a 1 := by
  ext i
  fin_cases a <;> fin_cases i <;> simp [axisVector] <;> ring

theorem axis_matrix_formula (a : Fin 3) (t : ℝ) :
    (axis a t : M2)=Real.cos t • (1 : M2)+Real.sin t • algebraElement (axisVector a 1) := by
  change QuaternionSU2Representation.repr (axisRaw a t)=_
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [QuaternionSU2Representation.repr,axisRaw,axisVector,algebraElement,tangent,SU2TraceHessianModel.generator,
      generatorX,generatorY,generatorZ,Fin.sum_univ_three,Matrix.one_apply,Complex.mul_re,
      Complex.mul_im]

theorem axis_inv (a : Fin 3) (t : ℝ) : (axis a t)⁻¹=axis a (-t) := by
  apply Subtype.ext
  change (axis a t : M2)ᴴ=(axis a (-t) : M2)
  rw [axis_matrix_formula,axis_matrix_formula]
  simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_smul,Matrix.conjTranspose_one,
    algebraElement_skewHermitian,star_trivial,Real.cos_neg,Real.sin_neg,neg_smul,smul_neg]

def curve (a : Fin 3) (r t : ℝ) : M2 := (axis a (t*r) : M2)
def slope (a : Fin 3) (r t : ℝ) : M2 :=
  (-r*Real.sin (t*r)) • (1 : M2)+(r*Real.cos (t*r)) • algebraElement (axisVector a 1)

theorem curve_contDiff (a : Fin 3) (r : ℝ) : ContDiff ℝ 2 (curve a r) := by
  have he : curve a r=(fun t : ℝ => Real.cos (t*r) • (1 : M2)+
      Real.sin (t*r) • algebraElement (axisVector a 1)) := funext (fun t => axis_matrix_formula a (t*r))
  rw [he]
  fun_prop

theorem curve_hasDerivAt (a : Fin 3) (r t : ℝ) : HasDerivAt (curve a r) (slope a r t) t := by
  have hc := ((Real.hasDerivAt_cos (t*r)).comp t ((hasDerivAt_id t).mul_const r)).smul_const (1 : M2)
  have hs := ((Real.hasDerivAt_sin (t*r)).comp t ((hasDerivAt_id t).mul_const r)).smul_const
    (algebraElement (axisVector a 1))
  convert! hc.add hs using 1
  · funext u
    exact axis_matrix_formula a (u*r)
  · unfold slope
    congr 1 <;> ring

theorem curve_zero (a : Fin 3) (r : ℝ) : curve a r 0=1 := by
  rw [curve,axis_matrix_formula]
  simp

theorem curve_first_zero (a : Fin 3) (r : ℝ) : deriv (curve a r) 0=algebraElement (axisVector a r) := by
  have hh := (curve_hasDerivAt a r 0).deriv
  rw [axisVector_scale,algebraElement_smul]
  convert! hh using 1 <;> simp [slope]

theorem slope_hasDerivAt_zero (a : Fin 3) (r : ℝ) :
    HasDerivAt (slope a r) ((-r^2) • (1 : M2)) 0 := by
  have hi := (hasDerivAt_id (0 : ℝ)).mul_const r
  have hs := (((Real.hasDerivAt_sin (0*r)).comp 0 hi).const_mul (-r)).smul_const (1 : M2)
  have hc := (((Real.hasDerivAt_cos (0*r)).comp 0 hi).const_mul r).smul_const
    (algebraElement (axisVector a 1))
  convert! hs.add hc using 1 <;> simp [slope,pow_two]

theorem curve_second_zero (a : Fin 3) (r : ℝ) :
    deriv (deriv (curve a r)) 0=(algebraElement (axisVector a r))^2 := by
  have he : deriv (curve a r)=slope a r := funext (fun t => (curve_hasDerivAt a r t).deriv)
  rw [he]
  have hh := (slope_hasDerivAt_zero a r).deriv
  have hv : lengthSq (axisVector a r)=4*r^2 := by
    fin_cases a <;> simp [lengthSq,axisVector,Fin.sum_univ_three] <;> ring
  rw [algebraElement_sq,hv]
  have he' : -(((4*r^2 : ℝ) : ℂ)/4)=((-r^2 : ℝ) : ℂ) := by push_cast; ring
  rw [he']
  convert! hh using 1

end OperatorDerivativeRewrite.Foundation.SU2AxisMatrixJets
