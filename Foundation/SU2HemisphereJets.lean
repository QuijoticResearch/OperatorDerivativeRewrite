import Foundation.SU2HemisphereChart
import Foundation.SU2FourWordVariation
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Exact first two matrix jets of the actual Haar hemisphere chart. -/
noncomputable section
open scoped Matrix Matrix.Norms.Operator Quaternion
namespace OperatorDerivativeRewrite.Foundation.SU2HemisphereJets
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereChart
open SU2TraceHessianModel SU2MatrixExponentialBridge SU2ExponentialMembership
open ChristoffelSkewCancellation

def sizeSq (y : Triple) : ℝ := (y 0)^2+(y 1)^2+(y 2)^2
def frame (y : Triple) : Fin 3 → ℝ := ![2*y 1,2*y 2,2*y 0]
def generator (y : Triple) : M2 := algebraElement (frame y)

theorem sizeSq_nonneg (y : Triple) : 0 ≤ sizeSq y := by unfold sizeSq; positivity

theorem rawPoint_matrix (y : Triple) :
    QuaternionSU2Representation.repr (rawPoint y)=1+generator y := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [QuaternionSU2Representation.repr,rawPoint,generator,frame,algebraElement,
      tangent,SU2TraceHessianModel.generator,generatorX,generatorY,generatorZ,
      Fin.sum_univ_three,Complex.mul_re,Complex.mul_im] <;> ring

theorem frame_smul (y : Triple) (t : ℝ) : frame (t • y)=t • frame y := by
  ext i
  fin_cases i <;> simp [frame] <;> ring

theorem rawPoint_matrix_smul (y : Triple) (t : ℝ) :
    QuaternionSU2Representation.repr (rawPoint (t • y))=1+t • generator y := by
  rw [rawPoint_matrix]
  unfold generator
  rw [frame_smul,algebraElement_smul]

theorem radius_smul (y : Triple) (t : ℝ) :
    radius (t • y)=Real.sqrt (1+t^2*sizeSq y) := by
  unfold radius chartRate sizeSq
  congr 1
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

def weight (y : Triple) (t : ℝ) : ℝ := (Real.sqrt (1+t^2*sizeSq y))⁻¹
def weightSlope (y : Triple) (t : ℝ) : ℝ := -t*sizeSq y*(weight y t)^3

theorem weight_zero (y : Triple) : weight y 0=1 := by simp [weight]

theorem weight_hasDerivAt (y : Triple) (t : ℝ) :
    HasDerivAt (weight y) (weightSlope y t) t := by
  have hp : 0 < 1+t^2*sizeSq y := by have hh := sizeSq_nonneg y; positivity
  have hs : Real.sqrt (1+t^2*sizeSq y) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have hb : HasDerivAt (fun u : ℝ => 1+u^2*sizeSq y) (2*t*sizeSq y) t := by
    convert! (((hasDerivAt_id t).pow 2).mul_const (sizeSq y)).const_add 1 using 1 <;> simp only [id_eq,Pi.mul_apply,Pi.pow_apply] <;> ring
  have hh := (hb.sqrt hp.ne').inv hs
  convert! hh using 1
  dsimp [weightSlope,weight]
  field_simp <;> ring

theorem weightSlope_hasDerivAt_zero (y : Triple) :
    HasDerivAt (weightSlope y) (-sizeSq y) 0 := by
  have hh := ((hasDerivAt_id (0 : ℝ)).mul_const (-sizeSq y)).mul
    ((weight_hasDerivAt y 0).pow 3)
  convert! hh using 1
  · funext t
    simp only [weightSlope,Pi.mul_apply,Pi.pow_apply,id_eq]
    ring
  · simp [weight_zero,weightSlope]

def curve (y : Triple) (t : ℝ) : M2 := (hemisphereChart (t • y) : M2)
def affine (y : Triple) (t : ℝ) : M2 := 1+t • generator y

def curveSlope (y : Triple) (t : ℝ) : M2 :=
  weightSlope y t • affine y t+weight y t • generator y

theorem curve_formula (y : Triple) (t : ℝ) : curve y t=weight y t • affine y t := by
  rw [curve,chart_matrix,rawPoint_matrix_smul,radius_smul]
  rfl

theorem affine_hasDerivAt (y : Triple) (t : ℝ) :
    HasDerivAt (affine y) (generator y) t := by
  convert! ((hasDerivAt_id t).smul_const (generator y)).const_add (1 : M2) using 1 <;>
    first | rfl | simp [affine,id_eq,one_smul]

theorem curve_hasDerivAt (y : Triple) (t : ℝ) :
    HasDerivAt (curve y) (curveSlope y t) t := by
  have he : curve y=(fun u => weight y u • affine y u) := funext (curve_formula y)
  rw [he]
  convert! (weight_hasDerivAt y t).smul (affine_hasDerivAt y t) using 1 <;>
    simp only [curveSlope,add_comm]

theorem curveSlope_hasDerivAt_zero (y : Triple) :
    HasDerivAt (curveSlope y) ((-sizeSq y) • (1 : M2)) 0 := by
  have hh := ((weightSlope_hasDerivAt_zero y).smul (affine_hasDerivAt y 0)).add
    ((weight_hasDerivAt y 0).smul_const (generator y))
  convert! hh using 1 <;> first | rfl | simp [curveSlope,weight_zero,weightSlope,affine]

theorem curve_zero (y : Triple) : curve y 0=1 := by
  rw [curve_formula]
  simp [weight_zero,affine]

theorem curve_first_zero (y : Triple) : deriv (curve y) 0=generator y := by
  convert! (curve_hasDerivAt y 0).deriv using 1 <;> first | rfl |
    simp [curveSlope,weightSlope,weight_zero,affine]

theorem curve_second_zero (y : Triple) :
    deriv (deriv (curve y)) 0=(-sizeSq y) • (1 : M2) := by
  have he : deriv (curve y)=curveSlope y := funext (fun t => (curve_hasDerivAt y t).deriv)
  rw [he]
  convert! (curveSlope_hasDerivAt_zero y).deriv using 1 <;> rfl

theorem lengthSq_frame (y : Triple) : lengthSq (frame y)=4*sizeSq y := by
  simp [lengthSq,frame,Fin.sum_univ_three,sizeSq]
  ring

theorem generator_square (y : Triple) :
    (generator y)^2=((-sizeSq y : ℝ) : ℂ) • (1 : M2) := by
  unfold generator
  rw [algebraElement_sq,lengthSq_frame]
  congr 1
  push_cast
  ring

theorem curve_second_generator (y : Triple) :
    deriv (deriv (curve y)) 0=(generator y)^2 := by
  rw [curve_second_zero,generator_square]
  rfl

theorem curve_two_jet (y : Triple) :
    curve y 0=NormedSpace.exp ((0 : ℝ) • generator y) ∧
      deriv (curve y) 0=deriv (fun t : ℝ => NormedSpace.exp (t • generator y)) 0 ∧
      deriv (deriv (curve y)) 0=
        deriv (deriv (fun t : ℝ => NormedSpace.exp (t • generator y))) 0 := by
  have he : deriv (fun t : ℝ => NormedSpace.exp (t • generator y))=
      (fun t => generator y*NormedSpace.exp (t • generator y)) := by
    funext t
    exact (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (generator y) t).deriv
  refine ⟨?_,?_,?_⟩
  · simp [curve_zero]
  · rw [he,curve_first_zero]
    simp
  · rw [he,curve_second_generator]
    have hh := ((hasDerivAt_exp_smul_const' (𝕂 := ℝ) (generator y) 0).const_mul (generator y)).deriv
    convert! hh.symm using 1 <;> simp [pow_two]

end OperatorDerivativeRewrite.Foundation.SU2HemisphereJets
