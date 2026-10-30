import Foundation.CubeGaussianCoordinateMeasure
import Foundation.SU2RootEuclideanMeasure

/-! Actual fixed-root Gaussian ground integrals for the five Schur channels. -/
noncomputable section
open MeasureTheory
open scoped Matrix
namespace OperatorDerivativeRewrite.Foundation.CubeGaussianChannelGround
open CubeGaussianModes SU2GaussianConeCoordinates SU2HemisphereJets
open QuaternionSU2Representation SU2RootEuclideanMeasure

def precision (i : Fin 5) : ℝ := weights i*(orders i+2)/4
def width (i : Fin 5) : ℝ := weights i*Real.sqrt (orders i*(orders i+4))/4
def ratio (i : Fin 5) : ℝ := weights i/(2*(precision i+width i))

theorem weights_positive (i : Fin 5) : 0 < weights i := by
  fin_cases i <;> norm_num [weights]

theorem orders_positive (i : Fin 5) : 0 < orders i := by
  fin_cases i <;> norm_num [orders]

theorem precision_positive (i : Fin 5) : 0 < precision i := by
  unfold precision
  have hw := weights_positive i
  have hm := orders_positive i
  positivity

theorem width_positive (i : Fin 5) : 0 < width i := by
  unfold width
  have hw := weights_positive i
  have hm := orders_positive i
  positivity

theorem width_relation (i : Fin 5) :
    (width i)^2=(precision i)^2-(weights i)^2/4 := by
  have hm : 0 ≤ orders i*(orders i+4) := by
    have h := orders_positive i
    positivity
  unfold width precision
  calc
    _ = (weights i)^2/16*(Real.sqrt (orders i*(orders i+4)))^2 := by ring
    _ = (weights i)^2/16*(orders i*(orders i+4)) := by rw [Real.sq_sqrt hm]
    _ = _ := by ring

private theorem ratio_linear (i : Fin 5) :
    (precision i+width i)*ratio i=weights i/2 := by
  have hp : precision i+width i ≠ 0 :=
    (add_pos (precision_positive i) (width_positive i)).ne'
  unfold ratio
  field_simp

private theorem ratio_square (i : Fin 5) :
    (precision i+width i)*(ratio i)^2=precision i-width i := by
  have hp : precision i+width i ≠ 0 :=
    (add_pos (precision_positive i) (width_positive i)).ne'
  apply mul_left_cancel₀ hp
  calc
    _ = ((precision i+width i)*ratio i)^2 := by ring
    _ = (weights i/2)^2 := by rw [ratio_linear]
    _ = (precision i+width i)*(precision i-width i) := by
      nlinarith [width_relation i]

private theorem shifted_square (x z : Triple) (r : ℝ) :
    sizeSq (z-r • x)=sizeSq z+r^2*sizeSq x-2*r*dotProduct x z := by
  simp [sizeSq,dotProduct,Fin.sum_univ_three]
  ring

theorem channel_completed (i : Fin 5) (x y : Triple) (c : SU2) :
    channel i x y c+width i*sizeSq y=width i*sizeSq x+
      (precision i+width i)*sizeSq (SU2RootAdjoint.rotate c y-ratio i • x) := by
  rw [channel_gaussian,← SU2RootAdjoint.rotate_sizeSq c y]
  change precision i*(sizeSq x+sizeSq (SU2RootAdjoint.rotate c y))-
    weights i*dotProduct x (SU2RootAdjoint.rotate c y)+
      width i*sizeSq (SU2RootAdjoint.rotate c y)=_
  rw [shifted_square]
  calc
    _ = width i*sizeSq x+(precision i+width i)*sizeSq (SU2RootAdjoint.rotate c y)+
        ((precision i+width i)*(ratio i)^2)*sizeSq x-
        2*((precision i+width i)*ratio i)*dotProduct x (SU2RootAdjoint.rotate c y) := by
      rw [ratio_square,ratio_linear]
      ring
    _ = _ := by ring

def gaussianMass (b : ℝ) : ℝ := ∫ y : Triple,Real.exp (-b*sizeSq y)

theorem gaussian_integrable (b : ℝ) (hb : 0 < b) :
    Integrable (fun y : Triple => Real.exp (-b*sizeSq y)) := by
  have h := SU2HaarLaplaceUpper.gaussian_integrable (4*b) (by positivity)
  convert h using 1
  funext y
  congr 1
  simp [chartRate,sizeSq]
  ring

theorem gaussianMass_positive (b : ℝ) (hb : 0 < b) : 0 < gaussianMass b :=
  integral_exp_pos (gaussian_integrable b hb)

theorem channel_ground_integral (i : Fin 5) (x : Triple) (c : SU2) :
    (∫ y : Triple,Real.exp (-channel i x y c)*Real.exp (-width i*sizeSq y))=
      Real.exp (-width i*sizeSq x)*gaussianMass (precision i+width i) := by
  have he (y : Triple) : Real.exp (-channel i x y c)*Real.exp (-width i*sizeSq y)=
      Real.exp (-width i*sizeSq x)*Real.exp (-(precision i+width i)*
        sizeSq (SU2RootAdjoint.rotate c y-ratio i • x)) := by
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    have h := channel_completed i x y c
    linarith
  simp_rw [he]
  rw [integral_const_mul,rotate_integral c
    (fun z : Triple => Real.exp (-(precision i+width i)*sizeSq (z-ratio i • x)))]
  rw [integral_sub_right_eq_self
    (fun z : Triple => Real.exp (-(precision i+width i)*sizeSq z)) (ratio i • x)]
  rfl

theorem channel_ground_integrable (i : Fin 5) (x : Triple) (c : SU2) :
    Integrable (fun y : Triple =>
      Real.exp (-channel i x y c)*Real.exp (-width i*sizeSq y)) := by
  by_contra hn
  have h := channel_ground_integral i x c
  rw [integral_undef hn] at h
  have hp := mul_pos (Real.exp_pos (-width i*sizeSq x))
    (gaussianMass_positive (precision i+width i)
      (add_pos (precision_positive i) (width_positive i)))
  linarith

def gaussianState (x : CubeChartAction.Boundary) : ℝ :=
  ∏ i : Fin 5,Real.exp (-width i*sizeSq (x i))

def stateMass : ℝ := ∏ i : Fin 5,gaussianMass (precision i+width i)

theorem fixed_root_ground_integral (x : CubeChartAction.Boundary) (c : SU2) :
    (∫ y : CubeChartAction.Boundary,(∏ i : Fin 5,Real.exp (-channel i (x i) (y i) c))*
      gaussianState y)=gaussianState x*stateMass := by
  unfold gaussianState stateMass
  simp_rw [← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_volume_eq_prod (fun (i : Fin 5) (y : Triple) =>
    Real.exp (-channel i (x i) y c)*Real.exp (-width i*sizeSq y))]
  simp_rw [channel_ground_integral]

theorem fixed_root_ground_integrable (x : CubeChartAction.Boundary) (c : SU2) :
    Integrable (fun y : CubeChartAction.Boundary =>
      (∏ i : Fin 5,Real.exp (-channel i (x i) (y i) c))*gaussianState y) := by
  unfold gaussianState
  simp_rw [← Finset.prod_mul_distrib]
  rw [volume_pi]
  exact Integrable.fintype_prod (fun i => channel_ground_integrable i (x i) c)

end OperatorDerivativeRewrite.Foundation.CubeGaussianChannelGround
