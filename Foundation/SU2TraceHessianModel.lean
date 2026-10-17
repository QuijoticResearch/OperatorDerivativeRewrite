import Foundation.ChristoffelSkewCancellation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Normalized SU(2) generators and an explicit symmetric Wilson trace model. -/
noncomputable section
open scoped Matrix
namespace OperatorDerivativeRewrite.Foundation.SU2TraceHessianModel
set_option backward.isDefEq.respectTransparency false
open ChristoffelSkewCancellation

abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ
def generator (a : Fin 3) : M2 := if a=0 then generatorX else if a=1 then generatorY else generatorZ
def tangent (a : Fin 3) : M2 := (1/2:ℂ) • generator a
def traceReal (U : M2) : ℝ := (Matrix.trace U).re

theorem tangent_skewHermitian (a : Fin 3) : (tangent a)ᴴ= -tangent a := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [tangent, generator, generatorX, generatorY, generatorZ, Matrix.conjTranspose_apply]

theorem tangent_trace_zero (a : Fin 3) : Matrix.trace (tangent a)=0 := by
  fin_cases a <;> norm_num [tangent, generator, generatorX, generatorY, generatorZ,
    Matrix.trace_fin_two]

theorem tangent_jordan (a b : Fin 3) :
    tangent a*tangent b+tangent b*tangent a=if a=b then -(1/2:ℂ) • (1:M2) else 0 := by
  fin_cases a <;> fin_cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [tangent, generator, generatorX, generatorY, generatorZ, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring_nf <;> norm_num [Complex.I_sq]

theorem trace_metric_normalization (a b : Fin 3) :
    -2*traceReal (tangent a*tangent b)=if a=b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [traceReal, tangent, generator, generatorX, generatorY, generatorZ,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Complex.mul_re, Complex.mul_im]

theorem generatorZ_metric_sq : -2*traceReal (generatorZ*generatorZ)=4 := by
  norm_num [traceReal, generatorZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two]

def rawSecond (U : M2) (a b : Fin 3) : ℝ := -(1/2:ℝ)*traceReal (U*tangent a*tangent b)
def connectionTerm (U : M2) (a b : Fin 3) : ℝ :=
  -(1/4:ℝ)*traceReal (U*(tangent a*tangent b-tangent b*tangent a))
def frameModel (U : M2) (a b : Fin 3) : ℝ := rawSecond U a b-connectionTerm U a b

theorem frameModel_jordan (U : M2) (a b : Fin 3) :
    frameModel U a b= -(1/4:ℝ)*traceReal (U*(tangent a*tangent b+tangent b*tangent a)) := by
  unfold frameModel rawSecond connectionTerm traceReal
  simp only [mul_sub, mul_add, Matrix.trace_sub, Matrix.trace_add, Complex.sub_re,
    Complex.add_re, Matrix.mul_assoc]
  ring

theorem frameModel_exact (U : M2) (a b : Fin 3) :
    frameModel U a b=if a=b then traceReal U/8 else 0 := by
  rw [frameModel_jordan, tangent_jordan]
  by_cases hab : a=b
  · simp only [if_pos hab, mul_smul_comm, mul_one, traceReal, Matrix.trace_smul, smul_eq_mul]
    norm_num [Complex.mul_re]
    ring
  · simp [hab, traceReal]

def quadratic (U : M2) (v : Fin 3 → ℝ) : ℝ := ∑ a, ∑ b, v a*frameModel U a b*v b

theorem quadratic_exact (U : M2) (v : Fin 3 → ℝ) :
    quadratic U v=(traceReal U/8)*(∑ a, (v a)^2) := by
  have hi (a : Fin 3) : (∑ b, v a*frameModel U a b*v b)=(traceReal U/8)*(v a)^2 := by
    rw [Finset.sum_eq_single a]
    · rw [frameModel_exact, if_pos rfl]
      ring
    · intro b hb hba
      rw [frameModel_exact, if_neg (Ne.symm hba)]
      ring
    · simp
  unfold quadratic
  simp_rw [hi]
  exact (Finset.mul_sum _ _ _).symm

def rotation (θ : ℝ) : M2 := (Real.cos θ : ℂ) • (1:M2)+(Real.sin θ : ℂ) • generatorZ

theorem rotation_unitary (θ : ℝ) : (rotation θ)ᴴ*rotation θ=1 ∧ rotation θ*(rotation θ)ᴴ=1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [rotation, generatorZ, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im] <;>
    simp only [Complex.cos_ofReal_re, Complex.sin_ofReal_re] <;>
    nlinarith [Real.sin_sq_add_cos_sq θ]

theorem rotation_det_one (θ : ℝ) : Matrix.det (rotation θ)=1 := by
  rw [Matrix.det_fin_two]
  apply Complex.ext <;>
    norm_num [rotation, generatorZ, Complex.mul_re, Complex.mul_im] <;>
    simp only [Complex.cos_ofReal_re, Complex.sin_ofReal_re] <;>
    nlinarith [Real.sin_sq_add_cos_sq θ]

theorem rotation_trace (θ : ℝ) : traceReal (rotation θ)=2*Real.cos θ := by
  norm_num [traceReal, rotation, generatorZ, Matrix.trace_fin_two]
  simp only [Complex.cos_ofReal_re]
  ring

theorem quadratic_rotation (θ : ℝ) (v : Fin 3 → ℝ) :
    quadratic (rotation θ) v=(Real.cos θ/4)*(∑ a, (v a)^2) := by
  rw [quadratic_exact, rotation_trace]
  ring

theorem quadratic_rotation_lower (θ : ℝ) (v : Fin 3 → ℝ) (c : ℝ) (hc : c≤Real.cos θ) :
    (c/4)*(∑ a, (v a)^2)≤quadratic (rotation θ) v := by
  rw [quadratic_rotation]
  have hs : 0≤∑ a, (v a)^2 := Finset.sum_nonneg (fun a _ => sq_nonneg (v a))
  nlinarith

theorem rotation_add (θ φ : ℝ) : rotation (θ+φ)=rotation θ*rotation φ := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [rotation, generatorZ, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re,
      Complex.mul_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
      Real.cos_add, Real.sin_add] <;> ring

def wilson (U : M2) : ℝ := 1-traceReal U/2
def axisCurve (θ t : ℝ) : ℝ := wilson (rotation θ*rotation (t/2))

theorem axisCurve_eq (θ t : ℝ) : axisCurve θ t=1-Real.cos (θ+t/2) := by
  unfold axisCurve wilson
  rw [← rotation_add, rotation_trace]
  ring

theorem axisCurve_hasDerivAt (θ t : ℝ) :
    HasDerivAt (axisCurve θ) (Real.sin (θ+t/2)/2) t := by
  have he : axisCurve θ=(fun s : ℝ => 1-Real.cos (θ+s/2)) := funext (axisCurve_eq θ)
  rw [he]
  have hi := (hasDerivAt_const t θ).add ((hasDerivAt_id t).div_const 2)
  have hh := (hasDerivAt_const t (1:ℝ)).sub ((Real.hasDerivAt_cos (θ+t/2)).comp t hi)
  convert hh using 1 <;> first | rfl | (funext s; rfl) | ring

theorem axisSlope_hasDerivAt (θ t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.sin (θ+s/2)/2) (Real.cos (θ+t/2)/4) t := by
  have hi := (hasDerivAt_const t θ).add ((hasDerivAt_id t).div_const 2)
  have hh := ((Real.hasDerivAt_sin (θ+t/2)).comp t hi).div_const 2
  convert hh using 1 <;> first | rfl | (funext s; rfl) | ring

theorem axisCurve_second_derivative (θ : ℝ) : deriv (deriv (axisCurve θ)) 0=Real.cos θ/4 := by
  have he : deriv (axisCurve θ)=(fun t : ℝ => Real.sin (θ+t/2)/2) :=
    funext (fun t => (axisCurve_hasDerivAt θ t).deriv)
  rw [he]
  simpa using (axisSlope_hasDerivAt θ 0).deriv

theorem axisCurve_model_match (θ : ℝ) :
    deriv (deriv (axisCurve θ)) 0=quadratic (rotation θ) (Pi.single (2 : Fin 3) (1:ℝ)) := by
  rw [axisCurve_second_derivative, quadratic_rotation]
  norm_num [Fin.sum_univ_three, Pi.single_apply]

end OperatorDerivativeRewrite.Foundation.SU2TraceHessianModel
