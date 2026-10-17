import Foundation.RestrictedEulerArbitraryDepletion
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Actual derivatives of affine velocity and quadratic pressure profiles.
These growing spatial fields are not asserted to have finite energy. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.AffineNavierStokesProfiles
open RestrictedEulerRatioCounterexample RestrictedEulerAlignedGrowth
  RestrictedEulerSpectralDistinction
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

abbrev Space := Fin 3 → ℝ

def spatialMap (p a : ℝ) : Space →L[ℝ] Space :=
  (Matrix.toLin' (matrix p a)).toContinuousLinearMap

theorem spatialMap_apply (p a : ℝ) (x : Space) :
    spatialMap p a x=(matrix p a).mulVec x := rfl

def velocity (p a t : ℝ) (x : Space) : Space := scale t • spatialMap p a x
def pressure (t : ℝ) (x : Space) : ℝ := -(scale t)^2*∑ i, (x i)^2

def advection (u : Space → Space) (x : Space) : Space := fderiv ℝ u x (u x)
def divergence (u : Space → Space) (x : Space) : ℝ :=
  ∑ i, fderiv ℝ u x (Pi.single i 1) i
def laplacian (u : Space → Space) (x : Space) : Space :=
  ∑ i, fderiv ℝ (fun y => fderiv ℝ u y) x (Pi.single i 1) (Pi.single i 1)

def pressureGradient (t : ℝ) (x : Space) (j : Fin 3) : ℝ :=
  deriv (fun s => pressure t (Function.update x j s)) (x j)
def pressureHessian (t : ℝ) (x : Space) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => deriv (fun s => pressureGradient t (Function.update x j s) i) (x j)

theorem velocity_fderiv (p a t : ℝ) (x : Space) :
    fderiv ℝ (velocity p a t) x=scale t • spatialMap p a :=
  ((scale t) • spatialMap p a).hasFDerivAt.fderiv

theorem velocity_second_fderiv (p a t : ℝ) (x : Space) :
    fderiv ℝ (fun y => fderiv ℝ (velocity p a t) y) x=0 := by
  have he : (fun y => fderiv ℝ (velocity p a t) y)=fun _ => scale t • spatialMap p a :=
    funext (velocity_fderiv p a t)
  rw [he]
  simp

theorem velocity_laplacian (p a t : ℝ) (x : Space) : laplacian (velocity p a t) x=0 := by
  simp only [laplacian,velocity_second_fderiv,ContinuousLinearMap.zero_apply,Finset.sum_const_zero]

theorem velocity_divergence (p a t : ℝ) (x : Space) : divergence (velocity p a t) x=0 := by
  simp only [divergence,velocity_fderiv,ContinuousLinearMap.smul_apply,spatialMap_apply,
    Matrix.mulVec_single_one,Matrix.col_apply,Pi.smul_apply,smul_eq_mul]
  rw [← Finset.mul_sum]
  change scale t*Matrix.trace (matrix p a)=0
  rw [matrix_trace,mul_zero]

theorem velocity_time_derivative (p a t : ℝ) (x : Space) (ht : t ≠ 1) :
    HasDerivAt (fun s => velocity p a s x) ((scale t)^2 • spatialMap p a x) t :=
  (scale_derivative t ht).smul_const _

theorem velocity_advection (p a t : ℝ) (x : Space) :
    advection (velocity p a t) x=
      (scale t)^2 • (matrix p a).mulVec ((matrix p a).mulVec x) := by
  rw [advection,velocity_fderiv,velocity]
  simp only [ContinuousLinearMap.smul_apply,map_smul,spatialMap_apply]
  rw [smul_smul,pow_two]

theorem pressure_partial (t : ℝ) (x : Space) (j : Fin 3) :
    pressureGradient t x j=-2*(scale t)^2*x j := by
  have hk (k : Fin 3) : HasDerivAt (fun s : ℝ => (Function.update x j s k)^2)
      (if k=j then 2*x j else 0) (x j) := by
    by_cases h : k=j
    · subst k
      simpa using hasDerivAt_pow 2 (x j)
    · simpa [h,Ne.symm h] using hasDerivAt_const (x j) ((x k)^2)
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => hk k)
  have hd := hs.const_mul (-(scale t)^2)
  have he : (∑ k : Fin 3, if k=j then 2*x j else 0)=2*x j := by simp
  rw [he] at hd
  have hd' := hd.congr_deriv (g' := -2*(scale t)^2*x j) (by ring)
  exact hd'.deriv

theorem pressure_gradient (t : ℝ) (x : Space) :
    pressureGradient t x=(-2*(scale t)^2) • x := by
  ext j
  exact pressure_partial t x j

theorem pressure_hessian_entry (t : ℝ) (x : Space) (i j : Fin 3) :
    pressureHessian t x i j=if i=j then -2*(scale t)^2 else 0 := by
  unfold pressureHessian
  simp_rw [pressure_partial]
  by_cases h : i=j
  · subst i
    simpa using ((hasDerivAt_id (x j)).const_mul (-2*(scale t)^2)).deriv
  · simpa [h,Ne.symm h] using deriv_const (x j) (-2*(scale t)^2*x i)

theorem pressure_hessian (t : ℝ) (x : Space) :
    pressureHessian t x=(-2*(scale t)^2) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  rw [pressure_hessian_entry]
  by_cases h : i=j <;> simp [h,Matrix.one_apply]

theorem profile_action (p a : ℝ) (ha : a^2=(p-2)*(p+1)) (x : Space) :
    (matrix p a).mulVec x+(matrix p a).mulVec ((matrix p a).mulVec x)=(2 : ℝ) • x := by
  have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A.mulVec x) (profile_polynomial p a ha)
  simp only [Matrix.add_mulVec,← Matrix.mulVec_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec] at h
  simpa only [add_comm] using h

theorem momentum (p a t ν : ℝ) (ha : a^2=(p-2)*(p+1)) (ht : t ≠ 1) (x : Space) :
    deriv (fun s => velocity p a s x) t+advection (velocity p a t) x+pressureGradient t x=
      ν • laplacian (velocity p a t) x := by
  rw [(velocity_time_derivative p a t x ht).deriv,velocity_advection,pressure_gradient,
    velocity_laplacian,smul_zero,spatialMap_apply,← smul_add,profile_action p a ha x]
  rw [smul_smul]
  module

theorem pressure_poisson (p a t : ℝ) (ha : a^2=(p-2)*(p+1)) (x : Space) :
    -Matrix.trace (pressureHessian t x)=Matrix.trace (family p a t*family p a t) := by
  have hs : Matrix.trace (family p a t*family p a t)=
      (scale t)^2*Matrix.trace (matrix p a*matrix p a) := by
    simp [family,Matrix.trace,Matrix.diag,Matrix.mul_apply,Fin.sum_univ_succ] <;> ring
  rw [hs,trace_square p a ha,pressure_hessian]
  norm_num [Matrix.trace,Matrix.diag,Fin.sum_univ_succ] <;> ring

theorem velocity_middle_coordinate (p a t : ℝ) (x : Space) :
    velocity p a t x 1=scale t*x 1 := by
  simp [velocity,spatialMap_apply,matrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem velocity_not_periodic (p a t : ℝ) (ht : t ≠ 1) :
    ¬ ∀ x : Space, velocity p a t (x+Pi.single 1 1)=velocity p a t x := by
  intro h
  have he := congrFun (h 0) 1
  have hc : scale t ≠ 0 := inv_ne_zero (sub_ne_zero.mpr (Ne.symm ht))
  simp [velocity_middle_coordinate] at he
  exact hc he

theorem velocity_spatially_unbounded (p a t B : ℝ) (ht : t < 1) :
    ∃ x : Space, B < velocity p a t x 1 := by
  have hc : 0 < scale t := inv_pos.mpr (sub_pos.mpr ht)
  refine ⟨Pi.single 1 ((B+1)/scale t),?_⟩
  rw [velocity_middle_coordinate]
  simp only [Pi.single_eq_same]
  have he : scale t*((B+1)/scale t)=B+1 := by field_simp
  rw [he]
  linarith

end OperatorDerivativeRewrite.Foundation.AffineNavierStokesProfiles
