import Foundation.OneSidedGramSector
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic.Module

/-! Exact physical eigenvectors from the actual one-sided Gram sector. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.OneSidedQuadraticEigenvalues
open OneSidedBlockIncidence OneSidedBlockKernel OneSidedBlockRank OneSidedGramSector
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

def H : Field →ₗ[ℝ] Field := Matrix.toLin' gram

def eigenvector (ell : ℝ) : Field := (ell-9) • v+w

theorem H_v : H v=w := gram_v

theorem H_w : H w=(9 : ℝ) • w-(11 : ℝ) • v := gram_w

theorem H_eigenvector (ell : ℝ) (hq : ell^2-9*ell+11=0) :
    H (eigenvector ell)=ell • eigenvector ell := by
  have hc : ell*(ell-9)=(-11 : ℝ) := by nlinarith
  unfold eigenvector
  calc
    H ((ell-9) • v+w)=(ell-9) • w+((9 : ℝ) • w-(11 : ℝ) • v) := by
      rw [map_add,map_smul,H_v,H_w]
    _ = ell • w+(-11 : ℝ) • v := by module
    _ = ell • ((ell-9) • v+w) := by rw [← hc]; module

theorem eigenvector_nonzero (ell : ℝ) : eigenvector ell≠0 := by
  intro h
  have hz : (ell-9) • v+(1 : ℝ) • w=0 := by simpa only [one_smul,eigenvector] using h
  have hi := sector_independent (ell-9) 1 hz
  norm_num at hi

theorem eigenvector_is_eigen (ell : ℝ) (hq : ell^2-9*ell+11=0) :
    Module.End.HasEigenvector H ell (eigenvector ell) := by
  rw [Module.End.hasEigenvector_iff,Module.End.mem_eigenspace_iff]
  exact ⟨H_eigenvector ell hq,eigenvector_nonzero ell⟩

def lowerRoot : ℝ := (9-Real.sqrt 37)/2
def upperRoot : ℝ := (9+Real.sqrt 37)/2

theorem lowerRoot_quadratic : lowerRoot^2-9*lowerRoot+11=0 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤37)
  unfold lowerRoot
  nlinarith

theorem upperRoot_quadratic : upperRoot^2-9*upperRoot+11=0 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤37)
  unfold upperRoot
  nlinarith

theorem lower_hasEigenvalue : Module.End.HasEigenvalue H lowerRoot :=
  Module.End.hasEigenvalue_of_hasEigenvector (eigenvector_is_eigen lowerRoot lowerRoot_quadratic)

theorem upper_hasEigenvalue : Module.End.HasEigenvalue H upperRoot :=
  Module.End.hasEigenvalue_of_hasEigenvector (eigenvector_is_eigen upperRoot upperRoot_quadratic)

theorem intV_origin : ∀ i : Fin 4, intV (origin,i)=0 := by decide

theorem intW_origin : ∀ i : Fin 4, intW (origin,i)=0 := by decide

theorem sector_physical (a b : ℝ) : OrthogonalToGauge (extend (a • v+b • w)) := by
  unfold OrthogonalToGauge
  apply Finset.sum_eq_zero
  intro e he
  by_cases ho : e.1=origin
  · rcases e with ⟨x,i⟩
    change x=origin at ho
    subst x
    simp [extend,he,Pi.add_apply,Pi.smul_apply,smul_eq_mul,v,w,intV_origin,intW_origin]
  · simp [originField,originStar,ho]

theorem eigenvector_physical (ell : ℝ) : OrthogonalToGauge (extend (eigenvector ell)) := by
  simpa only [one_smul,eigenvector] using sector_physical (ell-9) 1

theorem upperRoot_bounds : (754135/100000 : ℝ)<upperRoot ∧ upperRoot<(754145/100000 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤37)
  have hn := Real.sqrt_nonneg (37 : ℝ)
  unfold upperRoot
  constructor <;> nlinarith

theorem lowerRoot_bounds : (145855/100000 : ℝ)<lowerRoot ∧ lowerRoot<(145865/100000 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤37)
  have hn := Real.sqrt_nonneg (37 : ℝ)
  unfold lowerRoot
  constructor <;> nlinarith

theorem roots_positive : 0<lowerRoot ∧ 0<upperRoot := by
  constructor <;> linarith [lowerRoot_bounds.1,upperRoot_bounds.1]

theorem roots_distinct : lowerRoot≠upperRoot := by
  intro h
  linarith [lowerRoot_bounds.2,upperRoot_bounds.1]

theorem upperRoot_outside_reported_rounding : upperRoot<(754175/100000 : ℝ) := by
  linarith [upperRoot_bounds.2]

end OperatorDerivativeRewrite.Foundation.OneSidedQuadraticEigenvalues
