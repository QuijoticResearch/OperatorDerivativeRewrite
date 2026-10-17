import Foundation.GaussianPeriodicHeat
import Mathlib.Analysis.Calculus.FDeriv.Partial

/-! Joint smoothness of the actual Gaussian heat jets on their positive-parameter domain. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OperatorDerivativeRewrite.Foundation.GaussianJointHeatSmooth
open GaussianFourierJets GaussianPeriodicHeat

def domain : Set (ℝ × ℝ) := {p | 0 < p.1}

def joint (k : ℕ) (p : ℝ × ℝ) : ℝ := jet k p.1 p.2

def jointDerivative (k : ℕ) (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  joint (k+2) p • ContinuousLinearMap.fst ℝ ℝ ℝ +
    joint (k+1) p • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem domain_open : IsOpen domain := isOpen_lt continuous_const continuous_fst

theorem joint_continuous (k : ℕ) : ContinuousOn (joint k) domain := by
  intro p hp
  exact (jet_joint_continuous k p.1 p.2 hp).continuousWithinAt

theorem joint_hasFDeriv (k : ℕ) (p : ℝ × ℝ) (hp : p ∈ domain) :
    HasFDerivAt (joint k) (jointDerivative k p) p := by
  have he : ∀ᶠ v : ℝ × ℝ in 𝓝 p, 0 < v.1 :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds hp
  have hc (m : ℕ) : ContinuousAt
      (fun v : ℝ × ℝ => (1 : ℝ →L[ℝ] ℝ).smulRight (jet m v.1 v.2)) p := by
    have heq : (fun v : ℝ × ℝ => (1 : ℝ →L[ℝ] ℝ).smulRight (jet m v.1 v.2))=
        (fun v => (jet m v.1 v.2) • (1 : ℝ →L[ℝ] ℝ)) := by
      funext v
      apply ContinuousLinearMap.ext
      intro x
      simp [smul_eq_mul,mul_comm]
    rw [heq]
    exact (jet_joint_continuous m p.1 p.2 hp).smul continuousAt_const
  have h := hasStrictFDerivAt_uncurry_coprod
    (f := fun s y : ℝ => jet k s y)
    (f₁ := fun s y => (1 : ℝ →L[ℝ] ℝ).smulRight (jet (k+2) s y))
    (f₂ := fun s y => (1 : ℝ →L[ℝ] ℝ).smulRight (jet (k+1) s y))
    (u := p)
    (he.mono fun v hv => (parameter_derivative k v.1 hv v.2).hasFDerivAt)
    (he.mono fun v hv => (jet_derivative k v.1 hv v.2).hasFDerivAt)
    (hc (k+2))
    (hc (k+1))
  have hd : ((1 : ℝ →L[ℝ] ℝ).smulRight (jet (k+2) p.1 p.2)).coprod
      ((1 : ℝ →L[ℝ] ℝ).smulRight (jet (k+1) p.1 p.2))=jointDerivative k p := by
    apply ContinuousLinearMap.ext
    intro v
    simp [jointDerivative,joint,ContinuousLinearMap.coprod_apply,smul_eq_mul,mul_comm]
  change HasStrictFDerivAt (joint k)
    (((1 : ℝ →L[ℝ] ℝ).smulRight (jet (k+2) p.1 p.2)).coprod
      ((1 : ℝ →L[ℝ] ℝ).smulRight (jet (k+1) p.1 p.2))) p at h
  rw [hd] at h
  exact h.hasFDerivAt

theorem joint_smooth_nat (n k : ℕ) : ContDiffOn ℝ n (joint k) domain := by
  induction n generalizing k with
  | zero => exact contDiffOn_zero.mpr (joint_continuous k)
  | succ n ih =>
    have hd : ContDiffOn ℝ n (jointDerivative k) domain :=
      ((ih (k+2)).smul contDiffOn_const).add ((ih (k+1)).smul contDiffOn_const)
    have hh : ContDiffOn ℝ ((n : ℕ∞ω)+1) (joint k) domain := by
      apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
        (𝕜 := ℝ) (n := (n : ℕ∞ω)) (f := joint k) (s := domain) domain_open.uniqueDiffOn).2
      refine ⟨by simp, jointDerivative k,hd,?_⟩
      intro p hp
      exact (joint_hasFDeriv k p hp).hasFDerivWithinAt
    simpa only [Nat.cast_add,Nat.cast_one] using hh

theorem joint_smooth (k : ℕ) : ContDiffOn ℝ ∞ (joint k) domain :=
  contDiffOn_infty.mpr (fun n => joint_smooth_nat n k)

end OperatorDerivativeRewrite.Foundation.GaussianJointHeatSmooth
