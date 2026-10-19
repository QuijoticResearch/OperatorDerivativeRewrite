import Foundation.RiemannQuarticKernel
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven

/-! Actual theta-series derivatives and the arithmetic differential identity
behind the Xi Fourier kernel. -/
noncomputable section
open MeasureTheory Filter Set Real
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannThetaDifferentiation
open RiemannQuarticKernel

theorem thetaTerm_hasDerivAt (k n : ℕ) (v : ℝ) :
    HasDerivAt (fun w => thetaTerm k w n) (-Real.pi*thetaTerm (k+2) v n) v := by
  have h := (((hasDerivAt_id v).const_mul (-Real.pi*((n : ℝ)+1)^2)).exp).const_mul
    (((n : ℝ)+1)^k)
  convert h using 1
  · rfl
  · simp only [thetaTerm, pow_add, id_eq]
    ring

theorem thetaMoment_hasDerivAt (k : ℕ) (v : ℝ) (hv : 0 < v) :
    HasDerivAt (thetaMoment k) (-Real.pi*thetaMoment (k+2) v) v := by
  have hb := (thetaTerm_summable (k+2) (v/2) (half_pos hv)).mul_left Real.pi
  have h := hasDerivAt_tsum_of_isPreconnected
    (g := fun n w => thetaTerm k w n)
    (g' := fun n w => -Real.pi*thetaTerm (k+2) w n)
    (t := Ioi (v/2)) (y₀ := v) hb isOpen_Ioi (convex_Ioi (v/2)).isPreconnected
    (fun n w _ => thetaTerm_hasDerivAt k n w) ?_
    (by change v/2 < v; linarith) (thetaTerm_summable k v hv) (by change v/2 < v; linarith)
  · simpa only [thetaMoment, tsum_mul_left] using! h
  · intro n w hw
    rw [norm_mul, Real.norm_eq_abs, abs_neg, abs_of_pos Real.pi_pos,
      Real.norm_eq_abs, abs_of_nonneg (thetaTerm_nonneg _ _ _)]
    exact mul_le_mul_of_nonneg_left (thetaTerm_antitone (k+2) n hw.le) Real.pi_pos.le

theorem thetaMoment_exp_hasDerivAt (k : ℕ) (u : ℝ) :
    HasDerivAt (fun w => thetaMoment k (exp (4*w)))
      (-4*Real.pi*exp (4*u)*thetaMoment (k+2) (exp (4*u))) u := by
  have h := (thetaMoment_hasDerivAt k (exp (4*u)) (exp_pos _)).comp u
    (((hasDerivAt_id u).const_mul 4).exp)
  convert h using 1 <;> first | rfl | (simp only [id_eq]; ring)

def psi (u : ℝ) : ℝ := exp u*thetaMoment 0 (exp (4*u))

def psiPrime (u : ℝ) : ℝ := psi u-4*Real.pi*exp (5*u)*thetaMoment 2 (exp (4*u))

def psiSecond (u : ℝ) : ℝ := psi u-24*Real.pi*exp (5*u)*thetaMoment 2 (exp (4*u))+
  16*Real.pi^2*exp (9*u)*thetaMoment 4 (exp (4*u))

theorem psi_hasDerivAt (u : ℝ) : HasDerivAt psi (psiPrime u) u := by
  have h := (Real.hasDerivAt_exp u).mul (thetaMoment_exp_hasDerivAt 0 u)
  convert h using 1
  · rfl
  · simp only [psiPrime, psi, zero_add]
    rw [show 5*u=u+4*u by ring, exp_add]
    ring

theorem psiPrime_hasDerivAt (u : ℝ) : HasDerivAt psiPrime (psiSecond u) u := by
  have h := (psi_hasDerivAt u).sub
    (((((hasDerivAt_id u).const_mul 5).exp).const_mul (4*Real.pi)).mul
      (thetaMoment_exp_hasDerivAt 2 u))
  convert h using 1
  · rfl
  · simp only [psiSecond, psiPrime, psi, id_eq]
    rw [show 9*u=5*u+4*u by ring, exp_add]
    ring

theorem kernel_differential_identity (u : ℝ) :
    kernel u = (psiSecond u-psi u)/8 := by
  unfold kernel psiSecond
  ring

theorem psi_second_derivative (u : ℝ) : deriv (deriv psi) u = psiSecond u := by
  have he : deriv psi = psiPrime := funext fun x => (psi_hasDerivAt x).deriv
  rw [he]
  exact (psiPrime_hasDerivAt u).deriv

theorem kernel_eq_actual_second_derivative (u : ℝ) :
    kernel u = (deriv (deriv psi) u-psi u)/8 := by
  rw [psi_second_derivative]
  exact kernel_differential_identity u

theorem thetaMoment_zero_eq_cosKernel (v : ℝ) (hv : 0 < v) :
    thetaMoment 0 v = (HurwitzZeta.cosKernel 0 v-1)/2 := by
  have h := HurwitzZeta.hasSum_nat_cosKernel₀ 0 hv
  have hs := (thetaTerm_summable 0 v hv).hasSum.mul_left 2
  have he : (fun n : ℕ => 2*thetaTerm 0 v n) =
      (fun n : ℕ => 2*Real.cos (2*Real.pi*0*(n+1))*exp (-Real.pi*(n+1)^2*v)) := by
    funext n
    simp [thetaTerm]
  rw [he] at hs
  have hh := hs.unique h
  dsimp [thetaMoment] at hh ⊢
  linarith

end OperatorDerivativeRewrite.Foundation.RiemannThetaDifferentiation
