import Foundation.GaussianTimeSpaceHermite
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Variance-two Hermite polynomials for quadratic-flow parabolic scaling.
The existing Gaussian time-space polynomials are evaluated on the complex plane.
A positive finite Christoffel-Darboux energy proves all roots real; lowering and
absence of consecutive common roots prove simplicity. This supporting theorem
does not assert a parabolic limit or zero splitting for the actual Xi flow. -/
noncomputable section
open Complex MvPolynomial
open scoped ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuadraticHermite

def value (n : ℕ) (z : ℂ) : ℂ :=
  MvPolynomial.aeval (fun _ : Unit => z) (GaussianTimeSpaceHermite.polynomial 2 n)

@[simp] theorem value_zero (z : ℂ) : value 0 z = 1 := by simp [value]
@[simp] theorem value_one (z : ℂ) : value 1 z = z := by simp [value]

theorem value_recursion (n : ℕ) (z : ℂ) :
    value (n+2) z = z*value (n+1) z-2*((n : ℂ)+1)*value n z := by
  simp [value,GaussianTimeSpaceHermite.polynomial_recursion,Algebra.smul_def]
  <;> (ring_nf <;> simp)

def energy : ℕ → ℂ → ℝ
  | 0,_ => 1
  | n+1,z => ‖value (n+1) z‖^2+2*((n : ℝ)+1)*energy n z

theorem energy_pos (n : ℕ) (z : ℂ) : 0 < energy n z := by
  induction n with
  | zero => norm_num [energy]
  | succ n ih =>
    simp only [energy]
    positivity

theorem christoffel_darboux (n : ℕ) (z : ℂ) :
    value (n+1) z*conj (value n z)-value n z*conj (value (n+1) z) =
      (z-conj z)*(energy n z : ℂ) := by
  induction n with
  | zero => simp [energy]
  | succ n ih =>
    have hr : value (n+1+1) z =
        z*value (n+1) z-2*((n : ℂ)+1)*value n z := by
      simpa only [Nat.add_assoc] using value_recursion n z
    simp only [hr,map_sub,map_mul,map_add,map_ofNat,map_natCast,map_one]
    simp only [energy]
    push_cast
    have hn := Complex.mul_conj' (value (n+1) z)
    linear_combination (2*((n : ℂ)+1))*ih + (z-conj z)*hn

theorem roots_real_succ (n : ℕ) (z : ℂ) (hz : value (n+1) z = 0) : z.im = 0 := by
  have hc := christoffel_darboux n z
  have hc0 : (z-conj z)*(energy n z : ℂ)=0 := by
    simpa only [hz,map_zero,zero_mul,mul_zero,sub_self] using hc.symm
  have he : (energy n z : ℂ) ≠ 0 := by exact_mod_cast (energy_pos n z).ne'
  have hdiff : z-conj z=0 := (mul_eq_zero.mp hc0).resolve_right he
  have hi := congrArg Complex.im hdiff
  simp only [Complex.sub_im,Complex.conj_im,Complex.zero_im] at hi
  linarith

theorem roots_real (n : ℕ) (z : ℂ) (hz : value n z = 0) : z.im = 0 := by
  cases n with
  | zero => simp at hz
  | succ n => exact roots_real_succ n z hz

theorem no_consecutive_roots (n : ℕ) (z : ℂ) :
    ¬ (value n z=0 ∧ value (n+1) z=0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rintro ⟨hn,hnext⟩
    have hr := value_recursion n z
    have hc : 2*((n : ℂ)+1) ≠ 0 := by
      have hh : (2*(n+1) : ℕ) ≠ 0 := by omega
      exact_mod_cast hh
    have hm : (2*((n : ℂ)+1))*value n z=0 := by
      linear_combination hr-hnext+z*hn
    exact ih ⟨(mul_eq_zero.mp hm).resolve_left hc,hn⟩

private theorem hasDerivAt_aeval_unit (p : MvPolynomial Unit ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => MvPolynomial.aeval (fun _ : Unit => w) p)
      (MvPolynomial.aeval (fun _ : Unit => z) (pderiv () p)) z := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using hasDerivAt_const z (c : ℂ)
  | add p q hp hq => simpa [Pi.add_def] using hp.add hq
  | mul_X p i hp =>
    cases i
    simpa [MvPolynomial.pderiv_mul,Pi.mul_def,mul_comm,add_comm] using
      hp.mul (hasDerivAt_id z)

theorem value_hasDerivAt (n : ℕ) (z : ℂ) :
    HasDerivAt (value (n+1)) (((n : ℂ)+1)*value n z) z := by
  have h := hasDerivAt_aeval_unit (GaussianTimeSpaceHermite.polynomial 2 (n+1)) z
  change HasDerivAt
    (fun w : ℂ => MvPolynomial.aeval (fun _ : Unit => w)
      (GaussianTimeSpaceHermite.polynomial 2 (n+1)))
    (((n : ℂ)+1)*MvPolynomial.aeval (fun _ : Unit => z)
      (GaussianTimeSpaceHermite.polynomial 2 n)) z
  simpa [GaussianTimeSpaceHermite.polynomial_derivative,Algebra.smul_def] using h

theorem derivative_ne_zero_at_root (n : ℕ) (z : ℂ)
    (hz : value (n+1) z = 0) : deriv (value (n+1)) z ≠ 0 := by
  rw [(value_hasDerivAt n z).deriv]
  apply mul_ne_zero
  · exact_mod_cast (Nat.succ_ne_zero n)
  · intro hn
    exact no_consecutive_roots n z ⟨hn,hz⟩

end OperatorDerivativeRewrite.Foundation.RiemannQuadraticHermite
