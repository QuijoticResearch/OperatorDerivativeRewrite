import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.Real.Pi.Bounds

/-! The literal arithmetic kernel in the quartic manuscripts.  This module
does not assume a Fourier representation of the completed zeta function. -/
noncomputable section
open MeasureTheory Filter Set Real
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticKernel

def thetaTerm (k : ℕ) (v : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ)+1)^k * exp (-Real.pi*((n : ℝ)+1)^2*v)

def thetaMoment (k : ℕ) (v : ℝ) : ℝ := ∑' n, thetaTerm k v n

theorem thetaTerm_nonneg (k : ℕ) (v : ℝ) (n : ℕ) : 0 ≤ thetaTerm k v n := by
  unfold thetaTerm
  positivity

theorem thetaTerm_summable (k : ℕ) (v : ℝ) (hv : 0 < v) :
    Summable (thetaTerm k v) :=
  HurwitzKernelBounds.summable_f_nat k 1 hv

theorem thetaMoment_nonneg (k : ℕ) (v : ℝ) : 0 ≤ thetaMoment k v :=
  tsum_nonneg (thetaTerm_nonneg k v)

theorem thetaTerm_antitone (k : ℕ) (n : ℕ) : Antitone (fun v => thetaTerm k v n) := by
  intro v w hvw
  change ((n : ℝ)+1)^k * exp (-Real.pi*((n : ℝ)+1)^2*w) ≤
    ((n : ℝ)+1)^k * exp (-Real.pi*((n : ℝ)+1)^2*v)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left hvw
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) (sq_nonneg _))

theorem thetaMoment_exp_continuousOn (k : ℕ) :
    ContinuousOn (fun u : ℝ => thetaMoment k (exp (4*u))) (Ici 0) := by
  apply continuousOn_tsum (u := thetaTerm k 1)
  · intro n
    unfold thetaTerm
    fun_prop
  · exact thetaTerm_summable k 1 zero_lt_one
  · intro n u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (thetaTerm_nonneg _ _ _)]
    exact thetaTerm_antitone k n (one_le_exp (by change 0 ≤ u at hu; linarith : 0 ≤ 4*u))

theorem thetaTerm_decay (k : ℕ) (v : ℝ) (hv : 1 ≤ v) (n : ℕ) :
    thetaTerm k v n ≤ thetaTerm k (1/2) n * exp (-Real.pi*v/2) := by
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn : 1 ≤ ((n : ℝ)+1)^2 := by nlinarith [sq_nonneg (n : ℝ)]
  have h1 := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ ((n : ℝ)+1)^2)
  have h2 := mul_le_mul_of_nonneg_right hn (by linarith : 0 ≤ v)
  unfold thetaTerm
  conv_rhs => rw [mul_assoc, ← exp_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply exp_le_exp.mpr
  nlinarith [pi_pos]

theorem thetaMoment_decay (k : ℕ) (v : ℝ) (hv : 1 ≤ v) :
    thetaMoment k v ≤ thetaMoment k (1/2) * exp (-Real.pi*v/2) := by
  rw [thetaMoment, thetaMoment, ← tsum_mul_right]
  exact (thetaTerm_summable k v (by linarith)).tsum_le_tsum (thetaTerm_decay k v hv)
    ((thetaTerm_summable k (1/2) (by norm_num)).mul_right _)

def kernel (u : ℝ) : ℝ :=
  2*Real.pi^2*exp (9*u)*thetaMoment 4 (exp (4*u)) -
    3*Real.pi*exp (5*u)*thetaMoment 2 (exp (4*u))

theorem kernel_continuousOn : ContinuousOn kernel (Ici 0) := by
  exact ((continuous_const.mul (by fun_prop : Continuous (fun u : ℝ => exp (9*u)))).continuousOn.mul
    (thetaMoment_exp_continuousOn 4)).sub
    ((continuous_const.mul (by fun_prop : Continuous (fun u : ℝ => exp (5*u)))).continuousOn.mul
    (thetaMoment_exp_continuousOn 2))

def summand (n : ℕ) (u : ℝ) : ℝ :=
  (2*Real.pi^2*((n : ℝ)+1)^4*exp (9*u)-3*Real.pi*((n : ℝ)+1)^2*exp (5*u))*
    exp (-Real.pi*((n : ℝ)+1)^2*exp (4*u))

theorem summand_summable (u : ℝ) : Summable (fun n => summand n u) := by
  have h4 := (thetaTerm_summable 4 (exp (4*u)) (exp_pos _)).mul_left (2*Real.pi^2*exp (9*u))
  have h2 := (thetaTerm_summable 2 (exp (4*u)) (exp_pos _)).mul_left (3*Real.pi*exp (5*u))
  convert h4.sub h2 using 1
  funext n
  unfold summand thetaTerm
  ring

theorem kernel_eq_series (u : ℝ) : kernel u = ∑' n, summand n u := by
  have h4 := (thetaTerm_summable 4 (exp (4*u)) (exp_pos _)).mul_left (2*Real.pi^2*exp (9*u))
  have h2 := (thetaTerm_summable 2 (exp (4*u)) (exp_pos _)).mul_left (3*Real.pi*exp (5*u))
  have he (n : ℕ) : summand n u =
      (2*Real.pi^2*exp (9*u))*thetaTerm 4 (exp (4*u)) n -
        (3*Real.pi*exp (5*u))*thetaTerm 2 (exp (4*u)) n := by
    unfold summand thetaTerm
    ring
  simp_rw [he]
  rw [h4.tsum_sub h2, tsum_mul_left, tsum_mul_left]
  rfl

def envelopeConstant : ℝ :=
  2*Real.pi^2*thetaMoment 4 (1/2)+3*Real.pi*thetaMoment 2 (1/2)

theorem envelopeConstant_nonneg : 0 ≤ envelopeConstant := by
  have h4 := thetaMoment_nonneg 4 (1/2)
  have h2 := thetaMoment_nonneg 2 (1/2)
  unfold envelopeConstant
  positivity

theorem kernel_decay (u : ℝ) (hu : 0 ≤ u) :
    |kernel u| ≤ envelopeConstant*exp (9*u-Real.pi*exp (4*u)/2) := by
  have hv : 1 ≤ exp (4*u) := one_le_exp (by positivity)
  have hp4 := thetaMoment_nonneg 4 (exp (4*u))
  have hp2 := thetaMoment_nonneg 2 (exp (4*u))
  have hq4 := thetaMoment_nonneg 4 (1/2)
  have hq2 := thetaMoment_nonneg 2 (1/2)
  have h4 := thetaMoment_decay 4 (exp (4*u)) hv
  have h2 := thetaMoment_decay 2 (exp (4*u)) hv
  have he : exp (5*u) ≤ exp (9*u) := exp_le_exp.mpr (by linarith)
  calc
    |kernel u| ≤ 2*Real.pi^2*exp (9*u)*thetaMoment 4 (exp (4*u)) +
        3*Real.pi*exp (5*u)*thetaMoment 2 (exp (4*u)) := by
      exact (abs_sub _ _).trans_eq (by
        rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)])
    _ ≤ 2*Real.pi^2*exp (9*u)*(thetaMoment 4 (1/2)*exp (-Real.pi*exp (4*u)/2)) +
        3*Real.pi*exp (9*u)*(thetaMoment 2 (1/2)*exp (-Real.pi*exp (4*u)/2)) := by
      gcongr
    _ = envelopeConstant*exp (9*u-Real.pi*exp (4*u)/2) := by
      rw [sub_eq_add_neg, exp_add]
      unfold envelopeConstant
      ring

theorem summand_pos (n : ℕ) (u : ℝ) (hu : 0 ≤ u) : 0 < summand n u := by
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn : 1 ≤ ((n : ℝ)+1)^2 := by nlinarith [sq_nonneg (n : ℝ)]
  have he : 1 ≤ exp (4*u) := one_le_exp (by positivity)
  have hm : 1 ≤ ((n : ℝ)+1)^2*exp (4*u) := by nlinarith
  have hc : 0 < 2*Real.pi*(((n : ℝ)+1)^2*exp (4*u))-3 := by
    nlinarith [Real.pi_gt_three]
  have hf : summand n u =
      (Real.pi*((n : ℝ)+1)^2*exp (5*u))*
      (2*Real.pi*(((n : ℝ)+1)^2*exp (4*u))-3)*
      exp (-Real.pi*((n : ℝ)+1)^2*exp (4*u)) := by
    unfold summand
    rw [show 9*u=5*u+4*u by ring, exp_add]
    ring
  rw [hf]
  exact mul_pos (mul_pos (by positivity) hc) (exp_pos _)

theorem kernel_pos (u : ℝ) (hu : 0 ≤ u) : 0 < kernel u := by
  rw [kernel_eq_series]
  exact lt_of_lt_of_le (summand_pos 0 u hu)
    ((summand_summable u).le_tsum 0 (fun n _ => (summand_pos n u hu).le))

end OperatorDerivativeRewrite.Foundation.RiemannQuarticKernel
