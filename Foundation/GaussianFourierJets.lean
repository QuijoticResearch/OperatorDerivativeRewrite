import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Absolutely convergent periodic Gaussian Fourier jets, with justified
termwise spatial differentiation at every positive smoothing parameter. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace OperatorDerivativeRewrite.Foundation.GaussianFourierJets

def bound (k : ℕ) (s : ℝ) (n : ℤ) : ℝ := |(n : ℝ)|^k*Real.exp (-s*(n : ℝ)^2)
def term (k : ℕ) (s : ℝ) (n : ℤ) (y : ℝ) : ℝ :=
  (n : ℝ)^k*Real.exp (-s*(n : ℝ)^2)*Real.cos ((n : ℝ)*y+(k : ℝ)*Real.pi/2)
def jet (k : ℕ) (s y : ℝ) : ℝ := ∑' n : ℤ, term k s n y

theorem bound_summable (k : ℕ) (s : ℝ) (hs : 0 < s) : Summable (bound k s) := by
  have h := summable_pow_mul_jacobiTheta₂_term_bound 0
    (T := s/Real.pi) (div_pos hs Real.pi_pos) k
  have he (n : ℤ) : Real.exp (-Real.pi*(s/Real.pi*(n : ℝ)^2-2*0*|(n : ℝ)|)) =
      Real.exp (-s*(n : ℝ)^2) := by
    congr 1
    field_simp
    <;> ring
  change Summable (fun n : ℤ => |(n : ℝ)|^k*Real.exp (-s*(n : ℝ)^2))
  simpa only [Int.cast_abs, he] using h

theorem term_bound (k : ℕ) (s : ℝ) (n : ℤ) (y : ℝ) :
    ‖term k s n y‖ ≤ bound k s n := by
  rw [term, norm_mul, norm_mul, Real.norm_eq_abs, abs_pow,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  have h := Real.abs_cos_le_one ((n : ℝ)*y+(k : ℝ)*Real.pi/2)
  simpa only [bound, Real.norm_eq_abs, mul_one] using mul_le_mul_of_nonneg_left h
    (by positivity : 0 ≤ |(n : ℝ)|^k*Real.exp (-s*(n : ℝ)^2))

theorem term_summable (k : ℕ) (s : ℝ) (hs : 0 < s) (y : ℝ) :
    Summable (fun n : ℤ => term k s n y) :=
  (bound_summable k s hs).of_norm_bounded (fun n => term_bound k s n y)

theorem term_derivative (k : ℕ) (s : ℝ) (n : ℤ) (y : ℝ) :
    HasDerivAt (term k s n) (term (k+1) s n y) y := by
  have h := ((((hasDerivAt_id y).const_mul (n : ℝ)).add_const
    ((k : ℝ)*Real.pi/2)).cos).const_mul ((n : ℝ)^k*Real.exp (-s*(n : ℝ)^2))
  simp only [id_eq, mul_one] at h
  convert h using 1
  · rfl
  · simp only [term, Nat.cast_add, Nat.cast_one, pow_succ]
    rw [show (n : ℝ)*y+((k : ℝ)+1)*Real.pi/2 =
      ((n : ℝ)*y+(k : ℝ)*Real.pi/2)+Real.pi/2 by ring,
      Real.cos_add_pi_div_two]
    ring

theorem jet_derivative (k : ℕ) (s : ℝ) (hs : 0 < s) (y : ℝ) :
    HasDerivAt (jet k s) (jet (k+1) s y) y := by
  exact hasDerivAt_tsum (bound_summable (k+1) s hs)
    (fun n y => term_derivative k s n y)
    (fun n y => term_bound (k+1) s n y) (term_summable k s hs 0) y

theorem deriv_jet (k : ℕ) (s : ℝ) (hs : 0 < s) : deriv (jet k s) = jet (k+1) s :=
  funext (fun y => (jet_derivative k s hs y).deriv)

theorem jet_continuous (k : ℕ) (s : ℝ) (hs : 0 < s) : Continuous (jet k s) :=
  continuous_iff_continuousAt.mpr (fun y => (jet_derivative k s hs y).continuousAt)

theorem jet_smooth_nat (m k : ℕ) (s : ℝ) (hs : 0 < s) : ContDiff ℝ m (jet k s) := by
  induction m generalizing k with
  | zero => exact contDiff_zero.mpr (jet_continuous k s hs)
  | succ m ih =>
    rw [show ((m+1 : ℕ) : ℕ∞ω) = (m : ℕ∞ω)+1 by norm_cast,
      contDiff_succ_iff_deriv]
    refine ⟨fun y => (jet_derivative k s hs y).differentiableAt, ?_, ?_⟩
    · simp
    · rw [deriv_jet k s hs]
      exact ih (k+1)

theorem jet_smooth (k : ℕ) (s : ℝ) (hs : 0 < s) : ContDiff ℝ ∞ (jet k s) :=
  contDiff_infty.mpr (fun m => jet_smooth_nat m k s hs)

theorem term_periodic (k : ℕ) (s : ℝ) (n : ℤ) :
    Function.Periodic (term k s n) (2*Real.pi) := by
  intro y
  simp only [term]
  rw [show (n : ℝ)*(y+2*Real.pi)+(k : ℝ)*Real.pi/2 =
    ((n : ℝ)*y+(k : ℝ)*Real.pi/2)+(n : ℝ)*(2*Real.pi) by ring,
    Real.cos_add_int_mul_two_pi]

theorem jet_periodic (k : ℕ) (s : ℝ) : Function.Periodic (jet k s) (2*Real.pi) := by
  intro y
  unfold jet
  congr 1
  funext n
  exact term_periodic k s n y

end OperatorDerivativeRewrite.Foundation.GaussianFourierJets
