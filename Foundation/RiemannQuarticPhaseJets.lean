import Foundation.RiemannQuarticTrigJets

/-! Actual normalized phase coefficients for the literal arithmetic theta terms. -/
noncomputable section
open scoped ContDiff
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticPhaseJets
open RiemannQuarticTaylorJets RiemannQuarticDyadic RiemannQuarticIntervalJets

def phase (m : ℕ) (a u : ℝ) : ℝ :=
  8*u^4+a*u^1-Real.pi*(m : ℝ)^2*Real.exp (4*u)

theorem phase_contDiff (m : ℕ) (a : ℝ) : ContDiff ℝ ∞ (phase m a) := by
  unfold phase
  fun_prop

theorem phase_coefficient (m n : ℕ) (a u : ℝ) :
    coefficient (phase m a) n u =
      (8*((4 : ℕ).descFactorial n : ℝ)*u^(4-n)+
        a*((1 : ℕ).descFactorial n : ℝ)*u^(1-n)-
        Real.pi*(m : ℝ)^2*4^n*Real.exp (4*u))/(n.factorial : ℝ) := by
  unfold coefficient phase
  rw [iteratedDeriv_fun_sub (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop)]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_pow,
    iteratedDeriv_exp_const_mul]
  ring

def phaseJet (U E P A : Box) (m p n : ℕ) : Box :=
  divNat (sub
    (add
      (mul (rational (8*((4 : ℕ).descFactorial n : ℚ)) p) (pow U p (4-n)) p)
      (mul A (mul (rational ((1 : ℕ).descFactorial n : ℚ) p) (pow U p (1-n)) p) p) p)
    (mul (mul P (rational ((m : ℚ)^2) p) p)
      (mul (rational ((4 : ℚ)^n) p) E p) p) p) n.factorial p

theorem phaseJet_mem {u a : ℝ} {U E P A : Box}
    (hu : u ∈ U) (he : Real.exp (4*u) ∈ E) (hp : Real.pi ∈ P) (ha : a ∈ A)
    (m p n : ℕ) : coefficient (phase m a) n u ∈ phaseJet U E P A m p n := by
  rw [phase_coefficient]
  have hq : (8 : ℝ)*((4 : ℕ).descFactorial n : ℝ) ∈ rational (8*((4 : ℕ).descFactorial n : ℚ)) p := by
    simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using
      rational_mem (8*((4 : ℕ).descFactorial n : ℚ)) p
  have hl : ((1 : ℕ).descFactorial n : ℝ) ∈ rational ((1 : ℕ).descFactorial n : ℚ) p := by
    simpa only [Rat.cast_natCast] using rational_mem ((1 : ℕ).descFactorial n : ℚ) p
  have hm : (m : ℝ)^2 ∈ rational ((m : ℚ)^2) p := by
    have hcast : (((m : ℚ)^2 : ℚ) : ℝ)=(m : ℝ)^2 := by norm_cast
    rw [← hcast]
    exact rational_mem ((m : ℚ)^2) p
  have h4 : (4 : ℝ)^n ∈ rational ((4 : ℚ)^n) p := by
    simpa only [Rat.cast_pow, Rat.cast_ofNat] using rational_mem ((4 : ℚ)^n) p
  have hquartic := mul_mem hq (pow_mem hu p (4-n)) p
  have hlinear := mul_mem ha (mul_mem hl (pow_mem hu p (1-n)) p) p
  have htheta := mul_mem (mul_mem hp hm p) (mul_mem h4 he p) p
  have hnum := sub_mem (add_mem hquartic hlinear p) htheta p
  have h := divNat_mem hnum n.factorial p
  simpa only [phaseJet, mul_assoc] using h

def phaseExpJet (U E P A B : Box) (m p n : ℕ) : Box :=
  expJet (fun i => phaseJet U E P A m p i) B p n

theorem phaseExpJet_mem {u a : ℝ} {U E P A B : Box}
    (hu : u ∈ U) (he : Real.exp (4*u) ∈ E) (hp : Real.pi ∈ P) (ha : a ∈ A)
    (m p n : ℕ) (hb : Real.exp (phase m a u) ∈ B) :
    coefficient (fun v => Real.exp (phase m a v)) n u ∈ phaseExpJet U E P A B m p n := by
  exact expJet_mem (phase m a) (phase_contDiff m a) u
    (fun i => phaseJet U E P A m p i) B p n hb
    (fun i _ => phaseJet_mem hu he hp ha m p i)

end OperatorDerivativeRewrite.Foundation.RiemannQuarticPhaseJets
