import Foundation.RiemannQuarticPhaseJets

/-! Derivative enclosures for the actual finite arithmetic kernel, with its
two distinct exponential phases and exact normalization constants. -/
noncomputable section
open scoped ContDiff
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticArithmeticJets
open RiemannQuarticPhaseJets RiemannQuarticTaylorJets RiemannQuarticDyadic
open RiemannQuarticIntervalJets RiemannQuarticRealCertificate

def thetaWeight (m : ℕ) (u : ℝ) : ℝ :=
  2*Real.pi^2*(m : ℝ)^4*Real.exp (phase m 9 u)-
    3*Real.pi*(m : ℝ)^2*Real.exp (phase m 5 u)

def weight (N : ℕ) (u : ℝ) : ℝ := ∑ i ∈ Finset.range N, thetaWeight (i+1) u

theorem thetaWeight_contDiff (m : ℕ) : ContDiff ℝ ∞ (thetaWeight m) := by
  unfold thetaWeight phase
  fun_prop

theorem weight_contDiff (N : ℕ) : ContDiff ℝ ∞ (weight N) := by
  unfold weight thetaWeight phase
  fun_prop

theorem realIntegrand_eq_weight (N k : ℕ) (x u : ℝ) :
    realIntegrand N k x u=weight N u*channel k x u := by
  rw [realIntegrand_eq_sum]
  simp only [weight, thetaWeight, phase, Finset.sum_mul, Nat.cast_add, Nat.cast_one, pow_one]

theorem thetaWeight_coefficient (m n : ℕ) (u : ℝ) :
    coefficient (thetaWeight m) n u =
      2*Real.pi^2*(m : ℝ)^4*coefficient (fun v => Real.exp (phase m 9 v)) n u-
        3*Real.pi*(m : ℝ)^2*coefficient (fun v => Real.exp (phase m 5 v)) n u := by
  unfold coefficient thetaWeight
  rw [iteratedDeriv_fun_sub (by unfold phase; fun_prop) (by unfold phase; fun_prop)]
  simp only [iteratedDeriv_const_mul_field]
  ring

theorem weight_coefficient (N n : ℕ) (u : ℝ) :
    coefficient (weight N) n u=∑ i ∈ Finset.range N, coefficient (thetaWeight (i+1)) n u := by
  unfold coefficient weight
  rw [iteratedDeriv_fun_sum (fun i hi => ((thetaWeight_contDiff (i+1)).of_le (by simp)).contDiffAt),
    Finset.sum_div]

def thetaWeightJet (P E9 E5 : Box) (m p : ℕ) : Box :=
  sub
    (mul (mul (mul (rational 2 p) (pow P p 2) p) (rational ((m : ℚ)^4) p) p) E9 p)
    (mul (mul (mul (rational 3 p) P p) (rational ((m : ℚ)^2) p) p) E5 p) p

theorem thetaWeightJet_mem {u : ℝ} {P E9 E5 : Box} (hp : Real.pi ∈ P) (m n p : ℕ)
    (h9 : coefficient (fun v => Real.exp (phase m 9 v)) n u ∈ E9)
    (h5 : coefficient (fun v => Real.exp (phase m 5 v)) n u ∈ E5) :
    coefficient (thetaWeight m) n u ∈ thetaWeightJet P E9 E5 m p := by
  rw [thetaWeight_coefficient]
  have hm4 : (m : ℝ)^4 ∈ rational ((m : ℚ)^4) p := by
    have hcast : (((m : ℚ)^4 : ℚ) : ℝ)=(m : ℝ)^4 := by norm_cast
    rw [← hcast]
    exact rational_mem ((m : ℚ)^4) p
  have hm2 : (m : ℝ)^2 ∈ rational ((m : ℚ)^2) p := by
    have hcast : (((m : ℚ)^2 : ℚ) : ℝ)=(m : ℝ)^2 := by norm_cast
    rw [← hcast]
    exact rational_mem ((m : ℚ)^2) p
  have hc9 := mul_mem (mul_mem (rational_mem 2 p) (pow_mem hp p 2) p) hm4 p
  have hc5 := mul_mem (mul_mem (rational_mem 3 p) hp p) hm2 p
  have h := sub_mem (mul_mem hc9 h9 p) (mul_mem hc5 h5 p) p
  simpa only [thetaWeightJet, Rat.cast_ofNat] using h

def weightJet (P : Box) (E9 E5 : ℕ → Box) (N p : ℕ) : Box :=
  RiemannQuarticDyadic.sum (fun i => thetaWeightJet P (E9 (i+1)) (E5 (i+1)) (i+1) p) p N

theorem weightJet_mem {u : ℝ} {P : Box} (hp : Real.pi ∈ P) (E9 E5 : ℕ → Box) (N n p : ℕ)
    (h9 : ∀ m, 1 ≤ m → m ≤ N → coefficient (fun v => Real.exp (phase m 9 v)) n u ∈ E9 m)
    (h5 : ∀ m, 1 ≤ m → m ≤ N → coefficient (fun v => Real.exp (phase m 5 v)) n u ∈ E5 m) :
    coefficient (weight N) n u ∈ weightJet P E9 E5 N p := by
  rw [weight_coefficient]
  apply RiemannQuarticDyadic.sum_mem
  intro i hi
  exact thetaWeightJet_mem hp (i+1) n p
    (h9 (i+1) (by omega) (by omega)) (h5 (i+1) (by omega) (by omega))

theorem realIntegrandJet_mem (N k n p : ℕ) (x u : ℝ) (W C : ℕ → Box)
    (hW : ∀ i ≤ n, coefficient (weight N) i u ∈ W i)
    (hC : ∀ i ≤ n, coefficient (channel k x) i u ∈ C i) :
    coefficient (realIntegrand N k x) n u ∈ convolution W C p n := by
  have heq : realIntegrand N k x=fun v => weight N v*channel k x v := by
    funext v
    exact realIntegrand_eq_weight N k x v
  rw [heq]
  exact convolution_mem (weight N) (channel k x) (weight_contDiff N)
    (channel_contDiff k x) u W C p n hW hC

end OperatorDerivativeRewrite.Foundation.RiemannQuarticArithmeticJets
