import Foundation.RiemannQuarticFiniteApproximation

/-! The actual real integrals needed by a quartic-flow Laguerre certificate.
All numerical enclosure hypotheses below remain explicit. -/
noncomputable section
open MeasureTheory Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticRealCertificate
open RiemannQuarticFlow RiemannQuarticEvolution RiemannThetaTruncation
open RiemannQuarticFiniteApproximation RiemannQuarticJetCutoff

def channel (k : ℕ) (x u : ℝ) : ℝ :=
  match k with
  | 0 => Real.cos (u*x)
  | 1 => -u*Real.sin (u*x)
  | _ => -u^2*Real.cos (u*x)

def realIntegrand (N k : ℕ) (x u : ℝ) : ℝ :=
  Real.exp (8*u^4)*partialKernel N u*channel k x u

theorem realIntegrand_eq_sum (N k : ℕ) (x u : ℝ) :
    realIntegrand N k x u =
      ∑ n ∈ Finset.range N,
        (2*Real.pi^2*((n : ℝ)+1)^4*
          Real.exp (8*u^4+9*u-Real.pi*((n : ℝ)+1)^2*Real.exp (4*u))-
         3*Real.pi*((n : ℝ)+1)^2*
          Real.exp (8*u^4+5*u-Real.pi*((n : ℝ)+1)^2*Real.exp (4*u)))*channel k x u := by
  simp only [realIntegrand, partialKernel, thetaPrefix, RiemannQuarticKernel.thetaTerm,
    Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib, mul_sub, sub_mul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro n hn <;>
    simp only [sub_eq_add_neg, Real.exp_add] <;> ring

def realQuadrature (N k : ℕ) (x : ℝ) : ℝ :=
  ∫ u in 0..(8/5 : ℝ), realIntegrand N k x u

theorem symmetric_integrand_real (N k : ℕ) (hk : k ≤ 2) (x u : ℝ) :
    (partialIntegrand N k 8 (x : ℂ) u+
      (-1 : ℂ)^k*partialIntegrand N k 8 (-(x : ℂ)) u)/2 =
      (realIntegrand N k x u : ℂ) := by
  interval_cases k <;> apply Complex.ext <;>
    simp [partialIntegrand, realIntegrand, channel, Complex.mul_re, Complex.mul_im,
      Complex.exp_re, Complex.exp_im, pow_succ, ← Complex.ofReal_mul,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin] <;> ring

theorem finiteDerivative_real (N k : ℕ) (hk : k ≤ 2) (x : ℝ) :
    finiteDerivative N k 8 (x : ℂ) (8/5) = (realQuadrature N k x : ℂ) := by
  have hp := (partialIntegrand_continuous N k 8 (x : ℂ)).intervalIntegrable
    (μ := volume) (a := (0 : ℝ)) (b := (8/5 : ℝ))
  have hm := (partialIntegrand_continuous N k 8 (-(x : ℂ))).intervalIntegrable
    (μ := volume) (a := (0 : ℝ)) (b := (8/5 : ℝ))
  unfold finiteDerivative finiteJet
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add hp (hm.const_mul ((-1 : ℂ)^k)),
    ← intervalIntegral.integral_div]
  calc
    _ = ∫ u in 0..(8/5 : ℝ), (realIntegrand N k x u : ℂ) := by
      apply intervalIntegral.integral_congr
      exact fun u _ => symmetric_integrand_real N k hk x u
    _ = _ := by
      simp only [realQuadrature, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 8/5)]
      exact integral_ofReal

def actualJet (k : ℕ) (x : ℝ) : ℝ := (iteratedDeriv k (flow 8) (x : ℂ)).re

theorem actualJet_fifteen_error (k : ℕ) (hk : k ≤ 2) (x : ℝ) :
    |actualJet k x-realQuadrature 15 k x| ≤ (1/10^27 : ℝ) := by
  have he := derivative_finite_error k hk x
  rw [finiteDerivative_real 15 k hk x] at he
  have hr := RCLike.abs_re_le_norm
    (iteratedDeriv k (flow 8) (x : ℂ)-(realQuadrature 15 k x : ℂ))
  have hr' : |actualJet k x-realQuadrature 15 k x| ≤
      ‖iteratedDeriv k (flow 8) (x : ℂ)-(realQuadrature 15 k x : ℂ)‖ := by
    simpa only [RCLike.re_eq_complex_re, Complex.sub_re, Complex.ofReal_re, actualJet] using hr
  exact hr'.trans he

theorem four_term_numeric_bound :
    352*((4 : ℝ)+1)^4*Real.exp (-Real.pi*((4 : ℝ)+1)^2) ≤ (1/10^17 : ℝ) := by
  have he : (2 : ℝ)^75 ≤ Real.exp 75 := by
    have h : (2 : ℝ) ≤ Real.exp 1 := by
      have hh := Real.add_one_le_exp (1 : ℝ)
      linarith
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h 75
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one] using hp
  have hi : Real.exp (-Real.pi*((4 : ℝ)+1)^2) ≤ ((2 : ℝ)^75)⁻¹ := by
    calc
      _ ≤ Real.exp (-(75 : ℝ)) := Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
      _ = (Real.exp (75 : ℝ))⁻¹ := Real.exp_neg _
      _ ≤ _ := (inv_le_inv₀ (Real.exp_pos _) (by positivity)).mpr he
  calc
    _ ≤ 352*((4 : ℝ)+1)^4*((2 : ℝ)^75)⁻¹ :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ ≤ _ := by norm_num

theorem four_term_remainder (k : ℕ) (hk : k ≤ 2) (u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 8/5) :
    |u^k*Real.exp (8*u^4)*(RiemannQuarticKernel.kernel u-partialKernel 4 u)| ≤
      (1/10^17 : ℝ) :=
  (tilted_remainder_bound k 4 hk (by norm_num) u hu0 hu1).trans four_term_numeric_bound

theorem cutoff_four_error (k : ℕ) (hk : k ≤ 2) (x : ℝ) :
    ‖cutoffJet k 8 (x : ℂ) (8/5)-finiteJet 4 k 8 (x : ℂ) (8/5)‖ ≤
      (8/5 : ℝ)*(1/10^17) := by
  have hi : IntervalIntegrable (integrand k 8 (x : ℂ)) volume 0 (8/5) := by
    apply ContinuousOn.intervalIntegrable
    apply (integrand_continuousOn k 8 (x : ℂ)).mono
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 8/5)]
    exact fun u hu => hu.1
  have hj := (partialIntegrand_continuous 4 k 8 (x : ℂ)).intervalIntegrable
    (μ := volume) (a := (0 : ℝ)) (b := (8/5 : ℝ))
  rw [cutoffJet, finiteJet, ← intervalIntegral.integral_sub hi hj]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (8/5 : ℝ)) (C := (1/10^17 : ℝ))
    (f := fun u => integrand k 8 (x : ℂ) u-partialIntegrand 4 k 8 (x : ℂ) u) (by
      intro u hu
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 8/5)] at hu
      rw [integrand_difference_norm 4 k 8 x u (le_of_lt hu.1)]
      exact four_term_remainder k hk u (le_of_lt hu.1) hu.2)
  norm_num only [sub_zero, abs_of_pos (by norm_num : (0 : ℝ) < 8/5)] at h
  convert h using 1 <;> norm_num

theorem jet_four_error (k : ℕ) (hk : k ≤ 2) (x : ℝ) :
    ‖jet k 8 (x : ℂ)-finiteJet 4 k 8 (x : ℂ) (8/5)‖ ≤ (1/10^16 : ℝ) := by
  have h := dist_triangle (jet k 8 (x : ℂ)) (cutoffJet k 8 (x : ℂ) (8/5))
    (finiteJet 4 k 8 (x : ℂ) (8/5))
  simp only [dist_eq_norm] at h
  have ht := jet_cutoff_error k hk x
  have hf := cutoff_four_error k hk x
  linarith

theorem derivative_four_error (k : ℕ) (hk : k ≤ 2) (x : ℝ) :
    ‖iteratedDeriv k (flow 8) (x : ℂ)-finiteDerivative 4 k 8 (x : ℂ) (8/5)‖ ≤
      (1/10^16 : ℝ) := by
  rw [flow_iteratedDeriv]
  have hp := jet_four_error k hk x
  have hm := jet_four_error k hk (-x)
  simp only [Complex.ofReal_neg] at hm
  have he : symmetricJet k 8 (x : ℂ)-finiteDerivative 4 k 8 (x : ℂ) (8/5) =
      ((jet k 8 (x : ℂ)-finiteJet 4 k 8 (x : ℂ) (8/5))+
        (-1 : ℂ)^k*(jet k 8 (-(x : ℂ))-finiteJet 4 k 8 (-(x : ℂ)) (8/5)))/2 := by
    unfold symmetricJet finiteDerivative
    ring
  rw [he, norm_div]
  have hn : ‖(-1 : ℂ)^k‖=1 := by simp
  have h := norm_add_le (jet k 8 (x : ℂ)-finiteJet 4 k 8 (x : ℂ) (8/5))
    ((-1 : ℂ)^k*(jet k 8 (-(x : ℂ))-finiteJet 4 k 8 (-(x : ℂ)) (8/5)))
  rw [norm_mul, hn, one_mul] at h
  norm_num only [Complex.norm_ofNat] at *
  linarith

theorem actualJet_four_error (k : ℕ) (hk : k ≤ 2) (x : ℝ) :
    |actualJet k x-realQuadrature 4 k x| ≤ (1/10^16 : ℝ) := by
  have he := derivative_four_error k hk x
  rw [finiteDerivative_real 4 k hk x] at he
  have hr := RCLike.abs_re_le_norm
    (iteratedDeriv k (flow 8) (x : ℂ)-(realQuadrature 4 k x : ℂ))
  have hr' : |actualJet k x-realQuadrature 4 k x| ≤
      ‖iteratedDeriv k (flow 8) (x : ℂ)-(realQuadrature 4 k x : ℂ)‖ := by
    simpa only [RCLike.re_eq_complex_re, Complex.sub_re, Complex.ofReal_re, actualJet] using hr
  exact hr'.trans he

def realLaguerre (x : ℝ) : ℝ := actualJet 1 x^2-actualJet 0 x*actualJet 2 x

theorem negative_Laguerre_of_enclosures (x : ℝ)
    (h0 : realQuadrature 4 0 x ≤ -(163/10^12 : ℝ))
    (h1 : |realQuadrature 4 1 x| ≤ (4/10^13 : ℝ))
    (h2 : realQuadrature 4 2 x ≤ -(145/10^12 : ℝ)) :
    realLaguerre x < -(2/10^20 : ℝ) := by
  have e0 := abs_le.mp (actualJet_four_error 0 (by norm_num) x)
  have e1 := abs_le.mp (actualJet_four_error 1 (by norm_num) x)
  have e2 := abs_le.mp (actualJet_four_error 2 (by norm_num) x)
  have hb1 := abs_le.mp h1
  have a0 : actualJet 0 x ≤ -(16/10^11 : ℝ) := by linarith
  have a2 : actualJet 2 x ≤ -(14/10^11 : ℝ) := by linarith
  have a1 : |actualJet 1 x| ≤ (1/10^12 : ℝ) := by rw [abs_le]; constructor <;> linarith
  have ab1 := abs_le.mp a1
  have hs := mul_nonneg (show 0 ≤ 1/10^12-actualJet 1 x by linarith)
    (show 0 ≤ 1/10^12+actualJet 1 x by linarith)
  have hp := mul_nonneg (show 0 ≤ -actualJet 0 x-16/10^11 by linarith)
    (show 0 ≤ -actualJet 2 x-14/10^11 by linarith)
  unfold realLaguerre
  nlinarith

end OperatorDerivativeRewrite.Foundation.RiemannQuarticRealCertificate
