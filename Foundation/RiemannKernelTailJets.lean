import Foundation.RiemannThetaHolomorphic
import Foundation.RiemannKernelLaguerreJets
import Foundation.RiemannThetaTruncation
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
namespace OperatorDerivativeRewrite.Foundation.RiemannKernelTailJets
open RiemannQuarticKernel RiemannQuarticSaddleTheta RiemannThetaComplexKernel

/-- Literal finite theta kernelPrefix, in the original complex u coordinate. -/
def kernelPrefix (N : ℕ) (u : ℂ) : ℂ :=
  2*(Real.pi:ℂ)^2*Complex.exp (9*u)*
    (∑ j ∈ Finset.range N,complexThetaTerm 4 (Complex.exp (4*u)) j)-
  3*(Real.pi:ℂ)*Complex.exp (5*u)*
    (∑ j ∈ Finset.range N,complexThetaTerm 2 (Complex.exp (4*u)) j)

def remainder (N : ℕ) (u : ℂ) : ℂ := kernelComplex u-kernelPrefix N u

private theorem moment_prefix_tail (k N : ℕ) (v : ℂ) (hv : 0<v.re) :
    moment k v=(∑ j ∈ Finset.range N,complexThetaTerm k v j)+complexThetaTail k N v := by
  have hs : Summable (complexThetaTerm k v) := by
    simpa only [Nat.zero_add] using complexThetaTail_summable k 0 v hv
  simpa only [moment,complexThetaTail,Nat.add_comm] using (hs.sum_add_tsum_nat_add N).symm

theorem remainder_eq_tail (N : ℕ) (u : ℂ) (hu : 0<(Complex.exp (4*u)).re) :
    remainder N u=2*(Real.pi:ℂ)^2*Complex.exp (9*u)*complexThetaTail 4 N (Complex.exp (4*u))-
      3*(Real.pi:ℂ)*Complex.exp (5*u)*complexThetaTail 2 N (Complex.exp (4*u)) := by
  unfold remainder kernelComplex kernelPrefix
  rw [moment_prefix_tail 4 N _ hu,moment_prefix_tail 2 N _ hu]
  ring

theorem prefix_differentiable (N : ℕ) : Differentiable ℂ (kernelPrefix N) := by
  unfold kernelPrefix complexThetaTerm
  fun_prop

theorem prefix_real (N : ℕ) (u : ℝ) : kernelPrefix N (u:ℂ)=(RiemannThetaTruncation.partialKernel N u:ℂ) := by
  have he (a : ℝ) : Complex.exp ((a:ℂ)*(u:ℂ))=(Real.exp (a*u):ℂ) := by
    simp only [Complex.ofReal_exp,Complex.ofReal_mul]
  have he4 : Complex.exp (4*(u:ℂ))=(Real.exp (4*u):ℂ) := by simpa only [Complex.ofReal_ofNat] using he 4
  have he5 : Complex.exp (5*(u:ℂ))=(Real.exp (5*u):ℂ) := by simpa only [Complex.ofReal_ofNat] using he 5
  have he9 : Complex.exp (9*(u:ℂ))=(Real.exp (9*u):ℂ) := by simpa only [Complex.ofReal_ofNat] using he 9
  have hs (k : ℕ) : (∑ j ∈ Finset.range N,complexThetaTerm k (Complex.exp (4*(u:ℂ))) j)=
      ((∑ j ∈ Finset.range N,thetaTerm k (Real.exp (4*u)) j):ℝ) := by
    rw [he4]
    simp only [term_real,Complex.ofReal_sum]
  unfold kernelPrefix RiemannThetaTruncation.partialKernel RiemannThetaTruncation.thetaPrefix
  rw [he9,he5,hs 4,hs 2]
  push_cast
  rfl

theorem remainder_real (N : ℕ) (u : ℝ) :
    remainder N (u:ℂ)=(kernel u-RiemannThetaTruncation.partialKernel N u:ℝ) := by
  rw [remainder,kernelComplex_real,prefix_real,Complex.ofReal_sub]

/-- Entire disk lies in a rectangle where the TWO actual theta moments converge. -/
theorem disk_geometry (u : ℂ) (hu : u∈Metric.closedBall (1/32:ℂ) (1/64:ℝ)) :
    0≤u.re ∧ u.re≤1/16 ∧ |u.im|≤1/16 := by
  have hn : ‖u-(1/32:ℂ)‖≤(1/64:ℝ) := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hu
  have hr := (Complex.abs_re_le_norm (u-(1/32:ℂ))).trans hn
  have hi := (Complex.abs_im_le_norm (u-(1/32:ℂ))).trans hn
  norm_num at hr hi
  rcases abs_le.mp hr with ⟨hr0,hr1⟩
  exact ⟨by linarith,by linarith,hi.trans (by norm_num)⟩

theorem theta_domain (u : ℂ) (hr : 0≤u.re) (hi : |u.im|≤1/16) :
    (1/2:ℝ)≤(Complex.exp (4*u)).re := by
  have hib := abs_le.mp hi
  have hprod := mul_nonneg (sub_nonneg.mpr hib.2) (show 0≤(1/16:ℝ)+u.im by linarith [hib.1])
  have hc : (1/2:ℝ)≤Real.cos (4*u.im) := by
    nlinarith [(Real.one_sub_sq_div_two_le_cos (x := 4*u.im))]
  have he : 1≤Real.exp (4*u.re) := Real.one_le_exp (by positivity)
  have hm := mul_le_mul_of_nonneg_right he (show 0≤Real.cos (4*u.im) by linarith)
  norm_num [Complex.exp_re,Complex.mul_re,Complex.mul_im]
  nlinarith

private theorem small_exp_bound (a : ℝ) (ha : 0≤a) (ha9 : a≤9) (u : ℂ) (hu : u.re≤1/16) :
    Real.exp (a*u.re)≤3 := by
  have hx : a*u.re≤1 := by
    have h := mul_le_mul_of_nonneg_left hu ha
    nlinarith
  exact (Real.exp_le_exp.mpr hx).trans Real.exp_one_lt_three.le

/-- Uniform actual omitted-theta amplitude, with explicit cutoff and domain. -/
theorem remainder_norm_bound (N : ℕ) (u : ℂ) (hr : 0≤u.re) (hu : u.re≤1/16) (hi : |u.im|≤1/16) :
    ‖remainder N u‖≤264*((N:ℝ)+1)^4*Real.exp (-Real.pi*((N:ℝ)+1)^2/2) := by
  have hv := theta_domain u hr hi
  have h4 := complexThetaTail_bound 4 N (by norm_num) (Complex.exp (4*u)) hv
  have h2 := complexThetaTail_bound 2 N (by norm_num) (Complex.exp (4*u)) hv
  have ht := thetaTerm_antitone 4 N hv
  have hA : ‖2*(Real.pi:ℂ)^2*Complex.exp (9*u)‖≤96 := by
    rw [norm_mul,norm_mul,norm_pow,norm_pi]
    norm_num only [Complex.norm_ofNat]
    have he9 := norm_exp_scaled (9:ℝ) u
    simp only [Complex.ofReal_ofNat] at he9
    rw [he9]
    have hp : Real.pi^2≤16 := by nlinarith [Real.pi_lt_four,Real.pi_pos]
    have h := mul_le_mul hp (small_exp_bound 9 (by norm_num) (by norm_num) u hu)
      (Real.exp_pos (9*u.re)).le (by norm_num : (0:ℝ)≤16)
    nlinarith
  have hB : ‖3*(Real.pi:ℂ)*Complex.exp (5*u)‖≤36 := by
    rw [norm_mul,norm_mul,norm_pi]
    norm_num only [Complex.norm_ofNat]
    have he5 := norm_exp_scaled (5:ℝ) u
    simp only [Complex.ofReal_ofNat] at he5
    rw [he5]
    have h := mul_le_mul Real.pi_lt_four.le (small_exp_bound 5 (by norm_num) (by norm_num) u hu)
      (Real.exp_pos (5*u.re)).le (by norm_num : (0:ℝ)≤4)
    nlinarith
  rw [remainder_eq_tail N u (by linarith)]
  calc
    _ ≤ ‖2*(Real.pi:ℂ)^2*Complex.exp (9*u)*complexThetaTail 4 N (Complex.exp (4*u))‖+
        ‖3*(Real.pi:ℂ)*Complex.exp (5*u)*complexThetaTail 2 N (Complex.exp (4*u))‖ := norm_sub_le _ _
    _ ≤ 96*(2*thetaTerm 4 (1/2) N)+36*(2*thetaTerm 4 (1/2) N) := by
      simp only [norm_mul] at hA hB ⊢
      exact add_le_add (mul_le_mul hA (h4.trans (mul_le_mul_of_nonneg_left ht (by norm_num))) (norm_nonneg _) (by norm_num))
        (mul_le_mul hB (h2.trans (mul_le_mul_of_nonneg_left ht (by norm_num))) (norm_nonneg _) (by norm_num))
    _ = _ := by
      unfold thetaTerm
      rw [show -Real.pi*((N:ℝ)+1)^2*(1/2)=-Real.pi*((N:ℝ)+1)^2/2 by ring]
      ring


/-- Explicit disk amplitude majorant for the actual omitted series. -/
def amplitude (N : ℕ) : ℝ :=
  264*((N:ℝ)+1)^4*Real.exp (-Real.pi*((N:ℝ)+1)^2/2)

theorem remainder_diffContOnCl (N : ℕ) :
    DiffContOnCl ℂ (remainder N) (Metric.ball (1/32:ℂ) (1/64:ℝ)) := by
  have hd : DifferentiableOn ℂ (remainder N) (Metric.closedBall (1/32:ℂ) (1/64:ℝ)) := by
    intro u hu
    obtain ⟨hr,hU,hi⟩ := disk_geometry u hu
    have hv := theta_domain u hr hi
    exact ((kernelComplex_differentiableAt u (by linarith)).sub (prefix_differentiable N u)).differentiableWithinAt
  exact (hd.mono Metric.closure_ball_subset_closedBall).diffContOnCl

/-- All normalized complex derivatives have genuine Cauchy tail bounds.
No differentiation of an infinite series beyond the existing holomorphy proof. -/
theorem normalized_derivative_bound (N n : ℕ) :
    ‖iteratedDeriv n (remainder N) (1/32:ℂ)/(n.factorial:ℂ)‖≤amplitude N/(1/64:ℝ)^n := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0:ℝ)<1/64) (remainder_diffContOnCl N) (C := amplitude N) (by
      intro u hu
      obtain ⟨hr,hU,hi⟩ := disk_geometry u (Metric.sphere_subset_closedBall hu)
      exact remainder_norm_bound N u hr hU hi)
  rw [norm_div,norm_natCast]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<n.factorial)).mpr
  calc
    _ ≤ (n.factorial:ℝ)*amplitude N/(1/64:ℝ)^n := h
    _ = _ := by ring

private theorem amplitude_sixteen_bound :
    amplitude 16≤264*(17:ℝ)^4/(2:ℝ)^432 := by
  have he1 : (2:ℝ)≤Real.exp 1 := by have h := Real.add_one_le_exp (1:ℝ);linarith
  have hlarge : (2:ℝ)^432≤Real.exp 432 := by
    calc
      _ ≤ (Real.exp 1)^432 := pow_le_pow_left₀ (by norm_num) he1 432
      _ = _ := by rw [← Real.exp_nat_mul];norm_num
  have he : Real.exp (-Real.pi*((16:ℝ)+1)^2/2)≤((2:ℝ)^432)⁻¹ := by
    calc
      _ ≤ Real.exp (-432) := Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
      _ = (Real.exp 432)⁻¹ := Real.exp_neg 432
      _ ≤ _ := (inv_le_inv₀ (Real.exp_pos 432) (by positivity)).mpr hlarge
  unfold amplitude
  calc
    _ ≤ 264*((16:ℝ)+1)^4*((2:ℝ)^432)⁻¹ := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by norm_num [div_eq_mul_inv]

/-- The original-u Taylor tail through order10 is strictly below10^-100.
This does NOT yet enclose the square-root-coordinate prefix coefficients. -/
theorem sixteen_normalized_derivative_lt (n : ℕ) (hn : n≤10) :
    ‖iteratedDeriv n (remainder 16) (1/32:ℂ)/(n.factorial:ℂ)‖<1/(10:ℝ)^100 := by
  have hn64 : (64:ℝ)^n≤(64:ℝ)^10 := pow_le_pow_right₀ (by norm_num) hn
  calc
    _ ≤ amplitude 16/(1/64:ℝ)^n := normalized_derivative_bound 16 n
    _ = amplitude 16*(64:ℝ)^n := by simp only [one_div,inv_pow,div_inv_eq_mul]
    _ ≤ (264*(17:ℝ)^4/(2:ℝ)^432)*(64:ℝ)^10 :=
      mul_le_mul amplitude_sixteen_bound hn64 (by positivity) (by positivity)
    _ < _ := by
      rw [show (432:ℕ)=216+216 from rfl,pow_add]
      norm_num


/-- The remainder is analytic at every REAL point, independently of the small disk. -/
theorem remainder_analyticAt_real (N : ℕ) (u : ℝ) : AnalyticAt ℂ (remainder N) (u:ℂ) := by
  have he : 0<(Complex.exp (4*(u:ℂ))).re := by
    simpa only [← Complex.ofReal_ofNat,← Complex.ofReal_mul,← Complex.ofReal_exp,
      Complex.ofReal_re] using Real.exp_pos (4*u)
  have hp : DifferentiableOn ℂ (kernelPrefix N) Set.univ := (prefix_differentiable N).differentiableOn
  exact (kernelComplex_analyticAt (u:ℂ) he).sub (hp.analyticAt (by simp))

/-- Exact restriction of all complex derivatives to the actual real kernel tail. -/
theorem real_remainder_iteratedDeriv (N n : ℕ) :
    iteratedDeriv n (fun u : ℝ => kernel u-RiemannThetaTruncation.partialKernel N u)=
      fun u : ℝ => (iteratedDeriv n (remainder N) (u:ℂ)).re := by
  induction n with
  | zero =>
    funext u
    simp only [iteratedDeriv_zero]
    rw [remainder_real]
    rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext u
    have ha : AnalyticAt ℂ (iteratedDeriv n (remainder N)) (u:ℂ) := by
      rw [iteratedDeriv_eq_iterate]
      exact (remainder_analyticAt_real N u).iterated_deriv n
    simpa only [iteratedDeriv_succ] using ha.differentiableAt.hasDerivAt.real_of_complex.deriv

/-- Genuine normalized REAL Taylor-coefficient tail bound, original u coordinate. -/
theorem real_sixteen_coefficient_lt (n : ℕ) (hn : n≤10) :
    |iteratedDeriv n (fun u : ℝ => kernel u-RiemannThetaTruncation.partialKernel 16 u) (1/32)/
      (n.factorial:ℝ)|<1/(10:ℝ)^100 := by
  rw [real_remainder_iteratedDeriv,abs_div,abs_of_pos (by positivity : (0:ℝ)<n.factorial)]
  simp only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  calc
    _ ≤ ‖iteratedDeriv n (remainder 16) (1/32:ℂ)‖/(n.factorial:ℝ) :=
      div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) (by positivity)
    _ < _ := by simpa only [norm_div,norm_natCast] using sixteen_normalized_derivative_lt n hn


/-- Exact error in the actual real kernel coefficients, ready for interval input. -/
theorem real_sixteen_coefficient_error (n : ℕ) (hn : n≤10) :
    |RiemannQuarticTaylorJets.coefficient kernel n (1/32)-
      RiemannQuarticTaylorJets.coefficient (RiemannThetaTruncation.partialKernel 16) n (1/32)|<
      1/(10:ℝ)^100 := by
  have h := real_sixteen_coefficient_lt n hn
  have hK : ContDiffAt ℝ ∞ kernel (1/32) := (RiemannQuarticSaddleTimes.kernel_analyticAt (1/32)).contDiffAt
  have hP : ContDiffAt ℝ ∞ (RiemannThetaTruncation.partialKernel 16) (1/32) :=
    (RiemannQuarticTaylorJets.partialKernel_contDiff 16).contDiffAt
  rw [iteratedDeriv_fun_sub (hK.of_le (by simp)) (hP.of_le (by simp))] at h
  simpa only [RiemannQuarticTaylorJets.coefficient,sub_div] using h

end OperatorDerivativeRewrite.Foundation.RiemannKernelTailJets
