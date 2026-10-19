import Foundation.RiemannThetaDerivativeBounds
import Foundation.RiemannQuarticSaddleTimes
import Foundation.RiemannQuarticSaddleBranch
/-! Quantitative curvature of the literal arithmetic kernel and its quartic tilt.
Exact first/second derivative normalizations and genuine theta-tail bounds
control logarithmic curvature after leading cancellation. Every stationary
point with t>=0,u>=1 has strictly negative phase curvature. Escape of actual
global amplitude maxima makes all such maxima nondegenerate at every
sufficiently large time, with no exceptional-time restriction. The exact
saddle-time map is strictly increasing on [1,infinity), and global amplitude
maxima are unique at every sufficiently large time. Actual stationary scales
have explicit additive errors and relative curvature error at most 13/t. No uniform
frequency radius or integrated far-field/zero-control estimate follows. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticCurvature
open RiemannQuarticKernel RiemannQuarticSaddleTheta RiemannThetaComplexKernel

def kernelSecond (u : ℂ) : ℂ :=
  330*(Real.pi : ℂ)^2*Complex.exp (9*u)*moment 4 (Complex.exp (4*u))-
    224*(Real.pi : ℂ)^3*Complex.exp (13*u)*moment 6 (Complex.exp (4*u))+
    32*(Real.pi : ℂ)^4*Complex.exp (17*u)*moment 8 (Complex.exp (4*u))-
    75*(Real.pi : ℂ)*Complex.exp (5*u)*moment 2 (Complex.exp (4*u))

theorem kernelDerivative_hasDerivAt (u : ℂ) (hu : 0 < (Complex.exp (4*u)).re) :
    HasDerivAt kernelDerivative (kernelSecond u) u := by
  have he (a : ℂ) := ((hasDerivAt_id u).const_mul a).cexp
  have hm (k : ℕ) := (moment_hasDerivAt k _ hu).comp u (he 4)
  have hA := ((he 9).const_mul (30*(Real.pi : ℂ)^2)).mul (hm 4)
  have hB := ((he 13).const_mul (8*(Real.pi : ℂ)^3)).mul (hm 6)
  have hC := ((he 5).const_mul (15*(Real.pi : ℂ))).mul (hm 2)
  have hd := (hA.sub hB).sub hC
  convert hd using 1
  · funext w
    rfl
  · have h17 : Complex.exp (17*u)=Complex.exp (13*u)*Complex.exp (4*u) := by
      rw [← Complex.exp_add]; congr 1; ring
    have h13 : Complex.exp (13*u)=Complex.exp (9*u)*Complex.exp (4*u) := by
      rw [← Complex.exp_add]; congr 1; ring
    have h9 : Complex.exp (9*u)=Complex.exp (5*u)*Complex.exp (4*u) := by
      rw [← Complex.exp_add]; congr 1; ring
    dsimp [kernelSecond]
    rw [h17,h13,h9]
    norm_num
    ring

theorem logSlope_hasDerivAt (u : ℂ) (hu : 0 < (Complex.exp (4*u)).re)
    (hne : kernelComplex u ≠ 0) :
    HasDerivAt (fun w => kernelDerivative w/kernelComplex w)
      (kernelSecond u/kernelComplex u-(kernelDerivative u/kernelComplex u)^2) u := by
  have h := (kernelDerivative_hasDerivAt u hu).div (kernelComplex_hasDerivAt u hu) hne
  convert h using 1
  field_simp <;> ring

theorem eighth_le_four_half (v : ℝ) (hv : 1 ≤ v) (n : ℕ) :
    thetaTerm 8 v n ≤ thetaTerm 4 (v/2) n := by
  let q : ℝ := (n : ℝ)+1
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq4 : 0 ≤ q^4 := by positivity
  have hp := Real.pow_div_factorial_le_exp (Real.pi*q^2/2) (by positivity : 0 ≤ Real.pi*q^2/2) 2
  norm_num at hp
  have hpi : (8 : ℝ) ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hpre : q^4 ≤ Real.exp (Real.pi*q^2/2) := by
    have hmul := mul_le_mul_of_nonneg_right hpi hq4
    nlinarith
  have hpre' : q^4 ≤ Real.exp (Real.pi*q^2*v/2) := by
    apply hpre.trans
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ Real.pi*q^2/2)
    nlinarith
  change q^8*Real.exp (-Real.pi*q^2*v) ≤ q^4*Real.exp (-Real.pi*q^2*(v/2))
  calc
    _ = q^4*(q^4*Real.exp (-Real.pi*q^2*v)) := by ring
    _ ≤ q^4*(Real.exp (Real.pi*q^2*v/2)*Real.exp (-Real.pi*q^2*v)) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

theorem complex_tail_eight_bound (v : ℂ) (hv : 1 ≤ v.re) :
    ‖complexThetaTail 8 1 v‖ ≤ 32*Real.exp (-2*Real.pi*v.re) := by
  have h8 := RiemannThetaEffective.tail_summable 8 1 v.re (by linarith)
  have h4 := RiemannThetaEffective.tail_summable 4 1 (v.re/2) (by linarith)
  have hn : Summable (fun n => ‖complexThetaTerm 8 v (1+n)‖) := by
    simpa only [norm_complexThetaTerm] using h8
  calc
    _ ≤ ∑' n, ‖complexThetaTerm 8 v (1+n)‖ := norm_tsum_le_tsum_norm hn
    _ = RiemannThetaEffective.tail 8 1 v.re := by simp only [norm_complexThetaTerm,RiemannThetaEffective.tail]
    _ ≤ RiemannThetaEffective.tail 4 1 (v.re/2) :=
      h8.tsum_le_tsum (fun n => eighth_le_four_half v.re hv (1+n)) h4
    _ ≤ 2*thetaTerm 4 (v.re/2) 1 := RiemannThetaEffective.tail_four_bound 1 (v.re/2) (by linarith)
    _ = _ := by norm_num [thetaTerm]; ring_nf

def leadingSecond (u : ℂ) : ℂ :=
  (330*(Real.pi : ℂ)^2*Complex.exp (9*u)-224*(Real.pi : ℂ)^3*Complex.exp (13*u)+
    32*(Real.pi : ℂ)^4*Complex.exp (17*u)-75*(Real.pi : ℂ)*Complex.exp (5*u))*
    Complex.exp (-(Real.pi : ℂ)*Complex.exp (4*u))

theorem kernelSecond_remainder (u : ℂ) (hu : 0 < (Complex.exp (4*u)).re) :
    kernelSecond u-leadingSecond u=
      330*(Real.pi : ℂ)^2*Complex.exp (9*u)*complexThetaTail 4 1 (Complex.exp (4*u))-
      224*(Real.pi : ℂ)^3*Complex.exp (13*u)*complexThetaTail 6 1 (Complex.exp (4*u))+
      32*(Real.pi : ℂ)^4*Complex.exp (17*u)*complexThetaTail 8 1 (Complex.exp (4*u))-
      75*(Real.pi : ℂ)*Complex.exp (5*u)*complexThetaTail 2 1 (Complex.exp (4*u)) := by
  unfold kernelSecond leadingSecond
  rw [moment_split 4 _ hu,moment_split 6 _ hu,moment_split 8 _ hu,moment_split 2 _ hu]
  simp only [complexThetaTerm, Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add,
    one_pow, one_mul, Complex.ofReal_neg, Complex.ofReal_one, neg_mul]
  ring

theorem leading_hessian_identity (u : ℂ) :
    leadingSecond u*leading u-(RiemannThetaDerivativeBounds.leadingDerivative u)^2=
      -16*(Real.pi : ℂ)*Complex.exp (4*u)*(leading u)^2-
      96*(Real.pi : ℂ)*Complex.exp (4*u)*
        ((Real.pi : ℂ)*Complex.exp (5*u)*Complex.exp (-(Real.pi : ℂ)*Complex.exp (4*u)))^2 := by
  have h17 : Complex.exp (17*u)=Complex.exp (13*u)*Complex.exp (4*u) := by
    rw [← Complex.exp_add]; congr 1; ring
  have h13 : Complex.exp (13*u)=Complex.exp (9*u)*Complex.exp (4*u) := by
    rw [← Complex.exp_add]; congr 1; ring
  have h9 : Complex.exp (9*u)=Complex.exp (5*u)*Complex.exp (4*u) := by
    rw [← Complex.exp_add]; congr 1; ring
  unfold leadingSecond leading RiemannThetaDerivativeBounds.leadingDerivative
  rw [h17,h13,h9]
  ring

theorem quotient_perturbation (a A b B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    |a/A-b/B| ≤ |a-b|/A+|b| * |A-B|/(A*B) := by
  have he : a/A-b/B=(a-b)/A+b*(B-A)/(A*B) := by field_simp <;> ring
  rw [he]
  apply (abs_add_le _ _).trans_eq
  simp only [abs_div,abs_mul,abs_sub_comm B A,abs_of_pos hA,abs_of_pos hB]

theorem normalized_curvature_error (v r a0 a1 a2 f0 f1 f2 : ℝ)
    (hv : 3 ≤ v) (hr : 0 ≤ r) (hrmax : r ≤ 1/1024)
    (ha : 2*v ≤ a0) (hf : 3*v ≤ f0)
    (h0 : |a0-f0| ≤ 352*v*r)
    (h1 : |a1-f1| ≤ 20704*v^2*r)
    (h2 : |a2-f2| ≤ 568928*v^3*r)
    (hf1 : |f1| ≤ 263*v^2) (hf2 : |f2| ≤ 7027*v^3) :
    |(a2/a0-(a1/a0)^2)-(f2/f0-(f1/f0)^2)| ≤ 6000000*v^2*r := by
  have hv0 : 0 < v := by linarith
  have ha0 : 0 < a0 := by linarith
  have hf0 : 0 < f0 := by linarith
  have hq1 : |a1/a0-f1/f0| ≤ 26000*v*r := by
    calc
      _ ≤ |a1-f1|/a0+|f1| * |a0-f0|/(a0*f0) := quotient_perturbation _ _ _ _ ha0 hf0
      _ ≤ (20704*v^2*r)/a0+(263*v^2)*(352*v*r)/(a0*f0) := by gcongr
      _ ≤ (20704*v^2*r)/(2*v)+(263*v^2)*(352*v*r)/((2*v)*(3*v)) := by gcongr
      _ = (77344/3 : ℝ)*v*r := by field_simp <;> ring
      _ ≤ _ := by nlinarith [mul_nonneg hv0.le hr]
  have hq2 : |a2/a0-f2/f0| ≤ 700000*v^2*r := by
    calc
      _ ≤ |a2-f2|/a0+|f2| * |a0-f0|/(a0*f0) := quotient_perturbation _ _ _ _ ha0 hf0
      _ ≤ (568928*v^3*r)/a0+(7027*v^3)*(352*v*r)/(a0*f0) := by gcongr
      _ ≤ (568928*v^3*r)/(2*v)+(7027*v^3)*(352*v*r)/((2*v)*(3*v)) := by gcongr
      _ = (2090144/3 : ℝ)*v^2*r := by field_simp <;> ring
      _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg v) hr]
  have hl : |f1/f0| ≤ 88*v := by
    rw [abs_div,abs_of_pos hf0]
    calc
      _ ≤ (263*v^2)/f0 := div_le_div_of_nonneg_right hf1 hf0.le
      _ ≤ (263*v^2)/(3*v) := div_le_div_of_nonneg_left (by positivity) (by positivity) hf
      _ = (263/3 : ℝ)*v := by field_simp <;> ring
      _ ≤ _ := by linarith
  have hactual : |a1/a0| ≤ 114*v := by
    have hh := abs_sub_abs_le_abs_sub (a1/a0) (f1/f0)
    have he := mul_le_mul_of_nonneg_left hrmax (by positivity : 0 ≤ 26000*v)
    nlinarith
  have hsquare : |(a1/a0)^2-(f1/f0)^2| ≤ 5252000*v^2*r := by
    rw [show (a1/a0)^2-(f1/f0)^2=(a1/a0-f1/f0)*(a1/a0+f1/f0) by ring,abs_mul]
    calc
      _ ≤ (26000*v*r)*(114*v+88*v) := by
        apply mul_le_mul hq1 ((abs_add_le _ _).trans (add_le_add hactual hl))
          (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have he : (a2/a0-(a1/a0)^2)-(f2/f0-(f1/f0)^2)=
      (a2/a0-f2/f0)-((a1/a0)^2-(f1/f0)^2) := by ring
  rw [he]
  exact (abs_sub _ _).trans ((add_le_add hq2 hsquare).trans (by
    nlinarith [mul_nonneg (sq_nonneg v) hr]))

theorem curvature_error_small (v : ℝ) (hv : 16 ≤ v) :
    6000000*v^2*Real.exp (-Real.pi*v) ≤ 1 := by
  have hv0 : 0 < v := by linarith
  have h8 : (16 : ℝ)^8 ≤ v^8 := pow_le_pow_left₀ (by norm_num) hv 8
  have hc : (6000000 : ℝ) ≤ 3^10*v^8/(Nat.factorial 10) := by
    calc
      (6000000 : ℝ) ≤ 3^10*(16 : ℝ)^8/(Nat.factorial 10) := by norm_num
      _ ≤ _ := by gcongr
  have hpoly : 6000000*v^2 ≤ (3*v)^10/(Nat.factorial 10) := by
    calc
      _ ≤ (3^10*v^8/(Nat.factorial 10))*v^2 :=
        mul_le_mul_of_nonneg_right hc (sq_nonneg v)
      _ = _ := by ring
  have hExp := Real.pow_div_factorial_le_exp (Real.pi*v) (by positivity) 10
  rw [show -Real.pi*v=-(Real.pi*v) by ring,Real.exp_neg,← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  simp only [one_mul]
  apply hpoly.trans
  apply le_trans _ hExp
  gcongr
  exact Real.pi_gt_three.le

def normalizedMoment (k : ℕ) (v : ℝ) : ℝ := Real.exp (Real.pi*v)*thetaMoment k v

theorem moment_split_real (k : ℕ) (v : ℝ) (hv : 0 < v) :
    thetaMoment k v=Real.exp (-Real.pi*v)+RiemannThetaEffective.tail k 1 v := by
  have hs := (thetaTerm_summable k v hv).sum_add_tsum_nat_add 1
  have he : thetaMoment k v=thetaTerm k v 0+RiemannThetaEffective.tail k 1 v := by
    simpa only [thetaMoment,RiemannThetaEffective.tail,Finset.sum_range_one,Nat.add_comm] using hs.symm
  simpa [thetaTerm] using he

theorem complex_tail_real (k N : ℕ) (v : ℝ) (hv : 0 < v) :
    complexThetaTail k N (v : ℂ)=(RiemannThetaEffective.tail k N v : ℂ) := by
  have h := Complex.ofRealCLM.map_tsum (RiemannThetaEffective.tail_summable k N v hv)
  change (RiemannThetaEffective.tail k N v : ℂ)=∑' n, (thetaTerm k v (N+n) : ℂ) at h
  rw [h]
  apply tsum_congr
  intro n
  exact term_real k v (N+n)

theorem normalizedMoment_error (k : ℕ) (v C a : ℝ) (hv : 0 < v)
    (ht : ‖complexThetaTail k 1 (v : ℂ)‖ ≤ C*Real.exp (-a*Real.pi*v)) :
    |normalizedMoment k v-1| ≤ C*Real.exp ((1-a)*Real.pi*v) := by
  rw [complex_tail_real k 1 v hv,Complex.norm_real,Real.norm_eq_abs] at ht
  have he : Real.exp (Real.pi*v)*Real.exp (-Real.pi*v)=1 := by
    rw [← Real.exp_add]
    simp
  have hs : normalizedMoment k v-1=Real.exp (Real.pi*v)*RiemannThetaEffective.tail k 1 v := by
    rw [normalizedMoment,moment_split_real k v hv]
    nlinarith
  rw [hs,abs_mul,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (Real.pi*v)*(C*Real.exp (-a*Real.pi*v)) :=
      mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le
    _ = C*(Real.exp (Real.pi*v)*Real.exp (-a*Real.pi*v)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 1; congr 1; ring

theorem normalizedMoment_four_error (k : ℕ) (hk : k ≤ 4) (v : ℝ) (hv : 1 ≤ v) :
    |normalizedMoment k v-1| ≤ 32*Real.exp (-3*Real.pi*v) := by
  have ht := RiemannThetaDerivativeBounds.complex_tail_four_bound k hk (v : ℂ)
    (by simpa only [Complex.ofReal_re] using (show (1/2 : ℝ) ≤ v by linarith))
  have he := normalizedMoment_error k v 32 4 (by linarith) ht
  norm_num at he
  simpa only [neg_mul] using he

theorem normalizedMoment_six_error (v : ℝ) (hv : 1 ≤ v) :
    |normalizedMoment 6 v-1| ≤ 128*Real.exp (-3*Real.pi*v) := by
  have ht := RiemannThetaDerivativeBounds.complex_tail_six_bound (v : ℂ)
    (by simpa only [Complex.ofReal_re] using hv)
  have he := normalizedMoment_error 6 v 128 4 (by linarith) ht
  norm_num at he
  simpa only [neg_mul] using he

theorem normalizedMoment_eight_error (v : ℝ) (hv : 1 ≤ v) :
    |normalizedMoment 8 v-1| ≤ 32*Real.exp (-Real.pi*v) := by
  have ht := complex_tail_eight_bound (v : ℂ) (by simpa only [Complex.ofReal_re] using hv)
  have he := normalizedMoment_error 8 v 32 2 (by linarith) ht
  norm_num at he
  simpa only [neg_mul] using he

theorem normalizedMoment_ge_one (k : ℕ) (v : ℝ) (hv : 0 < v) :
    1 ≤ normalizedMoment k v := by
  have hs := (thetaTerm_summable k v hv).le_tsum 0 (fun n _ => thetaTerm_nonneg k v n)
  have ht : Real.exp (-Real.pi*v) ≤ thetaMoment k v := by simpa [thetaTerm,thetaMoment] using hs
  have he : Real.exp (Real.pi*v)*Real.exp (-Real.pi*v)=1 := by rw [← Real.exp_add]; simp
  rw [normalizedMoment,← he]
  exact mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le

theorem normalizedMoment_order (k l : ℕ) (hkl : k ≤ l) (v : ℝ) (hv : 0 < v) :
    normalizedMoment k v ≤ normalizedMoment l v := by
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact (thetaTerm_summable k v hv).tsum_le_tsum
    (fun n => RiemannThetaEffective.thetaTerm_order_le k l n hkl v)
    (thetaTerm_summable l v hv)

def coefficient0 (v : ℝ) : ℝ := 2*Real.pi*v*normalizedMoment 4 v-3*normalizedMoment 2 v

def coefficient1 (v : ℝ) : ℝ :=
  30*Real.pi*v*normalizedMoment 4 v-8*Real.pi^2*v^2*normalizedMoment 6 v-15*normalizedMoment 2 v

def coefficient2 (v : ℝ) : ℝ :=
  330*Real.pi*v*normalizedMoment 4 v-224*Real.pi^2*v^2*normalizedMoment 6 v+
    32*Real.pi^3*v^3*normalizedMoment 8 v-75*normalizedMoment 2 v

def leading0 (v : ℝ) : ℝ := 2*Real.pi*v-3

def leading1 (v : ℝ) : ℝ := 30*Real.pi*v-8*Real.pi^2*v^2-15

def leading2 (v : ℝ) : ℝ := 330*Real.pi*v-224*Real.pi^2*v^2+32*Real.pi^3*v^3-75

theorem leading0_lower (v : ℝ) (hv : 1 ≤ v) : 3*v ≤ leading0 v := by
  have hp := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (by linarith : 0 ≤ v)
  unfold leading0
  nlinarith

theorem coefficient0_lower (v : ℝ) (hv : 1 ≤ v) : 3*v ≤ coefficient0 v := by
  have h2 := normalizedMoment_ge_one 2 v (by linarith)
  have h42 := normalizedMoment_order 2 4 (by norm_num) v (by linarith)
  have hf := leading0_lower v hv
  have hf0 : 0 ≤ leading0 v := by linarith
  calc
    _ ≤ leading0 v := hf
    _ ≤ leading0 v*normalizedMoment 2 v := by
      simpa using mul_le_mul_of_nonneg_left h2 hf0
    _ ≤ leading0 v*normalizedMoment 2 v+
        2*Real.pi*v*(normalizedMoment 4 v-normalizedMoment 2 v) := by
      exact le_add_of_nonneg_right (mul_nonneg (by positivity) (sub_nonneg.mpr h42))
    _ = _ := by unfold leading0 coefficient0; ring

theorem normalizedMoment_four_weak (k : ℕ) (hk : k ≤ 4) (v : ℝ) (hv : 1 ≤ v) :
    |normalizedMoment k v-1| ≤ 32*Real.exp (-Real.pi*v) := by
  apply (normalizedMoment_four_error k hk v hv).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  nlinarith [Real.pi_pos]

theorem normalizedMoment_six_weak (v : ℝ) (hv : 1 ≤ v) :
    |normalizedMoment 6 v-1| ≤ 128*Real.exp (-Real.pi*v) := by
  apply (normalizedMoment_six_error v hv).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  nlinarith [Real.pi_pos]

theorem coefficient0_error (v : ℝ) (hv : 1 ≤ v) :
    |coefficient0 v-leading0 v| ≤ 352*v*Real.exp (-Real.pi*v) := by
  have h4 := normalizedMoment_four_weak 4 le_rfl v hv
  have h2 := normalizedMoment_four_weak 2 (by norm_num) v hv
  have he : coefficient0 v-leading0 v=
      2*Real.pi*v*(normalizedMoment 4 v-1)-3*(normalizedMoment 2 v-1) := by
    unfold coefficient0 leading0
    ring
  rw [he]
  calc
    _ ≤ |2*Real.pi*v*(normalizedMoment 4 v-1)|+|3*(normalizedMoment 2 v-1)| := abs_sub _ _
    _ = 2*Real.pi*v*|normalizedMoment 4 v-1|+3*|normalizedMoment 2 v-1| := by
      simp only [abs_mul,abs_of_nonneg (by linarith : 0 ≤ v),abs_of_pos Real.pi_pos]
      norm_num
    _ ≤ 2*Real.pi*v*(32*Real.exp (-Real.pi*v))+3*(32*Real.exp (-Real.pi*v)) := by gcongr
    _ = (64*Real.pi*v+96)*Real.exp (-Real.pi*v) := by ring
    _ ≤ _ := by
      have hp := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (by linarith : 0 ≤ v)
      have hc : 64*Real.pi*v+96 ≤ 352*v := by nlinarith
      exact mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le

theorem coefficient1_error (v : ℝ) (hv : 1 ≤ v) :
    |coefficient1 v-leading1 v| ≤ 20704*v^2*Real.exp (-Real.pi*v) := by
  have hv0 : 0 ≤ v := by linarith
  have hv2 : v ≤ v^2 := by nlinarith [sq_nonneg (v-1)]
  have hv12 : 1 ≤ v^2 := by linarith
  have h4 := normalizedMoment_four_weak 4 le_rfl v hv
  have h2 := normalizedMoment_four_weak 2 (by norm_num) v hv
  have h6 := normalizedMoment_six_weak v hv
  have he : coefficient1 v-leading1 v=
      30*Real.pi*v*(normalizedMoment 4 v-1)-8*Real.pi^2*v^2*(normalizedMoment 6 v-1)-
        15*(normalizedMoment 2 v-1) := by unfold coefficient1 leading1; ring
  rw [he]
  calc
    _ ≤ |30*Real.pi*v*(normalizedMoment 4 v-1)-8*Real.pi^2*v^2*(normalizedMoment 6 v-1)|+
        |15*(normalizedMoment 2 v-1)| := abs_sub _ _
    _ ≤ |30*Real.pi*v*(normalizedMoment 4 v-1)|+|8*Real.pi^2*v^2*(normalizedMoment 6 v-1)|+
        |15*(normalizedMoment 2 v-1)| := by gcongr; exact abs_sub _ _
    _ = 30*Real.pi*v*|normalizedMoment 4 v-1|+8*Real.pi^2*v^2*|normalizedMoment 6 v-1|+
        15*|normalizedMoment 2 v-1| := by
      simp only [abs_mul,abs_pow,abs_of_nonneg hv0,abs_of_pos Real.pi_pos]
      norm_num
    _ ≤ 30*Real.pi*v*(32*Real.exp (-Real.pi*v))+8*Real.pi^2*v^2*(128*Real.exp (-Real.pi*v))+
        15*(32*Real.exp (-Real.pi*v)) := by gcongr
    _ = (960*Real.pi*v+1024*Real.pi^2*v^2+480)*Real.exp (-Real.pi*v) := by ring
    _ ≤ _ := by
      have hp1 : Real.pi*v ≤ 4*v^2 := by
        exact (mul_le_mul_of_nonneg_right Real.pi_lt_four.le hv0).trans
          (mul_le_mul_of_nonneg_left hv2 (by norm_num))
      have hpi2 : Real.pi^2 ≤ 16 := by nlinarith [Real.pi_lt_four,Real.pi_pos]
      have hp2 := mul_le_mul_of_nonneg_right hpi2 (sq_nonneg v)
      have hc : 960*Real.pi*v+1024*Real.pi^2*v^2+480 ≤ 20704*v^2 := by nlinarith
      exact mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le

theorem coefficient2_error (v : ℝ) (hv : 1 ≤ v) :
    |coefficient2 v-leading2 v| ≤ 568928*v^3*Real.exp (-Real.pi*v) := by
  have hv0 : 0 ≤ v := by linarith
  have hv2 : v ≤ v^2 := by nlinarith [sq_nonneg (v-1)]
  have hv23 : v^2 ≤ v^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hv) (sq_nonneg v)]
  have hv3 : v ≤ v^3 := hv2.trans hv23
  have hv13 : 1 ≤ v^3 := hv.trans hv3
  have h4 := normalizedMoment_four_weak 4 le_rfl v hv
  have h2 := normalizedMoment_four_weak 2 (by norm_num) v hv
  have h6 := normalizedMoment_six_weak v hv
  have h8 := normalizedMoment_eight_error v hv
  have he : coefficient2 v-leading2 v=
      (330*Real.pi*v*(normalizedMoment 4 v-1)-224*Real.pi^2*v^2*(normalizedMoment 6 v-1))+
      32*Real.pi^3*v^3*(normalizedMoment 8 v-1)-75*(normalizedMoment 2 v-1) := by
    unfold coefficient2 leading2
    ring
  rw [he]
  calc
    _ ≤ |(330*Real.pi*v*(normalizedMoment 4 v-1)-224*Real.pi^2*v^2*(normalizedMoment 6 v-1))+
        32*Real.pi^3*v^3*(normalizedMoment 8 v-1)|+|75*(normalizedMoment 2 v-1)| := abs_sub _ _
    _ ≤ (|330*Real.pi*v*(normalizedMoment 4 v-1)-224*Real.pi^2*v^2*(normalizedMoment 6 v-1)|+
        |32*Real.pi^3*v^3*(normalizedMoment 8 v-1)|)+|75*(normalizedMoment 2 v-1)| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ ((|330*Real.pi*v*(normalizedMoment 4 v-1)|+|224*Real.pi^2*v^2*(normalizedMoment 6 v-1)|)+
        |32*Real.pi^3*v^3*(normalizedMoment 8 v-1)|)+|75*(normalizedMoment 2 v-1)| := by
      gcongr
      exact abs_sub _ _
    _ = 330*Real.pi*v*|normalizedMoment 4 v-1|+224*Real.pi^2*v^2*|normalizedMoment 6 v-1|+
        32*Real.pi^3*v^3*|normalizedMoment 8 v-1|+75*|normalizedMoment 2 v-1| := by
      simp only [abs_mul,abs_pow,abs_of_nonneg hv0,abs_of_pos Real.pi_pos]
      norm_num
    _ ≤ 330*Real.pi*v*(32*Real.exp (-Real.pi*v))+224*Real.pi^2*v^2*(128*Real.exp (-Real.pi*v))+
        32*Real.pi^3*v^3*(32*Real.exp (-Real.pi*v))+75*(32*Real.exp (-Real.pi*v)) := by gcongr
    _ = (10560*Real.pi*v+28672*Real.pi^2*v^2+1024*Real.pi^3*v^3+2400)*Real.exp (-Real.pi*v) := by ring
    _ ≤ _ := by
      have hp1 : Real.pi*v ≤ 4*v^3 := by
        exact (mul_le_mul_of_nonneg_right Real.pi_lt_four.le hv0).trans
          (mul_le_mul_of_nonneg_left hv3 (by norm_num))
      have hpi2 : Real.pi^2 ≤ 16 := by nlinarith [Real.pi_lt_four,Real.pi_pos]
      have hp2 : Real.pi^2*v^2 ≤ 16*v^3 :=
        (mul_le_mul_of_nonneg_right hpi2 (sq_nonneg v)).trans
          (mul_le_mul_of_nonneg_left hv23 (by norm_num))
      have hpi3 : Real.pi^3 ≤ 64 := by
        have hp := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_four.le 3
        norm_num at hp
        exact hp
      have hp3 := mul_le_mul_of_nonneg_right hpi3 (pow_nonneg hv0 3)
      have hc : 10560*Real.pi*v+28672*Real.pi^2*v^2+1024*Real.pi^3*v^3+2400 ≤ 568928*v^3 := by nlinarith
      exact mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le

theorem leading1_bound (v : ℝ) (hv : 1 ≤ v) : |leading1 v| ≤ 263*v^2 := by
  have hv0 : 0 ≤ v := by linarith
  have hv2 : v ≤ v^2 := by nlinarith [sq_nonneg (v-1)]
  have hv12 : 1 ≤ v^2 := by linarith
  have hp1 : Real.pi*v ≤ 4*v^2 :=
    (mul_le_mul_of_nonneg_right Real.pi_lt_four.le hv0).trans
      (mul_le_mul_of_nonneg_left hv2 (by norm_num))
  have hpi2 : Real.pi^2 ≤ 16 := by nlinarith [Real.pi_lt_four,Real.pi_pos]
  have hp2 := mul_le_mul_of_nonneg_right hpi2 (sq_nonneg v)
  have hn1 := mul_nonneg Real.pi_pos.le hv0
  have hn2 := mul_nonneg (sq_nonneg Real.pi) (sq_nonneg v)
  unfold leading1
  apply abs_le.mpr
  constructor <;> nlinarith

theorem leading2_bound (v : ℝ) (hv : 1 ≤ v) : |leading2 v| ≤ 7027*v^3 := by
  have hv0 : 0 ≤ v := by linarith
  have hv2 : v ≤ v^2 := by nlinarith [sq_nonneg (v-1)]
  have hv23 : v^2 ≤ v^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hv) (sq_nonneg v)]
  have hv3 : v ≤ v^3 := hv2.trans hv23
  have hv13 : 1 ≤ v^3 := hv.trans hv3
  have hp1 : Real.pi*v ≤ 4*v^3 :=
    (mul_le_mul_of_nonneg_right Real.pi_lt_four.le hv0).trans
      (mul_le_mul_of_nonneg_left hv3 (by norm_num))
  have hpi2 : Real.pi^2 ≤ 16 := by nlinarith [Real.pi_lt_four,Real.pi_pos]
  have hp2 : Real.pi^2*v^2 ≤ 16*v^3 :=
    (mul_le_mul_of_nonneg_right hpi2 (sq_nonneg v)).trans
      (mul_le_mul_of_nonneg_left hv23 (by norm_num))
  have hpi3 : Real.pi^3 ≤ 64 := by
    have hp := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_four.le 3
    norm_num at hp
    exact hp
  have hp3 := mul_le_mul_of_nonneg_right hpi3 (pow_nonneg hv0 3)
  have hn1 := mul_nonneg Real.pi_pos.le hv0
  have hn2 := mul_nonneg (sq_nonneg Real.pi) (sq_nonneg v)
  have hn3 := mul_nonneg (pow_nonneg Real.pi_pos.le 3) (pow_nonneg hv0 3)
  unfold leading2
  apply abs_le.mpr
  constructor <;> nlinarith

theorem coefficient_curvature_bound (v : ℝ) (hv : 16 ≤ v) :
    |(coefficient2 v/coefficient0 v-(coefficient1 v/coefficient0 v)^2)-
      (leading2 v/leading0 v-(leading1 v/leading0 v)^2)| ≤ 1 := by
  have hv1 : 1 ≤ v := by linarith
  have ha := coefficient0_lower v hv1
  have hf := leading0_lower v hv1
  have hr : Real.exp (-Real.pi*v) ≤ 1/1024 := by
    have h := RiemannThetaDerivativeBounds.ratioSix_le_sixteenth (v/3) (by linarith)
    unfold RiemannThetaDerivativeBounds.ratioSix at h
    rw [show -3*Real.pi*(v/3)=-Real.pi*v by ring] at h
    linarith
  have he := normalized_curvature_error v (Real.exp (-Real.pi*v))
    (coefficient0 v) (coefficient1 v) (coefficient2 v) (leading0 v) (leading1 v) (leading2 v)
    (by linarith) (Real.exp_pos _).le hr (by linarith) hf
    (coefficient0_error v hv1) (coefficient1_error v hv1) (coefficient2_error v hv1)
    (leading1_bound v hv1) (leading2_bound v hv1)
  exact he.trans (curvature_error_small v hv)

def scale (u : ℝ) : ℝ := Real.pi*Real.exp (5*u)*Real.exp (-Real.pi*Real.exp (4*u))

theorem scale_pos (u : ℝ) : 0 < scale u := by unfold scale; positivity

theorem scale_moment (k : ℕ) (u : ℝ) :
    scale u*normalizedMoment k (Real.exp (4*u))=
      Real.pi*Real.exp (5*u)*thetaMoment k (Real.exp (4*u)) := by
  have he : Real.exp (-Real.pi*Real.exp (4*u))*Real.exp (Real.pi*Real.exp (4*u))=1 := by
    rw [← Real.exp_add]
    simp
  unfold scale normalizedMoment
  calc
    _ = Real.pi*Real.exp (5*u)*
        (Real.exp (-Real.pi*Real.exp (4*u))*Real.exp (Real.pi*Real.exp (4*u)))*
        thetaMoment k (Real.exp (4*u)) := by ring
    _ = _ := by rw [he]; ring

theorem exp_shift (u : ℝ) (n : ℕ) :
    Real.exp ((5+4*(n : ℝ))*u)=Real.exp (5*u)*(Real.exp (4*u))^n := by
  rw [← Real.exp_nat_mul,← Real.exp_add]
  congr 1
  ring

theorem kernel_scale (u : ℝ) : kernel u=scale u*coefficient0 (Real.exp (4*u)) := by
  have h9 : Real.exp (9*u)=Real.exp (5*u)*Real.exp (4*u) := by convert exp_shift u 1 using 1 <;> norm_num
  symm
  unfold coefficient0
  calc
    _ = 2*Real.pi*Real.exp (4*u)*(scale u*normalizedMoment 4 (Real.exp (4*u)))-
        3*(scale u*normalizedMoment 2 (Real.exp (4*u))) := by ring
    _ = _ := by rw [scale_moment,scale_moment]; unfold kernel; rw [h9]; ring

theorem kernelPrime_scale (u : ℝ) :
    deriv kernel u=scale u*coefficient1 (Real.exp (4*u)) := by
  rw [(RiemannQuarticRealSaddle.kernel_hasDerivAt u).deriv,
    RiemannQuarticRealSaddle.kernelDerivative_real,Complex.ofReal_re]
  have h9 : Real.exp (9*u)=Real.exp (5*u)*Real.exp (4*u) := by convert exp_shift u 1 using 1 <;> norm_num
  have h13 : Real.exp (13*u)=Real.exp (5*u)*(Real.exp (4*u))^2 := by convert exp_shift u 2 using 1 <;> norm_num
  symm
  unfold coefficient1
  calc
    _ = 30*Real.pi*Real.exp (4*u)*(scale u*normalizedMoment 4 (Real.exp (4*u)))-
        8*Real.pi^2*(Real.exp (4*u))^2*(scale u*normalizedMoment 6 (Real.exp (4*u)))-
        15*(scale u*normalizedMoment 2 (Real.exp (4*u))) := by ring
    _ = _ := by rw [scale_moment,scale_moment,scale_moment,h9,h13]; ring

theorem kernelSecond_real (u : ℝ) :
    kernelSecond (u : ℂ)=
      ((330*Real.pi^2*Real.exp (9*u)*thetaMoment 4 (Real.exp (4*u))-
        224*Real.pi^3*Real.exp (13*u)*thetaMoment 6 (Real.exp (4*u))+
        32*Real.pi^4*Real.exp (17*u)*thetaMoment 8 (Real.exp (4*u))-
        75*Real.pi*Real.exp (5*u)*thetaMoment 2 (Real.exp (4*u)) : ℝ) : ℂ) := by
  have he (a : ℝ) : Complex.exp ((a : ℂ)*(u : ℂ))=(Real.exp (a*u) : ℂ) := by
    rw [← Complex.ofReal_mul,← Complex.ofReal_exp]
  unfold kernelSecond
  rw [show (4 : ℂ)=((4 : ℝ) : ℂ) by norm_num,he 4]
  rw [moment_real 4 _ (Real.exp_pos _),moment_real 6 _ (Real.exp_pos _),
    moment_real 8 _ (Real.exp_pos _),moment_real 2 _ (Real.exp_pos _)]
  rw [show (9 : ℂ)=((9 : ℝ) : ℂ) by norm_num,he 9,
    show (13 : ℂ)=((13 : ℝ) : ℂ) by norm_num,he 13,
    show (17 : ℂ)=((17 : ℝ) : ℂ) by norm_num,he 17,
    show (5 : ℂ)=((5 : ℝ) : ℂ) by norm_num,he 5]
  push_cast
  rfl

theorem kernelSecond_scale (u : ℝ) :
    (kernelSecond (u : ℂ)).re=scale u*coefficient2 (Real.exp (4*u)) := by
  rw [kernelSecond_real,Complex.ofReal_re]
  have h9 : Real.exp (9*u)=Real.exp (5*u)*Real.exp (4*u) := by convert exp_shift u 1 using 1 <;> norm_num
  have h13 : Real.exp (13*u)=Real.exp (5*u)*(Real.exp (4*u))^2 := by convert exp_shift u 2 using 1 <;> norm_num
  have h17 : Real.exp (17*u)=Real.exp (5*u)*(Real.exp (4*u))^3 := by convert exp_shift u 3 using 1 <;> norm_num
  symm
  unfold coefficient2
  calc
    _ = 330*Real.pi*Real.exp (4*u)*(scale u*normalizedMoment 4 (Real.exp (4*u)))-
        224*Real.pi^2*(Real.exp (4*u))^2*(scale u*normalizedMoment 6 (Real.exp (4*u)))+
        32*Real.pi^3*(Real.exp (4*u))^3*(scale u*normalizedMoment 8 (Real.exp (4*u)))-
        75*(scale u*normalizedMoment 2 (Real.exp (4*u))) := by ring
    _ = _ := by rw [scale_moment,scale_moment,scale_moment,scale_moment,h9,h13,h17]; ring

def realLogCurvature (u : ℝ) : ℝ :=
  (kernelSecond (u : ℂ)).re/kernel u-(deriv kernel u/kernel u)^2

theorem realLogCurvature_coefficients (u : ℝ) (hu : 0 ≤ u) :
    realLogCurvature u=coefficient2 (Real.exp (4*u))/coefficient0 (Real.exp (4*u))-
      (coefficient1 (Real.exp (4*u))/coefficient0 (Real.exp (4*u)))^2 := by
  have hv : 1 ≤ Real.exp (4*u) := Real.one_le_exp (by positivity)
  have ha := coefficient0_lower (Real.exp (4*u)) hv
  have hn : coefficient0 (Real.exp (4*u)) ≠ 0 := ne_of_gt (by nlinarith [Real.exp_pos (4*u)])
  unfold realLogCurvature
  rw [kernelSecond_scale,kernelPrime_scale,kernel_scale]
  field_simp [ne_of_gt (scale_pos u),hn] <;> ring

theorem leading_curvature_formula (v : ℝ) (hv : 1 ≤ v) :
    leading2 v/leading0 v-(leading1 v/leading0 v)^2=
      -16*Real.pi*v-96*Real.pi*v/(leading0 v)^2 := by
  have hl := leading0_lower v hv
  have hn : leading0 v ≠ 0 := ne_of_gt (by linarith)
  have hs : (leading0 v)^2 ≠ 0 := pow_ne_zero 2 hn
  have he : leading2 v/leading0 v-(leading1 v/leading0 v)^2=
      (leading2 v*leading0 v-(leading1 v)^2)/(leading0 v)^2 := by
    field_simp [hn] <;> ring
  rw [he]
  apply (div_eq_iff hs).mpr
  rw [sub_mul,div_mul_cancel₀ _ hs]
  unfold leading0 leading1 leading2
  ring

theorem exp_four_ge_sixteen (u : ℝ) (hu : 1 ≤ u) : 16 ≤ Real.exp (4*u) := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by have h := Real.add_one_le_exp (1 : ℝ); linarith
  calc
    (16 : ℝ)=2^4 := by norm_num
    _ ≤ (Real.exp 1)^4 := pow_le_pow_left₀ (by norm_num) he 4
    _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem realLogCurvature_bound (u : ℝ) (hu : 1 ≤ u) :
    |realLogCurvature u-(-16*Real.pi*Real.exp (4*u)-
      96*Real.pi*Real.exp (4*u)/(leading0 (Real.exp (4*u)))^2)| ≤ 1 := by
  have hv := exp_four_ge_sixteen u hu
  rw [realLogCurvature_coefficients u (by linarith),
    ← leading_curvature_formula (Real.exp (4*u)) (by linarith)]
  exact coefficient_curvature_bound (Real.exp (4*u)) hv

theorem realLogSlope_hasDerivAt (u : ℝ) (hu : 0 ≤ u) :
    HasDerivAt (fun w => deriv kernel w/kernel w) (realLogCurvature u) u := by
  have he : 0 < (Complex.exp (4*(u : ℂ))).re := by
    simpa only [← Complex.ofReal_ofNat,← Complex.ofReal_mul,← Complex.ofReal_exp,
      Complex.ofReal_re] using Real.exp_pos (4*u)
  have h2 : HasDerivAt (deriv kernel) (kernelSecond (u : ℂ)).re u := by
    convert (kernelDerivative_hasDerivAt (u : ℂ) he).real_of_complex using 1
    funext w
    exact (RiemannQuarticRealSaddle.kernel_hasDerivAt w).deriv
  have hk : kernel u ≠ 0 := ne_of_gt (kernel_pos u hu)
  have hd := h2.div (RiemannQuarticRealSaddle.kernel_hasDerivAt u) hk
  rw [← (RiemannQuarticRealSaddle.kernel_hasDerivAt u).deriv] at hd
  convert hd using 1
  unfold realLogCurvature
  field_simp <;> ring

theorem coefficient_slope_bound (v : ℝ) (hv : 16 ≤ v) :
    |coefficient1 v/coefficient0 v-leading1 v/leading0 v| ≤ 1 := by
  have hv0 : 0 < v := by linarith
  have hv1 : 1 ≤ v := by linarith
  have ha := coefficient0_lower v hv1
  have ha2 : 2*v ≤ coefficient0 v := by linarith
  have hf := leading0_lower v hv1
  have ha0 : 0 < coefficient0 v := by linarith
  have hf0 : 0 < leading0 v := by linarith
  have h0 := coefficient0_error v hv1
  have h1 := coefficient1_error v hv1
  have hf1 := leading1_bound v hv1
  calc
    _ ≤ |coefficient1 v-leading1 v|/coefficient0 v+
        |leading1 v| * |coefficient0 v-leading0 v|/(coefficient0 v*leading0 v) :=
      quotient_perturbation _ _ _ _ ha0 hf0
    _ ≤ (20704*v^2*Real.exp (-Real.pi*v))/coefficient0 v+
        (263*v^2)*(352*v*Real.exp (-Real.pi*v))/(coefficient0 v*leading0 v) := by gcongr
    _ ≤ (20704*v^2*Real.exp (-Real.pi*v))/(2*v)+
        (263*v^2)*(352*v*Real.exp (-Real.pi*v))/((2*v)*(3*v)) := by gcongr
    _ = (77344/3 : ℝ)*v*Real.exp (-Real.pi*v) := by field_simp <;> ring
    _ ≤ 26000*v*Real.exp (-Real.pi*v) := by gcongr; norm_num
    _ ≤ 6000000*v^2*Real.exp (-Real.pi*v) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      have h := mul_le_mul_of_nonneg_right (by linarith : 26000 ≤ 6000000*v) hv0.le
      nlinarith
    _ ≤ 1 := curvature_error_small v hv

theorem leading_slope_formula (v : ℝ) (hv : 1 ≤ v) :
    leading1 v/leading0 v=9-4*Real.pi*v+12/leading0 v := by
  have hl := leading0_lower v hv
  have hn : leading0 v ≠ 0 := ne_of_gt (by linarith)
  apply (div_eq_iff hn).mpr
  rw [add_mul,div_mul_cancel₀ _ hn]
  unfold leading0 leading1
  ring

theorem realLogSlope_coefficients (u : ℝ) (hu : 0 ≤ u) :
    deriv kernel u/kernel u=coefficient1 (Real.exp (4*u))/coefficient0 (Real.exp (4*u)) := by
  have hv : 1 ≤ Real.exp (4*u) := Real.one_le_exp (by positivity)
  have ha := coefficient0_lower (Real.exp (4*u)) hv
  have hn : coefficient0 (Real.exp (4*u)) ≠ 0 := ne_of_gt (by nlinarith [Real.exp_pos (4*u)])
  rw [kernelPrime_scale,kernel_scale]
  field_simp [ne_of_gt (scale_pos u),hn] <;> ring

theorem realLogSlope_bound (u : ℝ) (hu : 1 ≤ u) :
    |deriv kernel u/kernel u-(9-4*Real.pi*Real.exp (4*u)+12/leading0 (Real.exp (4*u)))| ≤ 1 := by
  have hv := exp_four_ge_sixteen u hu
  rw [realLogSlope_coefficients u (by linarith),← leading_slope_formula (Real.exp (4*u)) (by linarith)]
  exact coefficient_slope_bound (Real.exp (4*u)) hv

theorem realLogSlope_lower (u : ℝ) (hu : 1 ≤ u) :
    8-4*Real.pi*Real.exp (4*u) ≤ deriv kernel u/kernel u := by
  have hv := exp_four_ge_sixteen u hu
  have hf := leading0_lower (Real.exp (4*u)) (by linarith)
  have hp : 0 ≤ 12/leading0 (Real.exp (4*u)) := div_nonneg (by norm_num) (by linarith)
  have he := (abs_le.mp (realLogSlope_bound u hu)).1
  linarith

theorem realLogCurvature_upper (u : ℝ) (hu : 1 ≤ u) :
    realLogCurvature u ≤ -16*Real.pi*Real.exp (4*u)+1 := by
  have he := (abs_le.mp (realLogCurvature_bound u hu)).2
  have hp : 0 ≤ 96*Real.pi*Real.exp (4*u)/(leading0 (Real.exp (4*u)))^2 := by positivity
  linarith

theorem phaseSlope_real_hasDerivAt (t u : ℝ) (hu : 0 ≤ u) :
    HasDerivAt (RiemannQuarticSaddleTimes.phaseSlope t)
      (12*t*u^2+realLogCurvature u) u := by
  have h := (((hasDerivAt_id u).pow 3).const_mul (4*t)).add (realLogSlope_hasDerivAt u hu)
  convert h using 1
  · funext w
    rfl
  · simp only [id_eq]
    norm_num
    ring

theorem stationary_phaseSlope_deriv_upper (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : RiemannQuarticSaddleTimes.phaseSlope t u=0) :
    deriv (RiemannQuarticSaddleTimes.phaseSlope t) u ≤ -4*Real.pi*Real.exp (4*u)-23 := by
  have hl := realLogSlope_lower u hu
  have hc := realLogCurvature_upper u hu
  have hu0 : 0 ≤ u := by linarith
  have hu23 : u^2 ≤ u^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sq_nonneg u)]
  have hm := mul_le_mul_of_nonneg_left hu23 (by positivity : 0 ≤ 4*t)
  unfold RiemannQuarticSaddleTimes.phaseSlope at hs
  rw [(phaseSlope_real_hasDerivAt t u hu0).deriv]
  nlinarith

theorem stationary_phaseSlope_deriv_neg (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : RiemannQuarticSaddleTimes.phaseSlope t u=0) :
    deriv (RiemannQuarticSaddleTimes.phaseSlope t) u < 0 := by
  have h := stationary_phaseSlope_deriv_upper t u ht hu hs
  have hp := mul_pos Real.pi_pos (Real.exp_pos (4*u))
  nlinarith

theorem eventually_all_maxima_nondegenerate :
    ∀ᶠ t : ℝ in Filter.atTop, ∀ u ∈ Set.Ici (0 : ℝ),
      IsMaxOn (RiemannQuarticDomain.weighted 0 t 0) (Set.Ici 0) u →
        deriv (RiemannQuarticSaddleTimes.phaseSlope t) u < 0 := by
  filter_upwards [RiemannQuarticRealSaddle.maxima_escape 1 (by norm_num),
    Filter.eventually_ge_atTop (0 : ℝ)] with t ht ht0
  intro u hu hm
  have hu1 := ht u hu hm
  have hs := RiemannQuarticRealSaddle.max_real_stationary t u (by linarith) hm
  rw [← (RiemannQuarticRealSaddle.kernel_hasDerivAt u).deriv] at hs
  exact stationary_phaseSlope_deriv_neg t u ht0 hu1.le hs
open Filter Set RiemannQuarticDomain RiemannQuarticSaddleTimes RiemannQuarticRealSaddle

theorem realLogSlope_neg (u : ℝ) (hu : 1 ≤ u) : deriv kernel u/kernel u < 0 := by
  have hv := exp_four_ge_sixteen u hu
  have hf := leading0_lower (Real.exp (4*u)) (by linarith)
  have hf0 : 0 < leading0 (Real.exp (4*u)) := by linarith
  have hr : 12/leading0 (Real.exp (4*u)) ≤ 1 :=
    (div_le_iff₀ hf0).mpr (by linarith)
  have hs := (abs_le.mp (realLogSlope_bound u hu)).2
  have hp := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ 4*Real.pi)
  nlinarith [Real.pi_gt_three]

theorem saddleTime_pos (u : ℝ) (hu : 1 ≤ u) : 0 < saddleTime u := by
  unfold saddleTime
  exact div_pos (neg_pos.mpr (realLogSlope_neg u hu)) (by positivity)

theorem saddleTime_deriv_pos (u : ℝ) (hu : 1 ≤ u) : 0 < deriv saddleTime u := by
  have hu0 : 0 < u := by linarith
  have hs : phaseSlope (saddleTime u) u=0 := by rw [phaseSlope_factor _ _ hu0]; simp
  have hn := stationary_phaseSlope_deriv_neg (saddleTime u) u (saddleTime_pos u hu).le hu hs
  rw [(phaseSlope_hasDerivAt (saddleTime u) u hu0 rfl).deriv] at hn
  by_contra h
  have hd : deriv saddleTime u ≤ 0 := le_of_not_gt h
  have hp : 0 ≤ (-4*u^3)*deriv saddleTime u :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith [pow_nonneg hu0.le 3]) hd
  linarith

theorem saddleTime_strictMonoOn : StrictMonoOn saddleTime (Ici (1 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 1)
  · intro u hu
    exact (saddleTime_analyticAt u (by have h : 1 ≤ u := hu; linarith)).continuousAt.continuousWithinAt
  · intro u hu
    have hu1 : 1 < u := by simpa only [interior_Ici,mem_Ioi] using hu
    exact saddleTime_deriv_pos u hu1.le

theorem phaseSlope_zero_saddleTime (t u : ℝ) (hu : 0 < u) (hs : phaseSlope t u=0) :
    saddleTime u=t := by
  rw [phaseSlope_factor t u hu] at hs
  have hn : u^3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hu)
  have h := (mul_eq_zero.mp hs).resolve_right hn
  linarith

theorem large_stationary_unique (t u v : ℝ) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hsu : phaseSlope t u=0) (hsv : phaseSlope t v=0) : u=v := by
  apply saddleTime_strictMonoOn.injOn hu hv
  rw [phaseSlope_zero_saddleTime t u (by linarith) hsu,
    phaseSlope_zero_saddleTime t v (by linarith) hsv]

theorem eventually_unique_global_max :
    ∀ᶠ t : ℝ in atTop, ∃! u : ℝ, u ∈ Ici (0 : ℝ) ∧ IsMaxOn (weighted 0 t 0) (Ici 0) u := by
  filter_upwards [maxima_escape 1 (by norm_num)] with t ht
  obtain ⟨u,hu,hm⟩ := exists_global_max t
  refine ⟨u,⟨hu,hm⟩,?_⟩
  intro v hv
  apply saddleTime_strictMonoOn.injOn (ht v hv.1 hv.2).le (ht u hu hm).le
  rw [max_saddleTime t v (by have h := ht v hv.1 hv.2; linarith) hv.2,
    max_saddleTime t u (by have h := ht u hu hm; linarith) hm]

open RiemannQuarticSaddleBranch

theorem eventually_all_maxima_local_branches :
    ∀ᶠ t : ℝ in atTop, ∀ u ∈ Ici (0 : ℝ),
      IsMaxOn (weighted 0 t 0) (Ici 0) u →
      ∃ branch : ℂ → ℂ, branch 0=(u : ℂ) ∧ AnalyticAt ℂ branch 0 ∧
        HasStrictDerivAt branch (-Complex.I/deriv (complexSlope t) (u : ℂ)) 0 ∧
        ∀ᶠ z in nhds (0 : ℂ), complexSlope t (branch z)=-(Complex.I*z) ∧
          0 < (Complex.exp (4*branch z)).re ∧ kernelComplex (branch z) ≠ 0 := by
  filter_upwards [maxima_escape 1 (by norm_num),eventually_all_maxima_nondegenerate] with t he hn
  intro u hu hm
  have hu0 : 0 < u := by have h := he u hu hm; linarith
  have hreal : deriv (phaseSlope t) u ≠ 0 := ne_of_lt (hn u hu hm)
  have hc := complexSlope_deriv_ne_zero_of_real t u hu0 hreal
  exact exists_local_saddle_branch_of_deriv_ne_zero t u hu0 hm hc
theorem stationary_scale_bounds (t u : ℝ) (hu : 1 ≤ u) (hs : phaseSlope t u=0) :
    Real.pi*Real.exp (4*u)-3 ≤ t*u^3 ∧ t*u^3 ≤ Real.pi*Real.exp (4*u)-2 := by
  have hv := exp_four_ge_sixteen u hu
  have hf := leading0_lower (Real.exp (4*u)) (by linarith)
  have hf0 : 0 < leading0 (Real.exp (4*u)) := by linarith
  have hr : 12/leading0 (Real.exp (4*u)) ≤ 1 := (div_le_iff₀ hf0).mpr (by linarith)
  have hh := (abs_le.mp (realLogSlope_bound u hu)).2
  have hl := realLogSlope_lower u hu
  unfold phaseSlope at hs
  constructor <;> nlinarith

theorem leading_curvature_fraction_le_three (u : ℝ) (hu : 1 ≤ u) :
    96*Real.pi*Real.exp (4*u)/(leading0 (Real.exp (4*u)))^2 ≤ 3 := by
  have hv := exp_four_ge_sixteen u hu
  have hf := leading0_lower (Real.exp (4*u)) (by linarith)
  have hf0 : 0 < leading0 (Real.exp (4*u)) := by linarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 3*Real.exp (4*u)) hf 2
  norm_num [mul_pow] at hsq
  have hp := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (Real.exp_pos (4*u)).le
  have hm := mul_le_mul_of_nonneg_right
    (by linarith : (384 : ℝ) ≤ 27*Real.exp (4*u)) (Real.exp_pos (4*u)).le
  apply (div_le_iff₀ (sq_pos_of_pos hf0)).mpr
  nlinarith

theorem stationary_curvature_bounds (t u : ℝ) (hu : 1 ≤ u) (hs : phaseSlope t u=0) :
    4*t*u^2*(3-4*u)-52 ≤ deriv (phaseSlope t) u ∧
      deriv (phaseSlope t) u ≤ 4*t*u^2*(3-4*u)-31 := by
  have hscale := stationary_scale_bounds t u hu hs
  have hc := abs_le.mp (realLogCurvature_bound u hu)
  have hr := leading_curvature_fraction_le_three u hu
  have hupper := realLogCurvature_upper u hu
  rw [(phaseSlope_real_hasDerivAt t u (by linarith)).deriv]
  constructor <;> nlinarith

theorem stationary_abs_curvature_bounds (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : phaseSlope t u=0) :
    4*t*u^2*(4*u-3)+31 ≤ |deriv (phaseSlope t) u| ∧
      |deriv (phaseSlope t) u| ≤ 4*t*u^2*(4*u-3)+52 := by
  have h := stationary_curvature_bounds t u hu hs
  rw [abs_of_neg (stationary_phaseSlope_deriv_neg t u ht hu hs)]
  constructor <;> nlinarith

theorem stationary_curvature_relative (t u : ℝ) (ht : 0 < t) (hu : 1 ≤ u)
    (hs : phaseSlope t u=0) :
    abs (|deriv (phaseSlope t) u|/(4*t*u^2*(4*u-3))-1) ≤ 13/t := by
  let M := 4*t*u^2*(4*u-3)
  have hbound := stationary_abs_curvature_bounds t u ht.le hu hs
  have hu2 : 1 ≤ u^2 := by nlinarith [sq_nonneg (u-1)]
  have hu3 : 1 ≤ 4*u-3 := by linarith
  have hp := mul_le_mul hu2 hu3 (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ u^2)
  have hm : 4*t ≤ M := by
    have h := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 4*t)
    dsimp [M]
    nlinarith
  have hm0 : 0 < M := by linarith
  change abs (|deriv (phaseSlope t) u|/M-1) ≤ 13/t
  have he : |deriv (phaseSlope t) u|/M-1=(|deriv (phaseSlope t) u|-M)/M := by
    field_simp <;> ring
  rw [he,abs_div,abs_of_pos hm0,abs_of_nonneg (show 0 ≤ |deriv (phaseSlope t) u|-M from by
    dsimp [M]; nlinarith [hbound.1])]
  apply (div_le_iff₀ hm0).mpr
  calc
    _ ≤ 52 := by dsimp [M]; nlinarith [hbound.2]
    _ = (13/t)*(4*t) := by field_simp <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)

theorem model_stationary_curvature_identity (t u : ℝ)
    (hs : RiemannQuarticSaddleTheta.modelDerivative t (u : ℂ)=0) :
    12*t*u^2-16*Real.pi*Real.exp (4*u)=4*t*u^2*(3-4*u)-36 := by
  have hh : RiemannQuarticSaddleTheta.modelDerivative t (u : ℂ)=-(Complex.I*(0 : ℂ)) := by simpa using hs
  have h := RiemannQuarticSaddleTheta.saddle_real_identity t 0 (u : ℂ) hh
  have he : (Complex.exp (4*(u : ℂ))).re=Real.exp (4*u) := by
    simp only [← Complex.ofReal_ofNat,← Complex.ofReal_mul,← Complex.ofReal_exp,Complex.ofReal_re]
  rw [he] at h
  norm_num at h
  nlinarith

end OperatorDerivativeRewrite.Foundation.RiemannQuarticCurvature
