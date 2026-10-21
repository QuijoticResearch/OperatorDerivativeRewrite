import Foundation.RiemannQuadraticGaussian
import Foundation.RiemannQuadraticHermite
import Mathlib.Analysis.Complex.Exponential

/-! Genuine quadratic-flow parabolic expansion with an actual integrable remainder.
The cubic error is uniform on each fixed complex spatial disk. At a double zero,
the scaled actual flow converges uniformly on those disks to its variance-two
Hermite model, through punctured real scaling. Higher multiplicities, actual zero
counts and global strip contraction are separate obligations. -/
noncomputable section
open Complex MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuadraticParabolic
open RiemannEvenFlow RiemannEvenDomain
open RiemannQuarticFlow (halfLine)

def secondPhase (h : ℝ) (a b : ℂ) : ℂ :=
  1+(h : ℂ)*b+(h : ℂ)^2*(a+b^2/2)

theorem phase_remainder (h : ℝ) (hh : |h| ≤ 1) (a b : ℂ) :
    ‖Complex.exp ((h : ℂ)*b+(h : ℂ)^2*a)-secondPhase h a b‖ ≤
      |h|^3*((‖a‖+‖b‖)^3*Real.exp (‖a‖+‖b‖)+‖a‖*‖b‖+‖a‖^2/2) := by
  let x : ℂ := (h : ℂ)*b+(h : ℂ)^2*a
  let Q : ℝ := ‖a‖+‖b‖
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hr : 0 ≤ |h| := abs_nonneg h
  have hr2 : |h|^2 ≤ |h| := by nlinarith
  have hx : ‖x‖ ≤ |h| *Q := by
    have hn := norm_add_le ((h : ℂ)*b) ((h : ℂ)^2*a)
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs] at hn
    dsimp [x,Q]
    nlinarith [norm_nonneg a]
  have hxQ : ‖x‖ ≤ Q := hx.trans (mul_le_of_le_one_left hQ hh)
  have ht := Complex.norm_exp_sub_sum_le_norm_mul_exp x 3
  norm_num [Finset.sum_range_succ] at ht
  have ht' : ‖Complex.exp x-(1+x+x^2/2)‖ ≤
      |h|^3*Q^3*Real.exp Q := by
    apply ht.trans
    have hp := pow_le_pow_left₀ (norm_nonneg x) hx 3
    have he := Real.exp_le_exp.mpr hxQ
    have hm := mul_le_mul hp he (Real.exp_pos _).le (pow_nonneg (mul_nonneg hr hQ) 3)
    convert hm using 1 <;> ring
  have he : Complex.exp x-secondPhase h a b =
      (Complex.exp x-(1+x+x^2/2))+
        (h : ℂ)^3*(a*b+(h : ℂ)*a^2/2) := by
    dsimp [x,secondPhase]
    ring
  have hc : ‖a*b+(h : ℂ)*a^2/2‖ ≤ ‖a‖*‖b‖+‖a‖^2/2 := by
    have hn := norm_add_le (a*b) ((h : ℂ)*a^2/2)
    simp only [norm_mul,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      Complex.norm_ofNat] at hn
    nlinarith [sq_nonneg ‖a‖]
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  have hb := mul_le_mul_of_nonneg_left hc (pow_nonneg hr 3)
  dsimp [Q] at ht'
  linarith

theorem actual_integrand_phase (j : ℕ) (t h u : ℝ) (z w : ℂ) :
    RiemannEvenFlow.integrand 1 j (t+h^2) (z+(h : ℂ)*w) u =
      RiemannEvenFlow.integrand 1 j t z u *
        Complex.exp ((h : ℂ)*(Complex.I*(u : ℂ)*w)+
          (h : ℂ)^2*(u : ℂ)^2) := by
  unfold RiemannEvenFlow.integrand RiemannEvenDomain.weighted
  simp only [pow_zero,one_mul,zero_mul,add_zero]
  have ht : (t+h^2)*u^(2*1)=t*u^(2*1)+h^2*u^2 := by ring
  rw [ht,Real.exp_add]
  push_cast
  rw [Complex.exp_add]
  have hz : Complex.I*(u : ℂ)*(z+(h : ℂ)*w) =
      Complex.I*(u : ℂ)*z+(h : ℂ)*(Complex.I*(u : ℂ)*w) := by ring
  rw [hz,Complex.exp_add]
  ring

theorem phase_remainder_coarse (h : ℝ) (hh : |h| ≤ 1) (a b : ℂ) :
    ‖Complex.exp ((h : ℂ)*b+(h : ℂ)^2*a)-secondPhase h a b‖ ≤
      8*|h|^3*Real.exp (2*(‖a‖+‖b‖)) := by
  let Q : ℝ := ‖a‖+‖b‖
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have h2 := Real.pow_div_factorial_le_exp Q hQ 2
  have h3 := Real.pow_div_factorial_le_exp Q hQ 3
  norm_num at h2 h3
  have he : 1 ≤ Real.exp Q := Real.one_le_exp hQ
  have hab : ‖a‖*‖b‖+‖a‖^2/2 ≤ Q^2 := by
    dsimp [Q]; nlinarith [norm_nonneg a,norm_nonneg b,sq_nonneg ‖b‖]
  have hexp : Real.exp (2*Q) = Real.exp Q*Real.exp Q := by
    rw [show 2*Q=Q+Q by ring,Real.exp_add]
  have hc : Q^3*Real.exp Q+‖a‖*‖b‖+‖a‖^2/2 ≤ 8*Real.exp (2*Q) := by
    rw [hexp]
    nlinarith [mul_le_mul_of_nonneg_right h3 (Real.exp_pos Q).le,
      mul_nonneg (Real.exp_pos Q).le (sub_nonneg.mpr he)]
  have h := (phase_remainder h hh a b).trans
    (mul_le_mul_of_nonneg_left hc (pow_nonneg (abs_nonneg h) 3))
  dsimp [Q] at h
  convert h using 1 <;> ring

def remainder (j : ℕ) (t : ℝ) (z : ℂ) (h : ℝ) (w : ℂ) (u : ℝ) : ℂ :=
  integrand 1 j (t+h^2) (z+(h : ℂ)*w) u -
    (integrand 1 j t z u+(h : ℂ)*w*integrand 1 (j+1) t z u+
      (h : ℂ)^2*(w^2/2-1)*integrand 1 (j+2) t z u)

theorem remainder_factor (j : ℕ) (t h u : ℝ) (z w : ℂ) :
    remainder j t z h w u = integrand 1 j t z u *
      (Complex.exp ((h : ℂ)*(Complex.I*(u : ℂ)*w)+(h : ℂ)^2*(u : ℂ)^2)-
        secondPhase h ((u : ℂ)^2) (Complex.I*(u : ℂ)*w)) := by
  rw [remainder,actual_integrand_phase]
  simp only [integrand,pow_add,secondPhase]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem remainder_integrable (j : ℕ) (t : ℝ) (z : ℂ) (h : ℝ) (w : ℂ) :
    Integrable (remainder j t z h w) halfLine :=
  (integrand_integrable 1 j (t+h^2) (z+(h : ℂ)*w)).sub
    (((integrand_integrable 1 j t z).add
      ((integrand_integrable 1 (j+1) t z).const_mul ((h : ℂ)*w))).add
      ((integrand_integrable 1 (j+2) t z).const_mul ((h : ℂ)^2*(w^2/2-1))))

theorem remainder_bound (j : ℕ) (t h R u : ℝ) (z w : ℂ)
    (hh : |h| ≤ 1) (hw : ‖w‖ ≤ R) (hu : 0 ≤ u) :
    ‖remainder j t z h w u‖ ≤
      8*|h|^3*weighted 1 j (t+2) (‖z‖+2*R) u := by
  have hp := phase_remainder_coarse h hh ((u : ℂ)^2) (Complex.I*(u : ℂ)*w)
  have hq : ‖(u : ℂ)^2‖+‖Complex.I*(u : ℂ)*w‖ ≤ u^2+R*u := by
    simp only [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu,
      norm_mul,Complex.norm_I,one_mul]
    nlinarith
  rw [remainder_factor,norm_mul]
  calc
    _ ≤ weighted 1 j t ‖z‖ u*(8*|h|^3*Real.exp (2*(u^2+R*u))) := by
      exact mul_le_mul (integrand_bound 1 j t z u hu)
        (hp.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
          (by positivity))) (norm_nonneg _) (weighted_nonneg 1 j t ‖z‖ u hu)
    _ = _ := by
      unfold weighted
      rw [show (t+2)*u^(2*1)+(‖z‖+2*R)*u =
        (t*u^(2*1)+‖z‖*u)+2*(u^2+R*u) by ring]
      simp only [Real.exp_add]
      ring

theorem remainder_integral (j : ℕ) (t : ℝ) (z : ℂ) (h : ℝ) (w : ℂ) :
    (∫ u, remainder j t z h w u ∂halfLine) =
      jet 1 j (t+h^2) (z+(h : ℂ)*w) -
        (jet 1 j t z+(h : ℂ)*w*jet 1 (j+1) t z+
          (h : ℂ)^2*(w^2/2-1)*jet 1 (j+2) t z) := by
  have h0 := integrand_integrable 1 j t z
  have h1 := (integrand_integrable 1 (j+1) t z).const_mul ((h : ℂ)*w)
  have h2 := (integrand_integrable 1 (j+2) t z).const_mul ((h : ℂ)^2*(w^2/2-1))
  have hsum : Integrable (fun u => integrand 1 j t z u+
      (h : ℂ)*w*integrand 1 (j+1) t z u+
      (h : ℂ)^2*(w^2/2-1)*integrand 1 (j+2) t z u) halfLine := by
    simpa only [Pi.add_def] using (h0.add h1).add h2
  have hadd1 := integral_add h0 h1
  have hadd2 := integral_add (h0.add h1) h2
  simp only [Pi.add_def] at hadd1 hadd2
  simp only [remainder]
  rw [integral_sub (integrand_integrable 1 j (t+h^2) (z+(h : ℂ)*w))
    hsum,hadd2,hadd1]
  simp only [integral_const_mul,jet]

def budget (j : ℕ) (t : ℝ) (z : ℂ) (R : ℝ) : ℝ :=
  8*(∫ u, weighted 1 j (t+2) (‖z‖+2*R) u ∂halfLine)

theorem jet_expansion_bound (j : ℕ) (t h R : ℝ) (z w : ℂ)
    (hh : |h| ≤ 1) (hw : ‖w‖ ≤ R) :
    ‖jet 1 j (t+h^2) (z+(h : ℂ)*w) -
      (jet 1 j t z+(h : ℂ)*w*jet 1 (j+1) t z+
        (h : ℂ)^2*(w^2/2-1)*jet 1 (j+2) t z)‖ ≤
      budget j t z R*|h|^3 := by
  have hi := (weighted_integrable 1 j (t+2) (‖z‖+2*R)).const_mul (8*|h|^3)
  have hp : ∀ᵐ u ∂halfLine, ‖remainder j t z h w u‖ ≤
      8*|h|^3*weighted 1 j (t+2) (‖z‖+2*R) u := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    exact remainder_bound j t h R u z w hh hw hu
  have hb := norm_integral_le_of_norm_le hi hp
  rw [remainder_integral,integral_const_mul] at hb
  convert hb using 1 <;> dsimp [budget] <;> ring

theorem budget_nonneg (j : ℕ) (t : ℝ) (z : ℂ) (R : ℝ) :
    0 ≤ budget j t z R := by
  apply mul_nonneg (by norm_num)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
  exact weighted_nonneg 1 j (t+2) (‖z‖+2*R) u hu

theorem flow_expansion_bound (t h R : ℝ) (z w : ℂ)
    (hh : |h| ≤ 1) (hw : ‖w‖ ≤ R) :
    ‖flow 1 (t+h^2) (z+(h : ℂ)*w) -
      (flow 1 t z+(h : ℂ)*w*deriv (flow 1 t) z+
        (h : ℂ)^2*(w^2/2-1)*iteratedDeriv 2 (flow 1 t) z)‖ ≤
      budget 0 t z R*|h|^3 := by
  have hp := jet_expansion_bound 0 t h R z w hh hw
  have hn := jet_expansion_bound 0 t h R (-z) (-w) hh (by simpa only [norm_neg] using hw)
  rw [show -z+(h : ℂ)*(-w) = -(z+(h : ℂ)*w) by ring] at hn
  simp only [budget,norm_neg,neg_sq] at hn
  let ep := jet 1 0 (t+h^2) (z+(h : ℂ)*w) -
      (jet 1 0 t z+(h : ℂ)*w*jet 1 1 t z+(h : ℂ)^2*(w^2/2-1)*jet 1 2 t z)
  let en := jet 1 0 (t+h^2) (-(z+(h : ℂ)*w)) -
      (jet 1 0 t (-z)-(h : ℂ)*w*jet 1 1 t (-z)+
        (h : ℂ)^2*(w^2/2-1)*jet 1 2 t (-z))
  have hep : ‖ep‖ ≤ budget 0 t z R*|h|^3 := hp
  have hen : ‖en‖ ≤ budget 0 t z R*|h|^3 := by
    simpa only [en,budget,mul_neg,neg_mul,Nat.zero_add,sub_eq_add_neg] using hn
  have hd : deriv (flow 1 t) z = RiemannEvenEvolution.symmetricJet 1 1 t z := by
    simpa only [iteratedDeriv_one] using congrFun
      (RiemannEvenEvolution.flow_iteratedDeriv 1 1 t) z
  have he : flow 1 (t+h^2) (z+(h : ℂ)*w) -
      (flow 1 t z+(h : ℂ)*w*deriv (flow 1 t) z+
        (h : ℂ)^2*(w^2/2-1)*iteratedDeriv 2 (flow 1 t) z) = (ep+en)/2 := by
    rw [hd,RiemannEvenEvolution.flow_iteratedDeriv]
    simp only [flow,RiemannEvenEvolution.symmetricJet,ep,en]
    norm_num
    ring
  rw [he,norm_div,Complex.norm_ofNat]
  have hb := norm_add_le ep en
  linarith

theorem double_zero_scaled_bound (t h R : ℝ) (z w : ℂ)
    (hz : flow 1 t z=0) (hd : deriv (flow 1 t) z=0)
    (hh : |h| ≤ 1) (hne : h ≠ 0) (hw : ‖w‖ ≤ R) :
    ‖flow 1 (t+h^2) (z+(h : ℂ)*w)/(h : ℂ)^2 -
      (w^2/2-1)*iteratedDeriv 2 (flow 1 t) z‖ ≤ budget 0 t z R*|h| := by
  have hp := flow_expansion_bound t h R z w hh hw
  rw [hz,hd,mul_zero,zero_add,zero_add] at hp
  have hc : (h : ℂ) ≠ 0 := by exact_mod_cast hne
  have he : flow 1 (t+h^2) (z+(h : ℂ)*w)/(h : ℂ)^2 -
      (w^2/2-1)*iteratedDeriv 2 (flow 1 t) z =
      (flow 1 (t+h^2) (z+(h : ℂ)*w)-
        (h : ℂ)^2*(w^2/2-1)*iteratedDeriv 2 (flow 1 t) z)/(h : ℂ)^2 := by
    field_simp
  rw [he,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  apply (div_le_iff₀ (pow_pos (abs_pos.mpr hne) 2)).mpr
  nlinarith [hp]

theorem double_zero_uniform_on_disk (t R : ℝ) (z : ℂ)
    (hz : flow 1 t z=0) (hd : deriv (flow 1 t) z=0) :
    TendstoUniformlyOn
      (fun h : ℝ => fun w : ℂ => flow 1 (t+h^2) (z+(h : ℂ)*w)/(h : ℂ)^2)
      (fun w => (w^2/2-1)*iteratedDeriv 2 (flow 1 t) z)
      (𝓝[≠] 0) {w | ‖w‖ ≤ R} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have habs : Tendsto (fun h : ℝ => |h|) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [abs_zero] using
      (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun h : ℝ => budget 0 t z R*|h|) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul habs
  filter_upwards [habs.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ)<1)),
    hlim.eventually (Iio_mem_nhds hε),self_mem_nhdsWithin] with h hh he hne
  intro w hw
  rw [dist_comm,dist_eq_norm]
  exact (double_zero_scaled_bound t h R z w hz hd hh.le (by simpa using hne) hw).trans_lt he

theorem double_zero_hermite_uniform (t R : ℝ) (z : ℂ)
    (hz : flow 1 t z=0) (hd : deriv (flow 1 t) z=0) :
    TendstoUniformlyOn
      (fun h : ℝ => fun w : ℂ => flow 1 (t+h^2) (z+(h : ℂ)*w)/(h : ℂ)^2)
      (fun w => RiemannQuadraticHermite.value 2 w/2*iteratedDeriv 2 (flow 1 t) z)
      (𝓝[≠] 0) {w | ‖w‖ ≤ R} := by
  have hf : (fun w : ℂ => (w^2/2-1)*iteratedDeriv 2 (flow 1 t) z) =
      (fun w => RiemannQuadraticHermite.value 2 w/2*iteratedDeriv 2 (flow 1 t) z) := by
    funext w
    have h2 : RiemannQuadraticHermite.value 2 w=w^2-2 := by
      simpa [pow_two] using RiemannQuadraticHermite.value_recursion 0 w
    rw [h2]
    ring
  rw [← hf]
  exact double_zero_uniform_on_disk t R z hz hd

end OperatorDerivativeRewrite.Foundation.RiemannQuadraticParabolic
