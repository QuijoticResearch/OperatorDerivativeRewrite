import Foundation.CauchyPoissonDissipativity
/-! Explicit disk flow for the Cauchy/sine-drift generator, actual Poisson-integral
moment composition, and positive Fourier generator matching. No completed
Markov semigroup, transition-measure equality or closed domain is asserted. -/
noncomputable section
open Complex
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonFlow

def numerator (q l : ℝ) (z : ℂ) : ℂ := q*(1-l)+(q^2+l)*z
def denominator (q l : ℝ) (z : ℂ) : ℂ := 1+q^2*l+q*(1-l)*z
def flow (q l : ℝ) (z : ℂ) : ℂ := numerator q l z / denominator q l z

theorem disk_defect (q l : ℝ) (z : ℂ) :
    normSq (denominator q l z)-normSq (numerator q l z) =
      (1-l)^2*(1-q^2)*normSq (1+(q:ℂ)*z) +
      l^2*(1+q^2)^2*(1-normSq z) +
      2*l*(1-l)*(1+q^2)*(1-q^2*normSq z) := by
  simp [denominator,numerator,normSq_apply,Complex.mul_re,Complex.mul_im,← Complex.ofReal_pow]
  <;> ring

theorem base_ne_zero (q : ℝ) (hq : |q| < 1) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    1+(q:ℂ)*z ≠ 0 := by
  have hn : ‖(q:ℂ)*z‖ < 1 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (abs_nonneg q) hz).trans_lt hq
  intro he
  have hh : (q:ℂ)*z = -1 := by linear_combination he
  rw [hh] at hn
  norm_num at hn

theorem disk_defect_pos (q l : ℝ) (hq : |q| < 1) (hl : 0 ≤ l)
    (hlt : l < 1) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    0 < normSq (denominator q l z)-normSq (numerator q l z) := by
  have hq2 : q^2 < 1 := by nlinarith [sq_abs q,abs_nonneg q]
  have hz2 : normSq z ≤ 1 := by rw [← Complex.sq_norm]; nlinarith [norm_nonneg z]
  have hb : 0 < normSq (1+(q:ℂ)*z) :=
    lt_of_le_of_ne (normSq_nonneg _) (Ne.symm (mt normSq_eq_zero.mp (base_ne_zero q hq z hz)))
  have hfirst : 0 < (1-l)^2*(1-q^2)*normSq (1+(q:ℂ)*z) :=
    mul_pos (mul_pos (sq_pos_of_pos (by linarith)) (by linarith)) hb
  have hsecond : 0 ≤ l^2*(1+q^2)^2*(1-normSq z) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (by linarith)
  have hlast : 0 ≤ 2*l*(1-l)*(1+q^2)*(1-q^2*normSq z) := by
    have hp : q^2*normSq z ≤ q^2 := mul_le_of_le_one_right (sq_nonneg q) hz2
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by linarith))
      (by positivity)) (by linarith)
  rw [disk_defect]
  linarith

theorem denominator_ne_zero (q l : ℝ) (hq : |q| < 1) (hl : 0 ≤ l)
    (hl1 : l ≤ 1) (z : ℂ) (hz : ‖z‖ ≤ 1) : denominator q l z ≠ 0 := by
  rcases eq_or_lt_of_le hl1 with h | h
  · subst l
    simp only [denominator,ofReal_one,one_mul,mul_one,sub_self,mul_zero,zero_mul,add_zero]
    exact_mod_cast (ne_of_gt (show 0 < 1+q^2 by positivity))
  · have hp := disk_defect_pos q l hq hl h z hz
    intro he
    rw [he,map_zero] at hp
    linarith [normSq_nonneg (numerator q l z)]

theorem flow_one (q : ℝ) (z : ℂ) : flow q 1 z = z := by
  have h : (1+(q:ℂ)^2) ≠ 0 := by exact_mod_cast (ne_of_gt (show 0 < 1+q^2 by positivity))
  simp only [flow,numerator,denominator,ofReal_one,sub_self,mul_zero,zero_add,mul_one,zero_mul,add_zero]
  field_simp
  <;> ring

theorem flow_strict_disk (q l : ℝ) (hq : |q| < 1) (hl : 0 ≤ l)
    (hlt : l < 1) (z : ℂ) (hz : ‖z‖ ≤ 1) : ‖flow q l z‖ < 1 := by
  have hp := disk_defect_pos q l hq hl hlt z hz
  have hd := denominator_ne_zero q l hq hl hlt.le z hz
  rw [flow,norm_div,div_lt_one (norm_pos_iff.mpr hd)]
  have hsq : ‖numerator q l z‖^2 < ‖denominator q l z‖^2 := by
    rw [Complex.sq_norm,Complex.sq_norm]; linarith
  nlinarith [norm_nonneg (numerator q l z),norm_nonneg (denominator q l z)]

theorem flow_disk (q l : ℝ) (hq : |q| < 1) (hl : 0 ≤ l)
    (hl1 : l ≤ 1) (z : ℂ) (hz : ‖z‖ ≤ 1) : ‖flow q l z‖ ≤ 1 := by
  rcases eq_or_lt_of_le hl1 with h | h
  · subst l; simpa only [flow_one] using hz
  · exact (flow_strict_disk q l hq hl h z hz).le

theorem flow_composition (q l m : ℝ) (hq : |q| < 1)
    (hl : 0 ≤ l) (hl1 : l ≤ 1) (hm : 0 ≤ m) (hm1 : m ≤ 1)
    (z : ℂ) (hz : ‖z‖ ≤ 1) : flow q l (flow q m z) = flow q (l*m) z := by
  have hd := denominator_ne_zero q m hq hm hm1 z hz
  have he := denominator_ne_zero q l hq hl hl1 (flow q m z) (flow_disk q m hq hm hm1 z hz)
  have hf := denominator_ne_zero q (l*m) hq (mul_nonneg hl hm)
    (mul_le_one₀ hl1 hm hm1) z hz
  apply (div_eq_div_iff he hf).mpr
  dsimp [numerator,denominator,flow] at hd ⊢
  push_cast
  field_simp
  <;> ring

theorem flow_fixed (q l : ℝ) (hq : |q| < 1) (hl : 0 ≤ l) (hl1 : l ≤ 1) :
    flow q l (q:ℂ) = q := by
  have hz : ‖(q:ℂ)‖ ≤ 1 := by simpa using hq.le
  apply (div_eq_iff (denominator_ne_zero q l hq hl hl1 q hz)).mpr
  dsimp [numerator,denominator]
  ring

theorem flow_holomorphic (q l : ℝ) (hq : |q| < 1) (hl : 0 ≤ l) (hl1 : l ≤ 1) :
    DiffContOnCl ℂ (flow q l) (Metric.ball 0 1) := by
  apply DifferentiableOn.diffContOnCl
  intro z hz
  have hz1 : ‖z‖ ≤ 1 := by
    have := Metric.closure_ball_subset_closedBall hz
    simpa using this
  have hd := denominator_ne_zero q l hq hl hl1 z hz1
  apply DifferentiableAt.differentiableWithinAt
  exact (show DifferentiableAt ℂ (numerator q l) z by unfold numerator; fun_prop).div
    (show DifferentiableAt ℂ (denominator q l) z by unfold denominator; fun_prop) hd

theorem poisson_flow_moment (q l : ℝ) (hq : |q| < 1) (hl : 0 ≤ l) (hl1 : l ≤ 1)
    (w : ℂ) (hw : ‖w‖ < 1) (n : ℕ) :
    Real.circleAverage (fun z : ℂ => poissonKernel 0 w z • (flow q l z)^n) 0 1 =
      (flow q l w)^n := by
  have hf := (show Differentiable ℂ (fun z : ℂ => z^n) from differentiable_id.pow n).comp_diffContOnCl (flow_holomorphic q l hq hl hl1)
  exact hf.circleAverage_poissonKernel_smul (by simpa using hw)

theorem poisson_composition_moment (q l m : ℝ) (hq : |q| < 1)
    (hl : 0 ≤ l) (hl1 : l ≤ 1) (hm : 0 ≤ m) (hm1 : m < 1)
    (z : ℂ) (hz : ‖z‖ ≤ 1) (n : ℕ) :
    Real.circleAverage (fun w : ℂ => poissonKernel 0 (flow q m z) w •
      (flow q l w)^n) 0 1 = (flow q (l*m) z)^n := by
  rw [poisson_flow_moment q l hq hl hl1 _ (flow_strict_disk q m hq hm hm1 z hz),
    flow_composition q l m hq hl hl1 hm hm1.le z hz]

theorem poisson_fixed_moment (q l : ℝ) (hq : |q| < 1) (hl : 0 ≤ l) (hl1 : l ≤ 1)
    (n : ℕ) :
    Real.circleAverage (fun z : ℂ => poissonKernel 0 (q:ℂ) z • (flow q l z)^n) 0 1 =
      (q:ℂ)^n := by
  rw [poisson_flow_moment q l hq hl hl1 _ (by simpa using hq),flow_fixed q l hq hl hl1]

def rate (q : ℝ) : ℝ := (1+q^2)/(1-q^2)
def decay (q t : ℝ) : ℝ := Real.exp (-rate q*t)
def evolution (q t : ℝ) (z : ℂ) : ℂ := flow q (decay q t) z

theorem rate_pos (q : ℝ) (hq : |q| < 1) : 0 < rate q := by
  have hq2 : q^2 < 1 := by nlinarith [sq_abs q,abs_nonneg q]
  exact div_pos (by positivity) (by linarith)

theorem decay_range (q t : ℝ) (hq : |q| < 1) (ht : 0 ≤ t) :
    0 ≤ decay q t ∧ decay q t ≤ 1 := by
  constructor
  · exact (Real.exp_pos _).le
  · apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (rate_pos q hq).le) ht

theorem evolution_zero (q : ℝ) (z : ℂ) : evolution q 0 z = z := by
  simpa only [evolution,decay,mul_zero,Real.exp_zero] using flow_one q z

theorem evolution_add (q s t : ℝ) (hq : |q| < 1) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (z : ℂ) (hz : ‖z‖ ≤ 1) : evolution q (s+t) z = evolution q s (evolution q t z) := by
  have he : decay q (s+t) = decay q s * decay q t := by
    simp only [decay,mul_add,Real.exp_add]
  unfold evolution
  rw [he]
  exact (flow_composition q _ _ hq (decay_range q s hq hs).1 (decay_range q s hq hs).2
    (decay_range q t hq ht).1 (decay_range q t hq ht).2 z hz).symm

theorem evolution_derivative_zero (q : ℝ) (hq : |q| < 1) (z : ℂ) :
    HasDerivAt (fun t : ℝ => evolution q t z)
      (-z+(q:ℂ)/(1-(q:ℂ)^2)*(1-z^2)) 0 := by
  have hd : HasDerivAt (fun t : ℝ => (decay q t : ℂ)) (-(rate q : ℂ)) 0 := by
    simpa [decay] using ((((hasDerivAt_id (0:ℝ)).const_mul (-rate q)).exp).ofReal_comp)
  have hden : (1+(q:ℂ)^2) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < 1+q^2 by positivity))
  have hq2 : q^2 < 1 := by nlinarith [sq_abs q,abs_nonneg q]
  have hden2 : (1-(q:ℂ)^2) ≠ 0 := by exact_mod_cast (ne_of_gt (show 0 < 1-q^2 by linarith))
  have hn := ((hd.const_sub 1).const_mul (q:ℂ)).add ((hd.const_add ((q:ℂ)^2)).mul_const z)
  have he := ((hd.const_mul ((q:ℂ)^2)).const_add 1).add
    (((hd.const_sub 1).const_mul (q:ℂ)).mul_const z)
  have hh := hn.div he (by simpa [decay] using hden)
  convert hh using 1
  · rfl
  · simp [decay,rate]
    push_cast
    field_simp
    <;> ring

theorem evolution_strict_disk (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (z : ℂ) (hz : ‖z‖ ≤ 1) : ‖evolution q t z‖ < 1 := by
  apply flow_strict_disk q _ hq (decay_range q t hq ht.le).1 _ z hz
  apply Real.exp_lt_one_iff.mpr
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (rate_pos q hq)) ht

theorem actual_positive_mode_derivative (q : ℝ) (hq : |q| < 1) (n : ℕ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => (evolution q t (circleMap (0:ℂ) 1 θ))^(n+1))
      (FiniteFourierSynthesis.synthesis ![θ,0,0]
        (CauchyPoissonNonSymmetry.drift (2*q/(1-q^2))
          (AddMonoidAlgebra.single (BrownianEnergyRepair.Torus.axisWave (n+1)) 1))) 0 := by
  have h := (evolution_derivative_zero q hq (circleMap (0:ℂ) 1 θ)).pow (n+1)
  convert h using 1
  simp only [CauchyPoissonNonSymmetry.drift,CauchyPoissonCoreInvariant.generator_positive_mode,
    evolution_zero,Nat.add_sub_cancel]
  push_cast
  ring

end OperatorDerivativeRewrite.Foundation.CauchyPoissonFlow
