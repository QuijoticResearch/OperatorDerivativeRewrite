import Foundation.CauchyPoissonQuantitativeEntropy
/-! Explicit positive entropy-production rate for every allowed drift.
Coarse disk-defect, denominator and reference-density bounds yield a reset
minorization with controlled slope. No sharp LSI or jump identity is asserted. -/
open Complex MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped Topology
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonDriftRate
open CauchyPoissonFlow CauchyPoissonKernelComposition CauchyPoissonMarkovKernel
open CauchyPoissonQuantitativeEntropy CauchyPoissonMixtureEntropy
open CauchyPoissonForwardEntropy CauchyPoissonDensitySmooth

theorem denominator_bound (q l : ℝ) (hq : |q| < 1) (hl : 0 ≤ l) (hl1 : l ≤ 1)
    (z : Circle) : ‖denominator q l z‖ ≤ 3 := by
  have hq2 : q^2 ≤ 1 := by nlinarith [sq_abs q,abs_nonneg q]
  have hh := norm_add_le (1+(q:ℂ)^2*l) ((q:ℂ)*(1-l)*z)
  have hfirst : ‖1+(q:ℂ)^2*l‖ ≤ 2 := by
    have he : (1+(q:ℂ)^2*l) = ((1+q^2*l:ℝ):ℂ) := by push_cast; rfl
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hl1 (sq_nonneg q)]
  have hlast : ‖(q:ℂ)*(1-l)*z‖ ≤ 1 := by
    rw [norm_mul,norm_mul,Circle.norm_coe,mul_one]
    have he : (1-(l:ℂ)) = ((1-l:ℝ):ℂ) := by push_cast; rfl
    rw [he,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ 1-l by linarith)]
    nlinarith [mul_nonneg (abs_nonneg q) hl]
  exact hh.trans (by linarith)

theorem flow_defect_lower (q l : ℝ) (hq : |q| < 1) (hl : 0 ≤ l) (hl1 : l ≤ 1)
    (z : Circle) :
    2*l*(1-l)*(1+q^2)*(1-q^2)/9 ≤ 1-‖flow q l z‖^2 := by
  have hq2 : q^2 < 1 := by nlinarith [sq_abs q,abs_nonneg q]
  have hz : normSq (z:ℂ)=1 := by rw [← Complex.sq_norm]; simp
  have hdef := disk_defect q l z
  rw [hz] at hdef
  have hfirst : 0 ≤ (1-l)^2*(1-q^2)*normSq (1+(q:ℂ)*z) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (normSq_nonneg _)
  have hd : 0 < ‖denominator q l z‖^2 := sq_pos_of_pos
    (norm_pos_iff.mpr (denominator_ne_zero q l hq hl hl1 z (by simp)))
  have hb : ‖denominator q l z‖^2 ≤ 9 := by
    have := denominator_bound q l hq hl hl1 z
    nlinarith [norm_nonneg (denominator q l z)]
  have hn : 0 ≤ 2*l*(1-l)*(1+q^2)*(1-q^2) := by positivity
  have hprod := mul_le_mul_of_nonneg_left hb hn
  rw [← Complex.sq_norm,← Complex.sq_norm] at hdef
  have he : ‖flow q l z‖^2 = ‖numerator q l z‖^2 / ‖denominator q l z‖^2 := by
    rw [flow,norm_div,div_pow]
  rw [he]
  rw [show 1-‖numerator q l z‖^2/‖denominator q l z‖^2 =
      (‖denominator q l z‖^2-‖numerator q l z‖^2)/‖denominator q l z‖^2 by
    rw [sub_div,div_self (ne_of_gt hd)]]
  apply (le_div_iff₀ hd).mpr
  nlinarith [hprod]

theorem reference_upper (q : ℝ) (hq : |q| < 1) (w : ℂ) (hw : ‖w‖=1) :
    (1-|q|)^2 * poissonKernel 0 q w ≤ 1 := by
  have hdist : 1-|q| ≤ ‖w-(q:ℂ)‖ := by
    have hh := norm_sub_norm_le w (q:ℂ)
    simpa [hw,Complex.norm_real,Real.norm_eq_abs] using hh
  have hd : 0 < ‖w-(q:ℂ)‖ := by linarith
  have hsq : (1-|q|)^2 ≤ ‖w-(q:ℂ)‖^2 := by nlinarith
  simp only [poissonKernel,sub_zero,hw,one_pow,Complex.norm_real,Real.norm_eq_abs]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
  nlinarith [mul_nonneg (sq_nonneg (1-|q|)) (sq_nonneg |q|)]


def amplitude (q : ℝ) : ℝ := (1+q^2)*(1-q^2)*(1-|q|)^2/18

def reset (q t : ℝ) : ℝ := amplitude q * decay q t * (1-decay q t)

theorem amplitude_bounds (q : ℝ) (hq : |q| < 1) : 0 < amplitude q ∧ amplitude q ≤ 1/9 := by
  have hq2 : q^2 < 1 := by nlinarith [sq_abs q,abs_nonneg q]
  have hs : 0 < (1-|q|)^2 := sq_pos_of_pos (by linarith)
  have hs1 : (1-|q|)^2 ≤ 1 := by nlinarith [abs_nonneg q]
  have hp : 0 ≤ (1+q^2)*(1-q^2) := mul_nonneg (by positivity) (by linarith)
  have hp2 : (1+q^2)*(1-q^2) ≤ 2 := by nlinarith [sq_nonneg (q^2)]
  have hm := mul_le_mul_of_nonneg_left hs1 hp
  unfold amplitude
  constructor
  · exact div_pos (mul_pos (mul_pos (by positivity) (by linarith)) hs) (by norm_num)
  · nlinarith

theorem reset_bounds (q t : ℝ) (hq : |q| < 1) (ht : 0 < t) :
    0 < reset q t ∧ reset q t < 1 := by
  have ha := amplitude_bounds q hq
  have hl : 0 < decay q t := Real.exp_pos _
  have hl1 : decay q t < 1 := Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos (rate_pos q hq)) ht)
  have hp : decay q t*(1-decay q t) ≤ 1 := by nlinarith [sq_nonneg (decay q t)]
  have hm := mul_le_mul_of_nonneg_left hp ha.1.le
  unfold reset
  constructor
  · exact mul_pos (mul_pos ha.1 hl) (by linarith)
  · nlinarith

theorem drift_minorization (q t : ℝ) (hq : |q| < 1) (ht : 0 < t) (z : Circle) (θ : ℝ) :
    reset q t * poleWeight q θ ≤ poleWeight (evolution q t z) θ := by
  have hl := decay_range q t hq ht.le
  have hq2 : q^2 < 1 := by nlinarith [sq_abs q,abs_nonneg q]
  have hd := flow_defect_lower q (decay q t) hq hl.1 hl.2 z
  have hp := poisson_lower (evolution q t z) (evolution_strict_disk q t hq ht z (by simp))
    (circleMap 0 1 θ) (by simp)
  have hr := reference_upper q hq (circleMap 0 1 θ) (by simp)
  have hb : 0 ≤ decay q t*(1-decay q t)*(1+q^2)*(1-q^2)/18 :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hl.1 (by linarith [hl.2])) (by positivity)) (by linarith)) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hr hb
  have he : reset q t * poissonKernel 0 q (circleMap 0 1 θ) ≤
      poissonKernel 0 (evolution q t z) (circleMap 0 1 θ) := by
    unfold reset amplitude
    change 2*decay q t*(1-decay q t)*(1+q^2)*(1-q^2)/9 ≤ 1-‖evolution q t z‖^2 at hd
    nlinarith [hm]
  unfold poleWeight
  nlinarith [mul_le_mul_of_nonneg_left he (show 0 ≤ (2*Real.pi)⁻¹ by positivity)]



theorem entropy_contraction_explicit (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    klDiv ((kernel q t) ∘ₘ μ) (invariantLaw q) ≤
      ENNReal.ofReal (1-reset q t)*klDiv μ (invariantLaw q) :=
  entropy_contraction q t (reset q t) hq ht (reset_bounds q t hq ht).1.le
    (reset_bounds q t hq ht).2 (fun z θ _ => drift_minorization q t hq ht z θ) μ

theorem reset_derivative (q : ℝ) : HasDerivAt (reset q) (amplitude q * rate q) 0 := by
  have hd : HasDerivAt (decay q) (-rate q) 0 := by
    have he : decay q = (fun x : ℝ => Real.exp (-rate q*x)) := by
      funext x
      unfold decay
      rfl
    rw [he]
    simpa using ((hasDerivAt_id (0:ℝ)).const_mul (-rate q)).exp
  change HasDerivAt (fun t => amplitude q * decay q t * (1-decay q t)) _ 0
  convert (hd.const_mul (amplitude q)).mul (hd.const_sub 1) using 1 <;> simp [decay]

theorem production_bound (q t : ℝ) (hq : |q| < 1) (ht : 0 < t)
    (μ : Measure Circle) [IsProbabilityMeasure μ] :
    (∫ w, Real.log (densityCurve q hq μ t w).re *
      (deriv (densityCurve q hq μ) t w).re ∂invariantLaw q) ≤
      -(amplitude q * rate q)*(klDiv ((kernel q t) ∘ₘ μ) (invariantLaw q)).toReal := by
  let E := (klDiv ((kernel q t) ∘ₘ μ) (invariantLaw q)).toReal
  have hd := (actual_kl_derivative q t hq ht μ).tendsto_slope_zero_right
  have hr := (reset_derivative q).tendsto_slope_zero_right
  have hr' : Tendsto (fun h : ℝ => -(h⁻¹*reset q h)*E) (𝓝[Ioi 0] 0)
      (𝓝 (-(amplitude q*rate q)*E)) := by
    simpa [reset,decay] using hr.neg.mul_const E
  apply le_of_tendsto_of_tendsto hd hr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  change 0 < h at hh
  let := kernel_markov q t hq ht.le
  have hc := entropy_contraction_explicit q h hq hh ((kernel q t) ∘ₘ μ)
  rw [Measure.comp_assoc,kernel_composition q t h hq ht.le hh.le] at hc
  have hf := CauchyPoissonRegularization.positive_time_entropy_finite q t hq ht μ
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf) hc
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by linarith [(reset_bounds q h hq hh).2])] at hreal
  change h⁻¹ * (_-E) ≤ -(h⁻¹*reset q h)*E
  have hm := mul_le_mul_of_nonneg_left hreal (inv_nonneg.mpr hh.le)
  dsimp [E] at *
  nlinarith [hm]

theorem rate_positive (q : ℝ) (hq : |q| < 1) : 0 < amplitude q * rate q :=
  mul_pos (amplitude_bounds q hq).1 (rate_pos q hq)

end OperatorDerivativeRewrite.Foundation.CauchyPoissonDriftRate




