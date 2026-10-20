import Foundation.RiemannEvenGrowingFourier
import Foundation.RiemannQuarticLocalCosineZeros

/-! Actual real and simple integer-even zeros in an expanding frequency
window. No assertion concerning zeros outside the window is made. -/
noncomputable section
open Set Metric Complex Filter MeasureTheory
open scoped ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannEvenWindowZeros
open RiemannEvenDomain RiemannEvenRealSaddle RiemannEvenFlow RiemannEvenGrowingFourier

theorem flow_conj (m : ℕ) (t : ℝ) (z : ℂ) : flow m t (conj z) = conj (flow m t z) := by
  rw [RiemannEvenEvolution.flow_eq_cosine_integral,RiemannEvenEvolution.flow_eq_cosine_integral,← integral_conj]
  apply integral_congr_ae
  filter_upwards with v
  simp only [map_mul,Complex.conj_ofReal,← Complex.cos_conj]

theorem actual_real_simple_window (m : ℕ) (hm : 0 < m) :
    ∀ᶠ t : ℝ in atTop, ∀ u ∈ Ici (0 : ℝ),
      IsMaxOn (weighted m 0 t 0) (Ici 0) u → ∀ z : ℂ, ‖z‖ ≤ u/2 →
      flow m t z = 0 → z.im = 0 ∧ deriv (flow m t) z ≠ 0 := by
  let ε : ℝ := 1/(1000*Real.exp 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  filter_upwards [uniform_growing_normalized_cosine m hm ε hε,
    actual_growing_zero_strip m hm (1/1000) (by norm_num),
    maxima_escape m hm 2 (by norm_num)] with t hmodel hstrip hlarge
  intro u hu hmax z hz hzero
  have hu2 : 2 ≤ u := (hlarge u hu hmax).le
  have hu0 : 0 < u := by linarith
  have hun : (u : ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
  let q : ℂ := (u : ℂ)*z
  let a : ℝ := q.re
  let f : ℂ → ℂ := fun w => flow m t (w/(u : ℂ))/flow m t 0
  have hf : Differentiable ℂ f :=
    ((flow_differentiable m t).comp (differentiable_id.div_const _)).div_const _
  have hMconj : conj (flow m t 0) = flow m t 0 := by
    rw [RiemannEvenNormalization.flow_zero_eq_mass,Complex.conj_ofReal]
  have hconj : ∀ w, f (conj w) = conj (f w) := by
    intro w
    dsimp [f]
    have he : conj w/(u : ℂ) = conj (w/(u : ℂ)) := by simp only [map_div₀,Complex.conj_ofReal]
    rw [he,flow_conj,map_div₀,hMconj]
  have hstripz := hstrip u hu hmax z (hz.trans (by linarith)) hzero
  have hqim : |q.im| ≤ (1/1000 : ℝ) := by
    simpa only [q,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
      abs_mul,abs_of_pos hu0] using hstripz
  have hdist : ‖q-(a : ℂ)‖ = |q.im| := by
    have he : q-(a : ℂ) = (q.im : ℂ)*Complex.I := by
      apply Complex.ext <;> simp [a,Complex.mul_re,Complex.mul_im]
    rw [he,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  have hq : q ∈ closedBall (a : ℂ) (1/1000) := by
    simpa only [mem_closedBall,dist_eq_norm,hdist] using hqim
  have hscale : q/(u : ℂ) = z := by dsimp [q]; field_simp
  have hzeroF : f q = 0 := by dsimp [f]; rw [hscale,hzero,zero_div]
  have ha : ‖(a : ℂ)‖ ≤ u^2/2 := by
    have hqnorm : ‖q‖ = u*‖z‖ := by simp only [q,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu0]
    rw [Complex.norm_real,Real.norm_eq_abs]
    change |q.re| ≤ _
    have hmul : u*‖z‖ ≤ u*(u/2) := mul_le_mul_of_nonneg_left hz hu0.le
    have h := (Complex.abs_re_le_norm q).trans (hqnorm.le.trans hmul)
    nlinarith
  have hclose : ∀ w ∈ closedBall (a : ℂ) 1, ‖f w-Complex.cos w‖ ≤ 1/1000 := by
    intro w hw
    have hwDist : ‖w-(a : ℂ)‖ ≤ 1 := by simpa only [mem_closedBall,dist_eq_norm] using hw
    have hnorm : ‖w/(u : ℂ)‖ ≤ u := by
      have h := norm_add_le (w-(a : ℂ)) (a : ℂ)
      rw [sub_add_cancel] at h
      rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu0]
      apply (div_le_iff₀ hu0).mpr
      nlinarith [sq_nonneg (u-2)]
    have h := hmodel u hu hmax (w/(u : ℂ)) hnorm
    have hmul : (u : ℂ)*(w/(u : ℂ)) = w := by field_simp
    have him : u*(w/(u : ℂ)).im = w.im := by
      have hh := congrArg Complex.im hmul
      simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] using hh
    have himabs : u*|(w/(u : ℂ)).im| = |w.im| := by
      calc
        _ = |u*(w/(u : ℂ)).im| := by rw [abs_mul,abs_of_pos hu0]
        _ = _ := congrArg abs him
    rw [hmul,himabs] at h
    have hi := (Complex.abs_im_le_norm (w-(a : ℂ))).trans hwDist
    simp only [Complex.sub_im,Complex.ofReal_im,sub_zero] at hi
    have he := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hi) hε.le
    have heq : ε*Real.exp 1 = 1/1000 := by dsimp [ε]; field_simp
    change ‖f w-Complex.cos w‖ < _ at h
    exact h.le.trans (by rw [← heq]; exact he)
  have hlocal := RiemannQuarticLocalCosineZeros.real_simple_zero f a
    (fun w _ => hf w) hconj hclose q hq hzeroF
  have him : q.im = u*z.im := by simp [q,Complex.mul_im]
  refine ⟨?_,?_⟩
  · rw [him] at hlocal
    exact (mul_eq_zero.mp hlocal.1).resolve_left hu0.ne'
  · intro hder
    have hN : HasDerivAt (fun w : ℂ => flow m t w/flow m t 0) 0 z := by
      simpa only [hder,zero_div] using ((flow_differentiable m t z).hasDerivAt.div_const (flow m t 0))
    have hN' : HasDerivAt (fun w : ℂ => flow m t w/flow m t 0) 0 (q/(u : ℂ)) := by
      rw [hscale]; exact hN
    have hcomp := hN'.comp q ((hasDerivAt_id q).div_const (u : ℂ))
    have hfd : deriv f q = 0 := by
      simpa only [Function.comp_def,id_eq,zero_mul] using hcomp.deriv
    exact hlocal.2 hfd

theorem eventually_real_simple_on_each_disk (m : ℕ) (hm : 0 < m) (R : ℝ) (hR : 0 ≤ R) :
    ∀ᶠ t : ℝ in atTop, ∀ z : ℂ, ‖z‖ ≤ R → flow m t z = 0 →
      z.im = 0 ∧ deriv (flow m t) z ≠ 0 := by
  filter_upwards [actual_real_simple_window m hm,maxima_escape m hm (2*R) (by positivity)] with t hw he
  intro z hz hzero
  obtain ⟨u,hu,hmax⟩ := exists_global_max m t
  have hlarge := he u hu hmax
  exact hw u hu hmax z (by linarith) hzero

theorem sixth_order_eventually_real_simple_on_each_disk (R : ℝ) (hR : 0 ≤ R) :
    ∀ᶠ t : ℝ in atTop, ∀ z : ℂ, ‖z‖ ≤ R → flow 3 t z = 0 →
      z.im = 0 ∧ deriv (flow 3 t) z ≠ 0 :=
  eventually_real_simple_on_each_disk 3 (by norm_num) R hR

theorem eventually_nonreal_zeros_outside_each_disk (m : ℕ) (hm : 0 < m) (R : ℝ) (hR : 0 ≤ R) :
    ∀ᶠ t : ℝ in atTop, ∀ z : ℂ, flow m t z = 0 → z.im ≠ 0 → R < ‖z‖ := by
  filter_upwards [eventually_real_simple_on_each_disk m hm R hR] with t ht
  intro z hzero hnonreal
  by_contra h
  exact hnonreal (ht z (le_of_not_gt h) hzero).1

/- The growing-window conclusion alone cannot imply global reality. These
polynomials have no zero in the growing disk but have an escaping nonreal zero.
They are counterexamples to that inference, not models of the arithmetic flow. -/
theorem escaping_polynomial_nonreal_root (t : ℝ) (ht : 0 < t) :
    (Complex.I*(t : ℂ))^2+(t : ℂ)^2 = 0 ∧ (Complex.I*(t : ℂ)).im ≠ 0 := by
  constructor
  · simp only [mul_pow,Complex.I_sq,neg_one_mul]
    ring
  · simpa only [Complex.mul_im,Complex.I_re,Complex.ofReal_im,zero_mul,
      Complex.I_im,Complex.ofReal_re,one_mul,zero_add] using ht.ne'

theorem escaping_polynomial_no_zero_in_window (t : ℝ) (ht : 0 < t) (z : ℂ) (hz : ‖z‖ ≤ t/2) :
    z^2+(t : ℂ)^2 ≠ 0 := by
  intro hzero
  have he : z^2 = -(t : ℂ)^2 := by linear_combination hzero
  have hn := congrArg norm he
  simp only [norm_pow,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht] at hn
  have hs := pow_le_pow_left₀ (norm_nonneg z) hz 2
  nlinarith

end OperatorDerivativeRewrite.Foundation.RiemannEvenWindowZeros
