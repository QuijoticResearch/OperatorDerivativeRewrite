import Foundation.CauchyPoissonDriftRate
import Foundation.CauchyPoissonJumpLimit
import Foundation.CauchyPoissonBregmanStep
/-! Uniform small-time weighted kernel and positive Lipschitz Bregman bounds
for the actual circle Poisson flow, including tangential pole motion.
Spatial regularity of the actual evolved density is a separate obligation. -/
open Complex Filter Set
open scoped Topology
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonJumpDomination
open CauchyPoissonFlow CauchyPoissonDriftRate

theorem denominator_lower (q l : ℝ) (hl : 0 ≤ l) (hl1 : l ≤ 1)
    (z : Circle) : 1-|q| ≤ ‖denominator q l z‖ := by
  have ha : ‖1+(q:ℂ)^2*l‖ = 1+q^2*l := by
    have he : (1+(q:ℂ)^2*l) = ((1+q^2*l:ℝ):ℂ) := by push_cast; rfl
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hb : ‖(q:ℂ)*(1-l)*z‖ = |q| *(1-l) := by
    have he : (1-(l:ℂ)) = ((1-l:ℝ):ℂ) := by push_cast; rfl
    rw [norm_mul,norm_mul,Circle.norm_coe,mul_one,he,Complex.norm_real,
      Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ 1-l by linarith)]
  have hh := norm_sub_norm_le (1+(q:ℂ)^2*l) (-((q:ℂ)*(1-l)*z))
  rw [norm_neg,ha,hb,sub_neg_eq_add] at hh
  change 1-|q| ≤ ‖1+(q:ℂ)^2*l+(q:ℂ)*(1-l)*z‖
  nlinarith [mul_nonneg (sq_nonneg q) hl,mul_nonneg (abs_nonneg q) hl]

theorem flow_displacement (q l : ℝ) (hq : |q| < 1) (hl : 0 ≤ l) (hl1 : l ≤ 1)
    (z : Circle) : ‖flow q l z-(z:ℂ)‖ ≤ (4/(1-|q|))*(1-l) := by
  have hd := denominator_ne_zero q l hq hl hl1 z (by simp)
  have he : flow q l z-(z:ℂ) =
      (1-(l:ℂ))*((q:ℂ)-(1-(q:ℂ)^2)*z-(q:ℂ)*(z:ℂ)^2)/denominator q l z := by
    unfold flow numerator denominator at *
    field_simp
    ring
  have hq2 : q^2 < 1 := by nlinarith [sq_abs q,abs_nonneg q]
  have hb : ‖(q:ℂ)-(1-(q:ℂ)^2)*z-(q:ℂ)*(z:ℂ)^2‖ ≤ 4 := by
    have h1 := norm_sub_le (q:ℂ) ((1-(q:ℂ)^2)*z)
    have h2 := norm_sub_le ((q:ℂ)-(1-(q:ℂ)^2)*z) ((q:ℂ)*(z:ℂ)^2)
    have hc : ‖1-(q:ℂ)^2‖ = 1-q^2 := by
      have hc : 1-(q:ℂ)^2 = ((1-q^2:ℝ):ℂ) := by push_cast; rfl
      rw [hc,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith)]
    simp only [norm_mul,norm_pow,Circle.norm_coe,one_pow,mul_one,Complex.norm_real,
      Real.norm_eq_abs,hc] at h1 h2
    linarith [sq_nonneg q]
  rw [he,norm_div,norm_mul]
  have hlc : ‖1-(l:ℂ)‖ = 1-l := by
    rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ 1-l by linarith)]
  rw [hlc]
  have hp : 0 < 1-|q| := by linarith
  calc
    _ ≤ ((1-l)*4)/(1-|q|) := div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_left hb (by linarith)) hp
      (denominator_lower q l hl hl1 z)
    _ = _ := by ring

theorem radial_lower (q l : ℝ) (hq : |q| < 1) (hl : 1/2 ≤ l) (hl1 : l < 1)
    (z : Circle) : ((1+q^2)*(1-q^2)/18)*(1-l) ≤ 1-‖flow q l z‖ := by
  have hq2 : q^2 < 1 := by nlinarith [sq_abs q,abs_nonneg q]
  have h0 : 0 ≤ l := by linarith
  have hd := flow_defect_lower q l hq h0 hl1.le z
  have hp : 0 ≤ (1-l)*(1+q^2)*(1-q^2) := by positivity
  have hh := mul_nonneg (show 0 ≤ 2*l-1 by linarith) hp
  nlinarith [sq_nonneg (1-‖flow q l z‖)]

theorem weighted_kernel_bound (v : ℂ) (hv : ‖v‖ < 1) (z w : Circle)
    (C : ℝ) (hC : 0 ≤ C) (hc : ‖v-(z:ℂ)‖ ≤ C*(1-‖v‖)) :
    poissonKernel 0 v w * ‖(w:ℂ)-(z:ℂ)‖^2 ≤ (1-‖v‖^2)*(1+C)^2 := by
  have hd : 0 < ‖(w:ℂ)-v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (by
    intro h; rw [← h,Circle.norm_coe] at hv; linarith))
  have hr : 1-‖v‖ ≤ ‖(w:ℂ)-v‖ := by
    simpa only [Circle.norm_coe] using norm_sub_norm_le (w:ℂ) v
  have ht : ‖(w:ℂ)-(z:ℂ)‖ ≤ (1+C)*‖(w:ℂ)-v‖ := by
    have hh := norm_add_le ((w:ℂ)-v) (v-(z:ℂ))
    rw [sub_add_sub_cancel] at hh
    have hp := mul_le_mul_of_nonneg_left hr hC
    nlinarith
  have hs : ‖(w:ℂ)-(z:ℂ)‖^2 ≤ (1+C)^2*‖(w:ℂ)-v‖^2 := by
    nlinarith [sq_nonneg (‖(w:ℂ)-(z:ℂ)‖-(1+C)*‖(w:ℂ)-v‖), norm_nonneg ((w:ℂ)-(z:ℂ))]
  have hn : 0 ≤ 1-‖v‖^2 := by nlinarith [norm_nonneg v]
  simp only [poissonKernel,sub_zero,Circle.norm_coe,one_pow]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hs hn]

theorem flow_weighted_bound (q : ℝ) (hq : |q| < 1) :
    ∃ M : ℝ, 0 < M ∧ ∀ (l : ℝ), 1/2 ≤ l → l < 1 → ∀ z w : Circle,
      poissonKernel 0 (flow q l z) w * ‖(w:ℂ)-(z:ℂ)‖^2 ≤ M*(1-l) := by
  let D : ℝ := 4/(1-|q|)
  let c : ℝ := (1+q^2)*(1-q^2)/18
  have hq2 : q^2 < 1 := by nlinarith [sq_abs q,abs_nonneg q]
  have hD : 0 < D := div_pos (by norm_num) (by linarith)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨2*D*(1+D/c)^2, by positivity, ?_⟩
  intro l hl hl1 z w
  have hl0 : 0 ≤ l := by linarith
  have hv := flow_strict_disk q l hq hl0 hl1 z (by simp)
  have hdisp := flow_displacement q l hq hl0 hl1.le z
  have hrad := radial_lower q l hq hl hl1 z
  have hcomp : ‖flow q l z-(z:ℂ)‖ ≤ (D/c)*(1-‖flow q l z‖) := by
    have hh := mul_le_mul_of_nonneg_left hrad (div_nonneg hD.le hc.le)
    have he : (D/c)*(c*(1-l)) = D*(1-l) := by field_simp
    rw [he] at hh
    exact hdisp.trans hh
  have hdef : 1-‖flow q l z‖^2 ≤ 2*D*(1-l) := by
    have hn := norm_sub_norm_le (z:ℂ) (flow q l z)
    rw [Circle.norm_coe,norm_sub_rev] at hn
    nlinarith [sq_nonneg (1-‖flow q l z‖)]
  have hh := weighted_kernel_bound (flow q l z) hv z w (D/c)
    (div_nonneg hD.le hc.le) hcomp
  have hm := mul_le_mul_of_nonneg_right hdef (sq_nonneg (1+D/c))
  exact hh.trans (by nlinarith [hm])

theorem evolution_weighted_bound (q : ℝ) (hq : |q| < 1) :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, 0 < t → 1/2 ≤ decay q t → ∀ z w : Circle,
      t⁻¹ * poissonKernel 0 (evolution q t z) w * ‖(w:ℂ)-(z:ℂ)‖^2 ≤ M := by
  obtain ⟨M,hM,hm⟩ := flow_weighted_bound q hq
  refine ⟨M*rate q, mul_pos hM (rate_pos q hq), ?_⟩
  intro t ht hl z w
  have hlt : decay q t < 1 := Real.exp_lt_one_iff.mpr
    (mul_neg_of_neg_of_pos (neg_neg_of_pos (rate_pos q hq)) ht)
  have hh := hm (decay q t) hl hlt z w
  have he : 1-decay q t ≤ rate q*t := by
    have hh := Real.add_one_le_exp (-rate q*t)
    dsimp [decay]; linarith
  have hp := mul_le_mul_of_nonneg_left he hM.le
  have hk : poissonKernel 0 (evolution q t z) w * ‖(w:ℂ)-(z:ℂ)‖^2 ≤ (M*rate q)*t := by
    exact hh.trans (by nlinarith [hp])
  have hh := mul_le_mul_of_nonneg_left hk (inv_nonneg.mpr ht.le)
  simpa only [← mul_assoc, inv_mul_cancel_left₀ (ne_of_gt ht)] using
    (show t⁻¹ * (poissonKernel 0 (evolution q t z) w * ‖(w:ℂ)-(z:ℂ)‖^2) ≤ M*rate q from
      by convert hh using 1; field_simp)

theorem eventual_weighted_bound (q : ℝ) (hq : |q| < 1) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ z w : Circle,
      t⁻¹ * poissonKernel 0 (evolution q t z) w * ‖(w:ℂ)-(z:ℂ)‖^2 ≤ M := by
  obtain ⟨M,hM,hm⟩ := evolution_weighted_bound q hq
  refine ⟨M,hM,?_⟩
  have hc : ContinuousAt (decay q) 0 := by unfold decay; fun_prop
  have hh : ∀ᶠ t in 𝓝 (0:ℝ), 1/2 < decay q t :=
    hc.eventually (lt_mem_nhds (show (1/2:ℝ) < decay q 0 by norm_num [decay]))
  filter_upwards [hh.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hp
  exact hm t hp ht.le

theorem bregman_quadratic (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    CauchyPoissonBregmanStep.bregman a b ≤ (a-b)^2/b := by
  have hh := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos ha hb)) ha.le
  have he : a*(a/b-1)-a+b = (a-b)^2/b := by field_simp; ring
  unfold CauchyPoissonBregmanStep.bregman
  linarith

theorem bregman_chord_bound (f : Circle → ℝ) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 ≤ L)
    (hf : ∀ z, δ ≤ f z)
    (hlip : ∀ z w : Circle, |f z-f w| ≤ L*‖(w:ℂ)-(z:ℂ)‖) (z w : Circle) :
    CauchyPoissonBregmanStep.bregman (f z) (f w) ≤ (L^2/δ)*‖(w:ℂ)-(z:ℂ)‖^2 := by
  have hh := bregman_quadratic (f z) (f w) (hδ.trans_le (hf z)) (hδ.trans_le (hf w))
  have hs : (f z-f w)^2 ≤ L^2*‖(w:ℂ)-(z:ℂ)‖^2 := by
    have hb := hlip z w
    nlinarith [sq_abs (f z-f w), abs_nonneg (f z-f w), norm_nonneg ((w:ℂ)-(z:ℂ))]
  calc
    _ ≤ (f z-f w)^2/f w := hh
    _ ≤ (L^2*‖(w:ℂ)-(z:ℂ)‖^2)/δ := div_le_div₀ (by positivity) hs hδ (hf w)
    _ = _ := by ring

theorem eventual_bregman_domination (q : ℝ) (hq : |q| < 1)
    (f : Circle → ℝ) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 ≤ L)
    (hf : ∀ z, δ ≤ f z)
    (hlip : ∀ z w : Circle, |f z-f w| ≤ L*‖(w:ℂ)-(z:ℂ)‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ z w : Circle,
      t⁻¹ * poissonKernel 0 (evolution q t z) w *
        CauchyPoissonBregmanStep.bregman (f z) (f w) ≤ C := by
  obtain ⟨M,hM,hm⟩ := eventual_weighted_bound q hq
  refine ⟨M*(L^2/δ), by positivity, ?_⟩
  filter_upwards [hm,self_mem_nhdsWithin] with t ht hp
  intro z w
  have hv := evolution_strict_disk q t hq hp z (by simp)
  have hn : 0 ≤ poissonKernel 0 (evolution q t z) w := by
    simp only [poissonKernel,sub_zero,Circle.norm_coe,one_pow]
    apply div_nonneg _ (sq_nonneg _)
    nlinarith [norm_nonneg (evolution q t z)]
  have hb := mul_le_mul_of_nonneg_left (bregman_chord_bound f δ L hδ hL hf hlip z w)
    (mul_nonneg (inv_nonneg.mpr hp.le) hn)
  have hh := mul_le_mul_of_nonneg_right (ht z w) (show 0 ≤ L^2/δ by positivity)
  nlinarith [hb,hh]
end OperatorDerivativeRewrite.Foundation.CauchyPoissonJumpDomination
