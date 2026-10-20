import Foundation.RiemannEvenCompactWeight
import Foundation.RiemannEvenNaturalContour
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Convex.Jensen
/-! Actual integer-even reflected pairing. Unequal heights retain their
signed vertical endpoint integral; errors use nonzero amplitude norms. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannEvenHorizontalPairing
open RiemannEvenComplexWeight RiemannEvenNaturalContour

def horizontalIntegral (m : ℕ) (t : ℝ) (z : ℂ) (h : ℝ) : ℂ :=
  ∫ s : ℝ in Ioi 0, weight m t z ((s : ℂ)+(h : ℂ)*Complex.I)

theorem weight_conj (m : ℕ) (t : ℝ) (z q : ℂ) :
    weight m t (-conj z) (conj q)=conj (weight m t z q) := by
  unfold weight
  rw [map_mul,← RiemannQuarticKernelReflection.kernel_conj,← Complex.exp_conj]
  congr 2
  simp only [map_add,map_mul,map_pow,Complex.conj_ofReal,Complex.conj_I]
  ring

theorem horizontal_conj (m : ℕ) (t : ℝ) (z : ℂ) (h : ℝ) :
    horizontalIntegral m t (-conj z) (-h)=conj (horizontalIntegral m t z h) := by
  unfold horizontalIntegral
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with s
  have hq : (s : ℂ)+((-h : ℝ) : ℂ)*Complex.I=conj ((s : ℂ)+(h : ℂ)*Complex.I) := by
    simp only [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_neg]
    ring
  rw [hq,weight_conj]

theorem flow_real_horizontal (m : ℕ) (t x h : ℝ) (hh : |h| < Real.pi/8) :
    RiemannEvenFlow.flow m t (x : ℂ)=(horizontalIntegral m t (x : ℂ) h).re := by
  rw [flow_eq_paired_horizontal m t (x : ℂ) h hh]
  have hc := horizontal_conj m t (x : ℂ) h
  simp only [Complex.conj_ofReal] at hc
  have hn : (∫ s : ℝ in Ioi 0, weight m t (-(x : ℂ)) ((s : ℂ)-(h : ℂ)*Complex.I))=
      conj (horizontalIntegral m t (x : ℂ) h) := by
    simpa only [horizontalIntegral,Complex.ofReal_neg,neg_mul,← sub_eq_add_neg] using hc
  rw [hn]
  exact (Complex.re_eq_add_conj _).symm

theorem real_pair_error (m : ℕ) (t x h : ℝ) (hh : |h| < Real.pi/8) (A : ℂ)
    (hA : A ≠ 0) (η : ℝ) (he : ‖horizontalIntegral m t (x : ℂ) h/A-1‖ ≤ η) :
    ‖RiemannEvenFlow.flow m t (x : ℂ)-(A.re : ℂ)‖ ≤ η*‖A‖ := by
  have hid : horizontalIntegral m t (x : ℂ) h/A-1=(horizontalIntegral m t (x : ℂ) h-A)/A := by field_simp
  rw [hid,norm_div] at he
  have hnum := (div_le_iff₀ (norm_pos_iff.mpr hA)).mp he
  rw [flow_real_horizontal m t x h hh,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm (horizontalIntegral m t (x : ℂ) h-A)).trans hnum

theorem real_pair_cosine_error (m : ℕ) (t x h : ℝ) (hh : |h| < Real.pi/8) (A : ℂ)
    (hA : A ≠ 0) (η : ℝ) (he : ‖horizontalIntegral m t (x : ℂ) h/A-1‖ ≤ η) :
    |(RiemannEvenFlow.flow m t (x : ℂ)).re/‖A‖-Real.cos A.arg| ≤ η := by
  have herr := real_pair_error m t x h hh A hA η he
  have hre := (Complex.abs_re_le_norm (RiemannEvenFlow.flow m t (x : ℂ)-(A.re : ℂ))).trans herr
  simp only [Complex.sub_re,Complex.ofReal_re] at hre
  rw [Complex.cos_arg hA,← sub_div,abs_div,abs_of_pos (norm_pos_iff.mpr hA)]
  exact (div_le_iff₀ (norm_pos_iff.mpr hA)).mpr hre

theorem real_pair_zero_phase (m : ℕ) (t x h : ℝ) (hh : |h| < Real.pi/8) (A : ℂ)
    (hA : A ≠ 0) (η : ℝ) (he : ‖horizontalIntegral m t (x : ℂ) h/A-1‖ ≤ η)
    (hz : RiemannEvenFlow.flow m t (x : ℂ)=0) : |Real.cos A.arg| ≤ η := by
  have h := real_pair_cosine_error m t x h hh A hA η he
  simpa only [hz,Complex.zero_re,zero_div,zero_sub,abs_neg] using h

theorem real_pair_nonzero (m : ℕ) (t x h : ℝ) (hh : |h| < Real.pi/8) (A : ℂ)
    (hA : A ≠ 0) (η : ℝ) (he : ‖horizontalIntegral m t (x : ℂ) h/A-1‖ ≤ η)
    (hphase : η < |Real.cos A.arg|) : RiemannEvenFlow.flow m t (x : ℂ) ≠ 0 := by
  intro hz
  exact (not_lt_of_ge (real_pair_zero_phase m t x h hh A hA η he hz)) hphase

private theorem strip_between (h k y : ℝ) (hh : |h| < Real.pi/8) (hk : |k| < Real.pi/8)
    (hy : y ∈ uIcc k h) : |y| < Real.pi/8 := by
  rw [abs_lt]
  rcases le_total k h with ho | ho
  · rw [uIcc_of_le ho] at hy
    constructor <;> linarith [(abs_lt.mp hh).1,(abs_lt.mp hh).2,(abs_lt.mp hk).1,(abs_lt.mp hk).2,hy.1,hy.2]
  · rw [uIcc_of_ge ho] at hy
    constructor <;> linarith [(abs_lt.mp hh).1,(abs_lt.mp hh).2,(abs_lt.mp hk).1,(abs_lt.mp hk).2,hy.1,hy.2]

theorem vertical_interval_integrable (m : ℕ) (t : ℝ) (z : ℂ) (h k : ℝ)
    (hh : |h| < Real.pi/8) (hk : |k| < Real.pi/8) :
    IntervalIntegrable (fun y : ℝ => weight m t z ((y : ℂ)*Complex.I)) volume k h := by
  have hc : ContinuousOn (fun y : ℝ => weight m t z ((y : ℂ)*Complex.I)) (uIcc k h) := by
    intro y hy
    have hw := weight_analyticAt m t z ((y : ℂ)*Complex.I) (by
      simpa [Complex.mul_im] using strip_between h k y hh hk hy)
    exact (ContinuousAt.comp (g := weight m t z) (f := fun a : ℝ => (a : ℂ)*Complex.I)
      hw.continuousAt (by fun_prop)).continuousWithinAt
  exact hc.intervalIntegrable

theorem flow_unequal_heights (m : ℕ) (t : ℝ) (z : ℂ) (h k : ℝ)
    (hh : |h| < Real.pi/8) (hk : |k| < Real.pi/8) :
    RiemannEvenFlow.flow m t z=(horizontalIntegral m t z h+conj (horizontalIntegral m t (conj z) k)+
      Complex.I*(∫ y : ℝ in k..h, weight m t z ((y : ℂ)*Complex.I)))/2 := by
  rw [RiemannEvenFlow.flow,RiemannEvenComplexWeight.jet_zero_eq_halfline,
    RiemannEvenComplexWeight.jet_zero_eq_halfline,
    halfline_contour_shift_signed m t z h hh,
    halfline_contour_shift_signed m t (-z) (-k) (by simpa only [abs_neg] using hk),
    vertical_pair_cancel m t z k hk]
  have hc : horizontalIntegral m t (-z) (-k)=conj (horizontalIntegral m t (conj z) k) := by
    simpa only [Complex.conj_conj] using horizontal_conj m t (conj z) k
  have h0 : |(0 : ℝ)| < Real.pi/8 := by norm_num; positivity
  have hv := intervalIntegral.integral_add_adjacent_intervals
    (vertical_interval_integrable m t z k 0 hk h0) (vertical_interval_integrable m t z h k hh hk)
  change (horizontalIntegral m t z h+Complex.I*(∫ y : ℝ in 0..h, weight m t z ((y : ℂ)*Complex.I))+
    (horizontalIntegral m t (-z) (-k)+Complex.I*(-(∫ y : ℝ in 0..k, weight m t z ((y : ℂ)*Complex.I)))))/2= _
  rw [hc,← hv]
  ring

theorem cosine_margin_between (h k c y : ℝ) (hh : |h| < Real.pi/8) (hk : |k| < Real.pi/8)
    (hch : c ≤ Real.cos (4*h)) (hck : c ≤ Real.cos (4*k)) (hy : y ∈ uIcc k h) :
    c ≤ Real.cos (4*y) := by
  have hh4 : 4*h ∈ Icc (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith [(abs_lt.mp hh).1,(abs_lt.mp hh).2]
  have hk4 : 4*k ∈ Icc (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith [(abs_lt.mp hk).1,(abs_lt.mp hk).2]
  rcases le_total k h with ho | ho
  · rw [uIcc_of_le ho] at hy
    have hm := (strictConcaveOn_cos_Icc.concaveOn).min_le_of_mem_Icc hk4 hh4
      (show 4*y ∈ Icc (4*k) (4*h) by constructor <;> linarith [hy.1,hy.2])
    exact (le_min hck hch).trans hm
  · rw [uIcc_of_ge ho] at hy
    have hm := (strictConcaveOn_cos_Icc.concaveOn).min_le_of_mem_Icc hh4 hk4
      (show 4*y ∈ Icc (4*h) (4*k) by constructor <;> linarith [hy.1,hy.2])
    exact (le_min hch hck).trans hm


theorem vertical_segment_bound (m : ℕ) (t : ℝ) (ht : 0 ≤ t) (z : ℂ) (h k c : ℝ)
    (hh : |h| < Real.pi/8) (hk : |k| < Real.pi/8) (hc : 0 < c)
    (hch : c ≤ Real.cos (4*h)) (hck : c ≤ Real.cos (4*k)) :
    ‖∫ y : ℝ in k..h, weight m t z ((y : ℂ)*Complex.I)‖ ≤
      (528*|h-k|/c^3)*Real.exp (t+|z.re| *|h-k|-z.re*h) := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := k) (b := h) (f := fun y : ℝ => weight m t z ((y : ℂ)*Complex.I))
    (C := (528/c^3)*Real.exp (t+|z.re| *|h-k|-z.re*h)) ?_
  · exact hb.trans_eq (by ring)
  · intro y hy
    have hy' : y ∈ uIcc k h := uIoc_subset_uIcc hy
    have hcos := cosine_margin_between h k c y hh hk hch hck hy'
    have hcos0 : 0 < Real.cos (4*y) := hc.trans_le hcos
    have hystrip := strip_between h k y hh hk hy'
    have hy1 : |y| ≤ 1 := by linarith [Real.pi_lt_four]
    have hy2 : y^2 ≤ 1 := by nlinarith [(abs_le.mp hy1).1,(abs_le.mp hy1).2]
    have hypow : (y^2)^m ≤ 1 := pow_le_one₀ (sq_nonneg y) hy2
    have hty := mul_le_mul_of_nonneg_left hypow ht
    have hdist : |h-y| ≤ |h-k| := abs_sub_right_of_mem_uIcc hy'
    have hm := mul_le_mul_of_nonneg_left hdist (abs_nonneg z.re)
    have hp := le_abs_self (z.re*(h-y))
    rw [abs_mul] at hp
    have hlin : t*(y^2)^m-z.re*y ≤ t+|z.re| *|h-k|-z.re*h := by nlinarith
    have hw := RiemannEvenCompactWeight.compact_weight_bound m t ht z y 0 0 hcos0 (by norm_num) le_rfl
    simp only [zero_pow (by decide : (2 : ℕ) ≠ 0),zero_add,mul_zero,add_zero,
      Complex.ofReal_zero] at hw
    have hcoef : 528/Real.cos (4*y)^3 ≤ 528/c^3 :=
      div_le_div_of_nonneg_left (by norm_num) (pow_pos hc 3) (pow_le_pow_left₀ hc.le hcos 3)
    apply hw.trans
    exact mul_le_mul hcoef (Real.exp_le_exp.mpr hlin) (Real.exp_pos _).le (by positivity)

theorem exists_nonzero_vertical_residual (m : ℕ) (t : ℝ) : ∃ h : ℝ, |h| < Real.pi/8 ∧
    (∫ y : ℝ in 0..h, weight m t 0 ((y : ℂ)*Complex.I)) ≠ 0 := by
  let f : ℝ → ℂ := fun y => weight m t 0 ((y : ℂ)*Complex.I)
  let F : ℝ → ℂ := fun h => ∫ y : ℝ in 0..h, f y
  have hcf (y : ℝ) (hy : |y| < Real.pi/8) : ContinuousAt f y := by
    have hw := weight_analyticAt m t 0 ((y : ℂ)*Complex.I) (by simpa [Complex.mul_im] using hy)
    exact ContinuousAt.comp (g := weight m t 0) (f := fun y : ℝ => (y : ℂ)*Complex.I)
      hw.continuousAt (by fun_prop)
  have hc : ContinuousAt f 0 := hcf 0 (by norm_num; positivity)
  have hCS : ContinuousOn f (ball (0 : ℝ) (Real.pi/8)) := by
    intro y hy
    apply (hcf y ?_).continuousWithinAt
    simpa only [mem_ball,Real.dist_eq,sub_zero] using hy
  have hmeas : StronglyMeasurableAtFilter f (𝓝 (0 : ℝ)) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_ball hCS 0 (by simp; positivity)
  have hd : HasDerivAt F (f 0) 0 :=
    intervalIntegral.integral_hasDerivAt_right IntervalIntegrable.refl hmeas hc
  have hn : f 0 ≠ 0 := by
    dsimp [f,weight]
    apply mul_ne_zero (Complex.exp_ne_zero _)
    apply RiemannThetaComplexKernel.kernel_ne_zero <;> norm_num
  by_contra h
  have heq : F =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℂ)) := by
    change ∀ᶠ y : ℝ in 𝓝 (0 : ℝ), F y = 0
    rw [Metric.eventually_nhds_iff]
    refine ⟨Real.pi/8,by positivity,?_⟩
    intro y hy
    have hstrip : |y| < Real.pi/8 := by simpa only [Real.dist_eq,sub_zero] using hy
    by_contra hne
    exact h ⟨y,hstrip,hne⟩
  have hz : HasDerivAt (fun _ : ℝ => (0 : ℂ)) (f 0) 0 := hd.congr_of_eventuallyEq heq.symm
  exact hn (hz.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ)))

theorem exists_failure_of_omitted_residual (m : ℕ) (t : ℝ) :
    ∃ h : ℝ, |h| < Real.pi/8 ∧ RiemannEvenFlow.flow m t 0 ≠
      (horizontalIntegral m t 0 h+conj (horizontalIntegral m t 0 0))/2 := by
  obtain ⟨h,hh,hV⟩ := exists_nonzero_vertical_residual m t
  refine ⟨h,hh,?_⟩
  intro he
  have hfull := flow_unequal_heights m t 0 h 0 hh (by norm_num; positivity)
  simp only [map_zero] at hfull
  have hi : Complex.I*(∫ y : ℝ in 0..h, weight m t 0 ((y : ℂ)*Complex.I)) = 0 := by
    linear_combination 2*he-2*hfull
  exact hV ((mul_eq_zero.mp hi).resolve_left Complex.I_ne_zero)

end OperatorDerivativeRewrite.Foundation.RiemannEvenHorizontalPairing
