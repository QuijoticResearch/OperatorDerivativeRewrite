import Foundation.RiemannSixthTransitionCompact
import Foundation.RiemannSixthComplexReflectedDominance
import Foundation.RiemannQuarticTransitionReflection
/-! Actual reflected-channel noncancellation on sixth-order transition scales.
Complex centers, theta margins, signed integrals and nonzero main normalization
are explicit. The compact decay uses the fifth-power scale and factor32. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthTransitionReflection
open RiemannSixthTransitionCorrection RiemannSixthTransitionGaussian
open RiemannSixthTransitionContour RiemannSixthTransitionCompact
open RiemannEvenModelPhase RiemannEvenSaddleBranch RiemannEvenComplexWeight
open RiemannThetaComplexKernel RiemannQuarticErrorLimits
open RiemannQuarticTransitionReflection (reflectionCutoff reflectionCutoff_pos reflectionCutoff_small)
open RiemannSixthTransitionAnalyticBranch (moving_scale_ratio_bound)
section Scaled
variable (t K : ℝ) (c₀ w v : ℂ)
  (ht : 1 ≤ t) (hK : 8 ≤ K) (hr : 120020 ≤ w.re)
  (hmargin : t*w.re^5+8 ≤ 4*Real.pi*(Complex.exp (4*w)).re) (hi : |w.im| ≤ 1/2)
  (hn : ‖w‖ ≤ 2*w.re)
  (hs : modelDerivative 3 t w= -(Complex.I*c₀)) (hE : ‖Complex.exp (4*w)‖ ≤ K)
  (harith : (30005*Real.exp (-w.re))*K ≤ t*w.re^5/4)
  (hv : ‖v-w‖ ≤ 1/K)
include ht hK hr hmargin hi hn hs hE harith hv

theorem positive_compact_bound (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z)) (hy : z.im ≤ 0) :
    ‖∫ s : ℝ in 0..v.re-1, weight 3 t z ((s : ℂ)+(v.im : ℂ)*Complex.I)‖ ≤
      528*(v.re-1)*‖weight 3 t z v‖*Real.exp (5*v.re+3-2*t*v.re^5) := by
  have hg := corrected_geometry t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv
  have hd := RiemannSixthTransitionGaussian.horizontal_neighbor_domain t K c₀ w v
    ht hK (by linarith) hmargin hi hn hs hE harith hv 0 (by norm_num)
  simp only [Complex.ofReal_zero, add_zero] at hd
  have hh : |v.im| ≤ 1 := hg.2.1.le.trans (by linarith [Real.pi_lt_four])
  have herr : ‖complexSlope 3 t v-modelDerivative 3 t v‖ ≤ 1 := by
    have he := RiemannSixthTransitionGaussian.horizontal_neighbor_error t K c₀ w v
      ht hK (by linarith) hmargin hi hn hs hE harith hv 0 (by norm_num)
    simp only [Complex.ofReal_zero, add_zero] at he
    have hb := RiemannQuarticFarCorrection.small_error_at_large_real_part w.re hr
    have hExp := Real.exp_le_exp.mpr (show -4*w.re+4 ≤ -w.re by linarith)
    nlinarith
  have hupper := RiemannSixthComplexLeftCompact.actual_center_theta_upper t (by linarith) z v hg.1 hh hz herr
  have hvext : (v.re : ℂ)+(v.im : ℂ)*Complex.I=v := Complex.re_add_im v
  have ha1 : 0 ≤ v.re-1 := by linarith [hg.1]
  have h := RiemannSixthComplexLeftCompact.actual_left_compact_bound t ht z v.re v.im
    hg.1 hh hy (by simpa only [hvext] using hd.2.1) (by simpa only [hvext] using hupper)
  rw [hvext] at h
  apply h.trans
  have he := Real.exp_le_exp.mpr (show 5*v.re+3-2*t*v.re^5+3*z.im/4 ≤ 5*v.re+3-2*t*v.re^5 by linarith)
  exact mul_le_mul_of_nonneg_left he (by positivity)


theorem relative_positive_compact_bound (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z)) (hy : z.im ≤ 0) :
    ‖(∫ s : ℝ in 0..v.re-1, weight 3 t z ((s : ℂ)+(v.im : ℂ)*Complex.I))/
      (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))‖ ≤
      4224*Real.sqrt K*(t*w.re^5)*Real.exp (-(t*w.re^5)/32) := by
  have h := positive_compact_bound t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv z hz hy
  have hg := corrected_geometry t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv
  have hd : ‖v-w‖ ≤ 1/2 := hv.trans ((div_le_iff₀ (by linarith : 0 < K)).mpr (by linarith))
  have hc := (Complex.abs_re_le_norm (v-w)).trans hd
  simp only [Complex.sub_re] at hc
  have hva : w.re ≤ 2*v.re := by linarith [(abs_le.mp hc).1]
  have hcube := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith : 0 ≤ w.re) hva 5)
    (show 0 ≤ t by linarith)
  have hpoly : 5*v.re+3 ≤ v.re^5 := by
    have hsq : 4096 ≤ v.re^2 := by nlinarith [hg.1]
    have hcu := mul_le_mul_of_nonneg_right hsq (by linarith [hg.1] : 0 ≤ v.re)
    have h35 : v.re^3 ≤ v.re^5 := pow_le_pow_right₀ (by linarith [hg.1] : 1 ≤ v.re) (by norm_num)
    nlinarith [hg.1]
  have htime : v.re^5 ≤ t*v.re^5 := by nlinarith [pow_nonneg (by linarith [hg.1] : 0 ≤ v.re) 5]
  have hexp : 5*v.re+3-2*t*v.re^5 ≤ -(t*w.re^5)/32 := by nlinarith
  have hQ : v.re-1 ≤ t*w.re^5 := by
    have hh : w.re ≤ w.re^5 := by
      have hsq : 1 ≤ w.re^4 := one_le_pow₀ (by linarith : 1 ≤ w.re)
      nlinarith [mul_le_mul_of_nonneg_right hsq (by linarith : 0 ≤ w.re)]
    have htcu : w.re^5 ≤ t*w.re^5 := by nlinarith [pow_nonneg (by linarith : 0 ≤ w.re) 5]
    linarith [(abs_le.mp hc).2]
  let W := weight 3 t z v
  let G := ∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)
  let L := ∫ s : ℝ in 0..v.re-1, weight 3 t z ((s : ℂ)+(v.im : ℂ)*Complex.I)
  let B := 528*(t*w.re^5)*Real.exp (-(t*w.re^5)/32)
  have hnum : ‖L‖ ≤ ‖W‖*B := by
    apply h.trans
    have hm := mul_le_mul hQ (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le
      (show 0 ≤ t*w.re^5 by positivity)
    have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ 528*‖W‖ by positivity)
    dsimp [L,W,B] at *
    nlinarith
  have hnormal := gaussian_normalization_lower t K c₀ w v ht hK (by linarith) hmargin hi hn hs hE harith hv
  change 1 ≤ 8*Real.sqrt K*‖G‖ at hnormal
  have hG : G ≠ 0 := by intro h; norm_num [h] at hnormal
  have hW : W ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) hg.2.2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  change ‖L/(W*G)‖ ≤ _
  rw [norm_div, norm_mul]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hW) (norm_pos_iff.mpr hG))).mpr
  have hm := mul_le_mul_of_nonneg_left hnormal (mul_nonneg (norm_nonneg W) hB)
  dsimp [B] at *
  nlinarith

theorem reflected_compact_bound (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z)) (hy : z.im ≤ 0) :
    ‖∫ s : ℝ in 0..v.re-1, weight 3 t (-z) ((s : ℂ)-(v.im : ℂ)*Complex.I)‖ ≤
      528*(v.re-1)*‖weight 3 t z v‖*Real.exp (5*v.re+3-2*t*v.re^5) := by
  have hg := corrected_geometry t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv
  have hd := RiemannSixthTransitionGaussian.horizontal_neighbor_domain t K c₀ w v
    ht hK (by linarith) hmargin hi hn hs hE harith hv 0 (by norm_num)
  simp only [Complex.ofReal_zero, add_zero] at hd
  have hh : |v.im| ≤ 1 := hg.2.1.le.trans (by linarith [Real.pi_lt_four])
  have herr : ‖complexSlope 3 t v-modelDerivative 3 t v‖ ≤ 1 := by
    have he := RiemannSixthTransitionGaussian.horizontal_neighbor_error t K c₀ w v
      ht hK (by linarith) hmargin hi hn hs hE harith hv 0 (by norm_num)
    simp only [Complex.ofReal_zero, add_zero] at he
    have hb := RiemannQuarticFarCorrection.small_error_at_large_real_part w.re hr
    have hExp := Real.exp_le_exp.mpr (show -4*w.re+4 ≤ -w.re by linarith)
    nlinarith
  have hupper := RiemannSixthComplexLeftCompact.actual_center_theta_upper t (by linarith) z v hg.1 hh hz herr
  have hvext : (v.re : ℂ)+(v.im : ℂ)*Complex.I=v := Complex.re_add_im v
  have ha1 : 0 ≤ v.re-1 := by linarith [hg.1]
  have h := RiemannSixthComplexReflectedDominance.reflected_left_compact_bound t ht z v.re v.im
    hg.1 hh hy (by simpa only [hvext] using hd.2.1) (by simpa only [hvext] using hupper)
  rw [hvext] at h
  apply h.trans
  have he := Real.exp_le_exp.mpr (show 5*v.re+3-2*t*v.re^5+3*z.im/4 ≤ 5*v.re+3-2*t*v.re^5 by linarith)
  exact mul_le_mul_of_nonneg_left he (by positivity)


theorem relative_reflected_compact_bound (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z)) (hy : z.im ≤ 0) :
    ‖(∫ s : ℝ in 0..v.re-1, weight 3 t (-z) ((s : ℂ)-(v.im : ℂ)*Complex.I))/
      (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))‖ ≤
      4224*Real.sqrt K*(t*w.re^5)*Real.exp (-(t*w.re^5)/32) := by
  have h := reflected_compact_bound t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv z hz hy
  have hg := corrected_geometry t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv
  have hd : ‖v-w‖ ≤ 1/2 := hv.trans ((div_le_iff₀ (by linarith : 0 < K)).mpr (by linarith))
  have hc := (Complex.abs_re_le_norm (v-w)).trans hd
  simp only [Complex.sub_re] at hc
  have hva : w.re ≤ 2*v.re := by linarith [(abs_le.mp hc).1]
  have hcube := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith : 0 ≤ w.re) hva 5)
    (show 0 ≤ t by linarith)
  have hpoly : 5*v.re+3 ≤ v.re^5 := by
    have hsq : 4096 ≤ v.re^2 := by nlinarith [hg.1]
    have hcu := mul_le_mul_of_nonneg_right hsq (by linarith [hg.1] : 0 ≤ v.re)
    have h35 : v.re^3 ≤ v.re^5 := pow_le_pow_right₀ (by linarith [hg.1] : 1 ≤ v.re) (by norm_num)
    nlinarith [hg.1]
  have htime : v.re^5 ≤ t*v.re^5 := by nlinarith [pow_nonneg (by linarith [hg.1] : 0 ≤ v.re) 5]
  have hexp : 5*v.re+3-2*t*v.re^5 ≤ -(t*w.re^5)/32 := by nlinarith
  have hQ : v.re-1 ≤ t*w.re^5 := by
    have hh : w.re ≤ w.re^5 := by
      have hsq : 1 ≤ w.re^4 := one_le_pow₀ (by linarith : 1 ≤ w.re)
      nlinarith [mul_le_mul_of_nonneg_right hsq (by linarith : 0 ≤ w.re)]
    have htcu : w.re^5 ≤ t*w.re^5 := by nlinarith [pow_nonneg (by linarith : 0 ≤ w.re) 5]
    linarith [(abs_le.mp hc).2]
  let W := weight 3 t z v
  let G := ∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)
  let L := ∫ s : ℝ in 0..v.re-1, weight 3 t (-z) ((s : ℂ)-(v.im : ℂ)*Complex.I)
  let B := 528*(t*w.re^5)*Real.exp (-(t*w.re^5)/32)
  have hnum : ‖L‖ ≤ ‖W‖*B := by
    apply h.trans
    have hm := mul_le_mul hQ (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le
      (show 0 ≤ t*w.re^5 by positivity)
    have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ 528*‖W‖ by positivity)
    dsimp [L,W,B] at *
    nlinarith
  have hnormal := gaussian_normalization_lower t K c₀ w v ht hK (by linarith) hmargin hi hn hs hE harith hv
  change 1 ≤ 8*Real.sqrt K*‖G‖ at hnormal
  have hG : G ≠ 0 := by intro h; norm_num [h] at hnormal
  have hW : W ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) hg.2.2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  change ‖L/(W*G)‖ ≤ _
  rw [norm_div, norm_mul]
  apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hW) (norm_pos_iff.mpr hG))).mpr
  have hm := mul_le_mul_of_nonneg_left hnormal (mul_nonneg (norm_nonneg W) hB)
  dsimp [B] at *
  nlinarith

theorem reflected_outer_mass_bound (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z)) (hy : z.im ≤ 0) :
    IntegrableOn (fun s : ℝ => weight 3 t (-z) (conj v+(s : ℂ))) (Ioi (-1)) ∧
      ‖∫ s : ℝ in Ioi (-1), weight 3 t (-z) (conj v+(s : ℂ))‖ ≤
        3000*‖weight 3 t z v‖*Real.exp (2*z.im*(v.re-1))*Real.sqrt (Real.pi/(t*w.re^5/4096)) := by
  have hg := corrected_geometry t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv
  have hcont : Continuous (fun s : ℝ => weight 3 t (-z) (conj v+(s : ℂ))) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    have hq : |(conj v+(s : ℂ)).im| < Real.pi/8 := by simpa using hg.2.1
    exact ContinuousAt.comp (g := weight 3 t (-z)) (f := fun s : ℝ => conj v+(s : ℂ))
      (weight_analyticAt 3 t (-z) (conj v+(s : ℂ)) hq).continuousAt (by fun_prop)
  let A := 3000*‖weight 3 t z v‖*Real.exp (2*z.im*(v.re-1))
  let b := t*w.re^5/4096
  have hb : 0 < b := by dsimp [b]; positivity
  have hbound : ∀ s : ℝ, -1 ≤ s →
      ‖weight 3 t (-z) (conj v+(s : ℂ))‖ ≤ A*Real.exp (-b*s^2) := by
    intro s hsl
    have hmain := actual_gaussian_mass_envelope t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv z hz s hsl
    have hm := mul_nonpos_of_nonpos_of_nonneg hy (show 0 ≤ s+1 by linarith)
    have hexp : 2*z.im*(v.re+s) ≤ 2*z.im*(v.re-1) := by nlinarith
    have hconj : conj (v+(s : ℂ))=conj v+(s : ℂ) := by simp
    rw [← hconj, RiemannEvenComplexReflection.reflected_weight_norm]
    simp only [Complex.add_re, Complex.ofReal_re]
    have hprod := mul_le_mul hmain (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (by positivity)
    exact hprod.trans_eq (by dsimp [A,b]; ring)
  have hmajor : Integrable (fun s : ℝ => A*Real.exp (-b*s^2)) :=
    (integrable_exp_neg_mul_sq hb).const_mul A
  have hpoint : ∀ᵐ s : ℝ ∂volume.restrict (Ioi (-1)),
      ‖weight 3 t (-z) (conj v+(s : ℂ))‖ ≤ A*Real.exp (-b*s^2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs1
    exact hbound s hs1.le
  refine ⟨hmajor.integrableOn.mono' hcont.aestronglyMeasurable hpoint, ?_⟩
  have hnorm := norm_integral_le_of_norm_le hmajor.integrableOn hpoint
  have hwhole := setIntegral_le_integral (s := Ioi (-1)) hmajor
    (Eventually.of_forall (fun s : ℝ => (show 0 ≤ A*Real.exp (-b*s^2) from by dsimp [A]; positivity)))
  apply hnorm.trans (hwhole.trans_eq ?_)
  rw [integral_const_mul, integral_gaussian]

theorem relative_reflected_outer_bound (C : ℝ) (hC : 0 < C) (hscale : K ≤ C*(t*w.re^5))
    (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z)) (hy : z.im ≤ 0) :
    ‖(∫ s : ℝ in Ioi (-1), weight 3 t (-z) (conj v+(s : ℂ)))/
      (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))‖ ≤
      3072000*Real.sqrt C*Real.exp (2*z.im*(v.re-1)) := by
  have hmass := (reflected_outer_mass_bound t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv z hz hy).2
  have hQ : 0 < t*w.re^5 := by positivity
  have hroot : Real.sqrt K*Real.sqrt (Real.pi/(t*w.re^5/4096)) ≤ 128*Real.sqrt C := by
    have hKroot := Real.sqrt_le_sqrt hscale
    rw [Real.sqrt_mul hC.le] at hKroot
    have harg : Real.pi/(t*w.re^5/4096)=4096*Real.pi/(t*w.re^5) := by ring
    have hprod : Real.sqrt (t*w.re^5)*Real.sqrt (Real.pi/(t*w.re^5/4096))=Real.sqrt (4096*Real.pi) := by
      rw [← Real.sqrt_mul hQ.le, harg]
      congr 1
      field_simp
    have hpi : Real.sqrt (4096*Real.pi) ≤ 128 := by
      apply (Real.sqrt_le_iff).mpr
      constructor <;> nlinarith [Real.pi_lt_four]
    have hm := mul_le_mul_of_nonneg_right hKroot (Real.sqrt_nonneg (Real.pi/(t*w.re^5/4096)))
    rw [mul_assoc, hprod] at hm
    have hmC := mul_le_mul_of_nonneg_left hpi (Real.sqrt_nonneg C)
    nlinarith
  let W := weight 3 t z v
  let G := ∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)
  let L := ∫ s : ℝ in Ioi (-1), weight 3 t (-z) (conj v+(s : ℂ))
  let B := 3000*Real.exp (2*z.im*(v.re-1))*Real.sqrt (Real.pi/(t*w.re^5/4096))
  have hnum : ‖L‖ ≤ ‖W‖*B := hmass.trans_eq (by dsimp [W,B]; ring)
  have hnormal := gaussian_normalization_lower t K c₀ w v ht hK (by linarith) hmargin hi hn hs hE harith hv
  change 1 ≤ 8*Real.sqrt K*‖G‖ at hnormal
  have hG : G ≠ 0 := by intro h; norm_num [h] at hnormal
  have hg := corrected_geometry t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv
  have hW : W ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) hg.2.2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hratio : ‖L/(W*G)‖ ≤ 8*Real.sqrt K*B := by
    rw [norm_div, norm_mul]
    apply (div_le_iff₀ (mul_pos (norm_pos_iff.mpr hW) (norm_pos_iff.mpr hG))).mpr
    have hm := mul_le_mul_of_nonneg_left hnormal (mul_nonneg (norm_nonneg W) hB)
    nlinarith
  change ‖L/(W*G)‖ ≤ _
  apply hratio.trans
  have hm := mul_le_mul_of_nonneg_right hroot (Real.exp_pos (2*z.im*(v.re-1))).le
  dsimp [B]
  nlinarith

theorem reflected_horizontal_split (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z)) (hy : z.im ≤ 0) :
    (∫ s : ℝ in Ioi 0, weight 3 t (-z) ((s : ℂ)-(v.im : ℂ)*Complex.I))=
      (∫ s : ℝ in 0..v.re-1, weight 3 t (-z) ((s : ℂ)-(v.im : ℂ)*Complex.I))+
      (∫ s : ℝ in Ioi (-1), weight 3 t (-z) (conj v+(s : ℂ))) := by
  have hg := corrected_geometry t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv
  have hmass := reflected_outer_mass_bound t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv z hz hy
  have hsplit := RiemannEvenHorizontalDecomposition.horizontal_decomposition 3 t (-z) (conj v)
    (by simpa using hg.2.1) (-1) hmass.1
  simp only [Complex.conj_re, Complex.conj_im, Complex.ofReal_neg, neg_mul, neg_neg,
    ← sub_eq_add_neg] at hsplit
  have hrev : (∫ s : ℝ in (1 : ℝ)..(-1), weight 3 t (-z) (conj v+(s : ℂ)))=
      -(∫ s : ℝ in (-1 : ℝ)..1, weight 3 t (-z) (conj v+(s : ℂ))) :=
    intervalIntegral.integral_symm (-1) 1
  linear_combination hsplit+hrev

theorem reflected_outer_cutoff_bound (C : ℝ) (hC : 0 < C) (hscale : K ≤ C*(t*w.re^5))
    (z : ℂ) (hz : complexSlope 3 t v= -(Complex.I*z))
    (hthreshold : z.im ≤ -reflectionCutoff C/w.re) :
    ‖(∫ s : ℝ in Ioi (-1), weight 3 t (-z) (conj v+(s : ℂ)))/
      (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))‖ ≤ 1/8 := by
  have ha : 0 < w.re := by linarith
  have hL := reflectionCutoff_pos C hC
  have hy : z.im ≤ 0 := hthreshold.trans (div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le)
  have hyA := (le_div_iff₀ ha).mp hthreshold
  have hd : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ (by linarith : 0 < K)).mpr (by linarith))
  have hc := (Complex.abs_re_le_norm (v-w)).trans hd
  simp only [Complex.sub_re] at hc
  have hhalf : w.re/2 ≤ v.re-1 := by linarith [(abs_le.mp hc).1]
  have hm := mul_nonpos_of_nonpos_of_nonneg hy (show 0 ≤ 2*(v.re-1)-w.re by linarith)
  have hexp : 2*z.im*(v.re-1) ≤ -reflectionCutoff C := by nlinarith
  apply (relative_reflected_outer_bound t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv C hC hscale z hz hy).trans
  apply (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)).trans
  exact reflectionCutoff_small C hC

end Scaled

theorem eventually_uniform_lower_horizontal_error (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ Q : ℝ in atTop, ∀ (t K : ℝ) (c₀ w v z : ℂ),
      1 ≤ t → 8 ≤ K → 120020 ≤ w.re → t*w.re^5+8 ≤ 4*Real.pi*(Complex.exp (4*w)).re → |w.im| ≤ 1/2 → ‖w‖ ≤ 2*w.re →
      modelDerivative 3 t w= -(Complex.I*(c₀ : ℂ)) → ‖Complex.exp (4*w)‖ ≤ K → (30005*Real.exp (-w.re))*K ≤ t*w.re^5/4 → ‖v-w‖ ≤ 1/K →
      complexSlope 3 t v= -(Complex.I*z) → z.im ≤ 0 → Q=t*w.re^5 → K ≤ C*Q →
      ‖(∫ s : ℝ in Ioi 0, weight 3 t z ((s : ℂ)+(v.im : ℂ)*Complex.I))/
        (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))-1‖ < ε := by
  filter_upwards [eventually_uniform_relative_outer_error C (ε/2) hC (half_pos hε),
    eventually_ge_atTop (1 : ℝ),
    (compact_budget_tendsto_zero C).eventually (gt_mem_nhds (half_pos hε))]
    with Q houter hQ hbudget
  intro t K c₀ w v z ht hK hr hmargin hi hn hs hE harith hv hstat hy hQid hratio
  have ho := houter t K c₀ w v z ht hK hr hmargin hi hn hs hE harith hv hstat hQid hratio
  have hc := relative_positive_compact_bound t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv z hstat hy
  rw [← hQid] at hc
  have hroot : Real.sqrt K ≤ Real.sqrt C*Q := by
    have hh : Real.sqrt Q ≤ Q := by nlinarith [Real.sq_sqrt (show 0 ≤ Q by linarith), Real.sqrt_nonneg Q]
    have hmul := mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg C)
    have hrK := Real.sqrt_le_sqrt hratio
    rw [Real.sqrt_mul hC.le] at hrK
    linarith
  have hmul := mul_le_mul_of_nonneg_right hroot (show 0 ≤ 4224*Q*Real.exp (-Q/32) by positivity)
  have hcomp :
      ‖(∫ s : ℝ in 0..v.re-1, weight 3 t z ((s : ℂ)+(v.im : ℂ)*Complex.I))/
        (weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2)))‖ < ε/2 := by
    nlinarith
  have hsplit := horizontal_compact_outer_identity t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv z hstat
  let D := weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2))
  let H := ∫ s : ℝ in Ioi 0, weight 3 t z ((s : ℂ)+(v.im : ℂ)*Complex.I)
  let L := ∫ s : ℝ in Ioi (-1), weight 3 t z (v+(s : ℂ))
  let B := ∫ s : ℝ in 0..v.re-1, weight 3 t z ((s : ℂ)+(v.im : ℂ)*Complex.I)
  have hid : H/D-1=(L/D-1)+B/D := by
    change H=B+L at hsplit
    rw [hsplit, add_div]
    ring
  change ‖H/D-1‖ < ε
  rw [hid]
  have htri := norm_add_le (L/D-1) (B/D)
  change ‖L/D-1‖ < ε/2 at ho
  change ‖B/D‖ < ε/2 at hcomp
  linarith

theorem eventually_uniform_nonzero_lower (C : ℝ) (hC : 0 < C) :
    ∀ᶠ Q : ℝ in atTop, ∀ (t K : ℝ) (c₀ w v z : ℂ),
      1 ≤ t → 8 ≤ K → 120020 ≤ w.re → t*w.re^5+8 ≤ 4*Real.pi*(Complex.exp (4*w)).re → |w.im| ≤ 1/2 → ‖w‖ ≤ 2*w.re →
      modelDerivative 3 t w= -(Complex.I*c₀) → ‖Complex.exp (4*w)‖ ≤ K → (30005*Real.exp (-w.re))*K ≤ t*w.re^5/4 → ‖v-w‖ ≤ 1/K →
      complexSlope 3 t v= -(Complex.I*z) → Q=t*w.re^5 → K ≤ C*Q →
      z.im ≤ -reflectionCutoff C/w.re → RiemannEvenFlow.flow 3 t z ≠ 0 := by
  filter_upwards [eventually_uniform_lower_horizontal_error C (1/4) hC (by norm_num),
    eventually_ge_atTop (1 : ℝ),
    (compact_budget_tendsto_zero C).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/8))]
    with Q hmain hQ hcompact
  intro t K c₀ w v z ht hK hr hmargin hi hn hs hE harith hv hstat hQid hscale hthreshold hzero
  have ha : 0 < w.re := by linarith
  have hy : z.im ≤ 0 := hthreshold.trans (div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (reflectionCutoff_pos C hC).le) ha.le)
  have hM := hmain t K c₀ w v z ht hK hr hmargin hi hn hs hE harith hv hstat hy hQid hscale
  have hCpt := relative_reflected_compact_bound t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv z hstat hy
  rw [← hQid] at hCpt
  have hroot : Real.sqrt K ≤ Real.sqrt C*Q := by
    have hh : Real.sqrt Q ≤ Q := by nlinarith [Real.sq_sqrt (show 0 ≤ Q by linarith), Real.sqrt_nonneg Q]
    have hm := mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg C)
    have hk := Real.sqrt_le_sqrt hscale
    rw [Real.sqrt_mul hC.le] at hk
    linarith
  have hmul := mul_le_mul_of_nonneg_right hroot (show 0 ≤ 4224*Q*Real.exp (-Q/32) by positivity)
  let D := weight 3 t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) v*(s : ℂ)^2/2))
  let M := ∫ s : ℝ in Ioi 0, weight 3 t z ((s : ℂ)+(v.im : ℂ)*Complex.I)
  let O := ∫ s : ℝ in Ioi 0, weight 3 t (-z) ((s : ℂ)-(v.im : ℂ)*Complex.I)
  let B := ∫ s : ℝ in 0..v.re-1, weight 3 t (-z) ((s : ℂ)-(v.im : ℂ)*Complex.I)
  let T := ∫ s : ℝ in Ioi (-1), weight 3 t (-z) (conj v+(s : ℂ))
  have hB : ‖B/D‖ < (1/8 : ℝ) := by
    change ‖B/D‖ ≤ _ at hCpt
    nlinarith
  have hT := reflected_outer_cutoff_bound t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv C hC
    (by simpa only [hQid] using hscale) z hstat hthreshold
  change ‖T/D‖ ≤ (1/8 : ℝ) at hT
  have hsplit := reflected_horizontal_split t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv z hstat hy
  change O=B+T at hsplit
  have hO : ‖O/D‖ ≤ (1/4 : ℝ) := by
    rw [hsplit, add_div]
    exact (norm_add_le _ _).trans (by linarith)
  have hg := corrected_geometry t K c₀ w v ht hK hr hmargin hi hn hs hE harith hv
  have hf := RiemannEvenNaturalContour.flow_eq_paired_horizontal 3 t z v.im hg.2.1
  rw [hzero] at hf
  change 0=(M+O)/2 at hf
  have hsum : M+O=0 := by linear_combination -2*hf
  have heq : (M/D-1)+O/D= -1 := by
    calc
      _ = (M+O)/D-1 := by ring
      _ = _ := by rw [hsum, zero_div, zero_sub]
  have htri := norm_add_le (M/D-1) (O/D)
  rw [heq, norm_neg, norm_one] at htri
  change ‖M/D-1‖ < (1/4 : ℝ) at hM
  linarith

theorem eventually_actual_nonzero_lower (M : ℝ) (hM : 0 ≤ M) :
    ∀ᶠ t : ℝ in atTop, ∀ u : ℝ, 65536*(M+7) ≤ u → RiemannEvenRealSaddle.phaseSlope 3 t u=0 →
      ∀ z : ℂ, ‖z‖ ≤ M*RiemannQuarticTransitionSaddle.realScale u →
        z.im ≤ -(2*reflectionCutoff (1024*(M+8)))/u → RiemannEvenFlow.flow 3 t z ≠ 0 := by
  let C := 1024*(M+8)
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨U,hU⟩ := eventually_atTop.1 (eventually_uniform_nonzero_lower C hC)
  filter_upwards [eventually_ge_atTop (max U 1)] with t htU
  intro u hu hs z hz hy
  have ht : 1 ≤ t := (le_max_right U 1).trans htU
  have hu0 : 0 < u := by linarith
  have hL := reflectionCutoff_pos C hC
  have hy0 : z.im ≤ 0 := hy.trans (div_nonpos_of_nonpos_of_nonneg (by change -(2*reflectionCutoff C) ≤ 0; linarith) hu0.le)
  obtain ⟨w,hw,_⟩ := RiemannSixthTransitionSaddle.existsUnique_transition_model_saddle
    t u M z ht hM hu hs (by linarith) hz
  have hd := transition_scale_data t u M z w ht hM hu hs (by linarith) hz hw.1 hw.2
  let K := (M+8)*RiemannQuarticTransitionSaddle.realScale u
  have hK0 : 0 < K := by dsimp [K]; positivity [RiemannQuarticTransitionSaddle.realScale_pos u]
  have hwpos : 0 < w.re := by linarith [hd.2.1]
  obtain ⟨v,hv,_⟩ := actual_scaled_frequency_disk t K z w z ht hd.1 hd.2.1 hd.2.2.2.2.2.2 hd.2.2.1
    hd.2.2.2.1 (by linarith) hw.2 hd.2.2.2.2.1 hd.2.2.2.2.2.1 (by simp; positivity)
  have hvdist : ‖v-w‖ ≤ 1/K := by simpa only [mem_closedBall, dist_eq_norm] using hv.1
  have hg := RiemannSixthTransitionSaddle.transition_model_geometry t u M z w ht hM hu hs (by linarith) hz hw.1 hw.2
  have hscale : K ≤ C*(t*w.re^5) := moving_scale_ratio_bound t u M w ht hM hu hs hg.1
  have hcoord := (Complex.abs_re_le_norm (w-(u : ℂ))).trans hg.1
  simp only [Complex.sub_re, Complex.ofReal_re] at hcoord
  have hlarge : 120020 ≤ w.re := by linarith [(abs_le.mp hcoord).1]
  have huW : u ≤ 2*w.re := by linarith [(abs_le.mp hcoord).1]
  have hyu := (le_div_iff₀ hu0).mp hy
  have hmul := mul_nonpos_of_nonpos_of_nonneg hy0 (show 0 ≤ 2*w.re-u by linarith)
  have hthreshold : z.im ≤ -reflectionCutoff C/w.re := by
    apply (le_div_iff₀ hwpos).mpr
    change z.im*u ≤ -(2*reflectionCutoff C) at hyu
    nlinarith
  have hQ : U ≤ t*w.re^5 := by
    have hp : 1 ≤ w.re^5 := one_le_pow₀ (by linarith : 1 ≤ w.re)
    have hh := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ t)
    linarith [(le_max_left U 1).trans htU]
  exact hU (t*w.re^5) hQ t K z w v z ht hd.1 hlarge hd.2.2.2.2.2.2 hd.2.2.1 hd.2.2.2.1
    hw.2 hd.2.2.2.2.1 hd.2.2.2.2.2.1 hvdist hv.2 rfl hscale hthreshold

end OperatorDerivativeRewrite.Foundation.RiemannSixthTransitionReflection
