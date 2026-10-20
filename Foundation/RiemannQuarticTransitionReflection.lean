import Foundation.RiemannQuarticTransitionCompact
/-! Reflected arithmetic channels on the bounded transition scales.
The normalization is always the nonzero MAIN actual Gaussian amplitude.
Only the exact endpoint-cancelled pair is used for full-flow conclusions. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticTransitionReflection
open RiemannQuarticTransitionCorrection RiemannQuarticTransitionGaussian
open RiemannQuarticTransitionContour RiemannQuarticTransitionCompact
open RiemannQuarticSaddleTheta RiemannQuarticSaddleBranch RiemannQuarticFrequencyBranch
open RiemannQuarticFarModelSaddle RiemannThetaComplexKernel RiemannQuarticErrorLimits
open RiemannQuarticNaturalContour RiemannQuarticComplexContour

def reflectionCutoff (C : ℝ) : ℝ := 100000000*(C+1)

theorem reflectionCutoff_pos (C : ℝ) (hC : 0 < C) : 0 < reflectionCutoff C := by
  unfold reflectionCutoff
  positivity

theorem reflectionCutoff_small (C : ℝ) (hC : 0 < C) :
    3072000*Real.sqrt C*Real.exp (-reflectionCutoff C) ≤ 1/8 := by
  have hsqrt : Real.sqrt C ≤ C+1 := by nlinarith [Real.sq_sqrt hC.le, Real.sqrt_nonneg C]
  have he := Real.add_one_le_exp (reflectionCutoff C)
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-reflectionCutoff C)).le
  have hid : Real.exp (reflectionCutoff C)*Real.exp (-reflectionCutoff C)=1 := by rw [← Real.exp_add]; simp
  rw [hid] at hm
  have hprod : reflectionCutoff C*Real.exp (-reflectionCutoff C) ≤ 1 := by nlinarith [Real.exp_pos (-reflectionCutoff C)]
  have hcoef : 3072000*Real.sqrt C ≤ reflectionCutoff C/8 := by unfold reflectionCutoff; linarith
  have hh := mul_le_mul_of_nonneg_right hcoef (Real.exp_pos (-reflectionCutoff C)).le
  nlinarith

section Scaled
variable (t K : ℝ) (c₀ w v : ℂ)
  (ht : 1 ≤ t) (hK : 8 ≤ K) (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
  (hn : ‖w‖ ≤ 2*w.re) (hcenter : c₀.im ≤ 1)
  (hs : modelDerivative t w= -(Complex.I*c₀)) (hE : ‖Complex.exp (4*w)‖ ≤ K)
  (hv : ‖v-w‖ ≤ 1/K)
include ht hK hr hi hn hcenter hs hE hv

theorem reflected_compact_bound (z : ℂ) (hz : complexSlope t v= -(Complex.I*z)) (hy : z.im ≤ 0) :
    ‖∫ s : ℝ in 0..v.re-1, saddleWeight t (-z) ((s : ℂ)-(v.im : ℂ)*Complex.I)‖ ≤
      528*(v.re-1)*‖saddleWeight t z v‖*Real.exp (5*v.re+3-2*t*v.re^3) := by
  have hg := corrected_geometry t K c₀ w v ht hK hr hi hn hcenter hs hE hv
  have hd := RiemannQuarticTransitionGaussian.horizontal_neighbor_domain t K c₀ w v
    ht hK (by linarith) hi hn hcenter hs hE hv 0 (by norm_num)
  simp only [Complex.ofReal_zero, add_zero] at hd
  have hh : |v.im| ≤ 1 := hg.2.1.le.trans (by linarith [Real.pi_lt_four])
  have herr : ‖complexSlope t v-modelDerivative t v‖ ≤ 1 := by
    have he := RiemannQuarticTransitionGaussian.horizontal_neighbor_error t K c₀ w v
      ht hK (by linarith) hi hn hcenter hs hE hv 0 (by norm_num)
    simp only [Complex.ofReal_zero, add_zero] at he
    have hb := RiemannQuarticFarCorrection.small_error_at_large_real_part w.re hr
    have hExp := Real.exp_le_exp.mpr (show -4*w.re+4 ≤ -w.re by linarith)
    nlinarith
  have hupper := RiemannQuarticComplexCompactTail.actual_center_theta_upper t (by linarith) z v hd.1 hz herr
  have hvext : (v.re : ℂ)+(v.im : ℂ)*Complex.I=v := Complex.re_add_im v
  have ha1 : 0 ≤ v.re-1 := by linarith [hg.1]
  have h := RiemannQuarticReflectedDominance.reflected_left_compact_bound t ht z v.re v.im
    hg.1 hh hy (by simpa only [hvext] using hd.2.1) (by simpa only [hvext] using hupper)
  rw [hvext] at h
  apply h.trans
  have he := Real.exp_le_exp.mpr (show 5*v.re+3-2*t*v.re^3+3*z.im/4 ≤ 5*v.re+3-2*t*v.re^3 by linarith)
  exact mul_le_mul_of_nonneg_left he (by positivity)


theorem relative_reflected_compact_bound (z : ℂ) (hz : complexSlope t v= -(Complex.I*z)) (hy : z.im ≤ 0) :
    ‖(∫ s : ℝ in 0..v.re-1, saddleWeight t (-z) ((s : ℂ)-(v.im : ℂ)*Complex.I))/
      (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤
      4224*Real.sqrt K*(t*w.re^3)*Real.exp (-(t*w.re^3)/8) := by
  have h := reflected_compact_bound t K c₀ w v ht hK hr hi hn hcenter hs hE hv z hz hy
  have hg := corrected_geometry t K c₀ w v ht hK hr hi hn hcenter hs hE hv
  have hd : ‖v-w‖ ≤ 1/2 := hv.trans ((div_le_iff₀ (by linarith : 0 < K)).mpr (by linarith))
  have hc := (Complex.abs_re_le_norm (v-w)).trans hd
  simp only [Complex.sub_re] at hc
  have hva : w.re ≤ 2*v.re := by linarith [(abs_le.mp hc).1]
  have hcube := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith : 0 ≤ w.re) hva 3)
    (show 0 ≤ t by linarith)
  have hpoly : 5*v.re+3 ≤ v.re^3 := by
    have hsq : 4096 ≤ v.re^2 := by nlinarith [hg.1]
    have hcu := mul_le_mul_of_nonneg_right hsq (by linarith [hg.1] : 0 ≤ v.re)
    nlinarith [hg.1]
  have htime : v.re^3 ≤ t*v.re^3 := by nlinarith [pow_nonneg (by linarith [hg.1] : 0 ≤ v.re) 3]
  have hexp : 5*v.re+3-2*t*v.re^3 ≤ -(t*w.re^3)/8 := by nlinarith
  have hQ : v.re-1 ≤ t*w.re^3 := by
    have hh : w.re ≤ w.re^3 := by
      have hsq : 1 ≤ w.re^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hsq (by linarith : 0 ≤ w.re)]
    have htcu : w.re^3 ≤ t*w.re^3 := by nlinarith [pow_nonneg (by linarith : 0 ≤ w.re) 3]
    linarith [(abs_le.mp hc).2]
  let W := saddleWeight t z v
  let G := ∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)
  let L := ∫ s : ℝ in 0..v.re-1, saddleWeight t (-z) ((s : ℂ)-(v.im : ℂ)*Complex.I)
  let B := 528*(t*w.re^3)*Real.exp (-(t*w.re^3)/8)
  have hnum : ‖L‖ ≤ ‖W‖*B := by
    apply h.trans
    have hm := mul_le_mul hQ (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le
      (show 0 ≤ t*w.re^3 by positivity)
    have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ 528*‖W‖ by positivity)
    dsimp [L,W,B] at *
    nlinarith
  have hnormal := gaussian_normalization_lower t K c₀ w v ht hK (by linarith) hi hn hcenter hs hE hv
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

theorem reflected_outer_mass_bound (z : ℂ) (hz : complexSlope t v= -(Complex.I*z)) (hy : z.im ≤ 0) :
    IntegrableOn (fun s : ℝ => saddleWeight t (-z) (conj v+(s : ℂ))) (Ioi (-1)) ∧
      ‖∫ s : ℝ in Ioi (-1), saddleWeight t (-z) (conj v+(s : ℂ))‖ ≤
        3000*‖saddleWeight t z v‖*Real.exp (2*z.im*(v.re-1))*Real.sqrt (Real.pi/(t*w.re^3/4096)) := by
  have hg := corrected_geometry t K c₀ w v ht hK hr hi hn hcenter hs hE hv
  have hcont : Continuous (fun s : ℝ => saddleWeight t (-z) (conj v+(s : ℂ))) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    have hq : |(conj v+(s : ℂ)).im| < Real.pi/8 := by simpa using hg.2.1
    exact ContinuousAt.comp (g := saddleWeight t (-z)) (f := fun s : ℝ => conj v+(s : ℂ))
      (weight_analyticAt t (-z) (conj v+(s : ℂ)) hq).continuousAt (by fun_prop)
  let A := 3000*‖saddleWeight t z v‖*Real.exp (2*z.im*(v.re-1))
  let b := t*w.re^3/4096
  have hb : 0 < b := by dsimp [b]; positivity
  have hbound : ∀ s : ℝ, -1 ≤ s →
      ‖saddleWeight t (-z) (conj v+(s : ℂ))‖ ≤ A*Real.exp (-b*s^2) := by
    intro s hsl
    have hmain := actual_gaussian_mass_envelope t K c₀ w v ht hK hr hi hn hcenter hs hE hv z hz s hsl
    have hm := mul_nonpos_of_nonpos_of_nonneg hy (show 0 ≤ s+1 by linarith)
    have hexp : 2*z.im*(v.re+s) ≤ 2*z.im*(v.re-1) := by nlinarith
    have hconj : conj (v+(s : ℂ))=conj v+(s : ℂ) := by simp
    rw [← hconj, reflected_weight_norm]
    simp only [Complex.add_re, Complex.ofReal_re]
    have hprod := mul_le_mul hmain (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (by positivity)
    exact hprod.trans_eq (by dsimp [A,b]; ring)
  have hmajor : Integrable (fun s : ℝ => A*Real.exp (-b*s^2)) :=
    (integrable_exp_neg_mul_sq hb).const_mul A
  have hpoint : ∀ᵐ s : ℝ ∂volume.restrict (Ioi (-1)),
      ‖saddleWeight t (-z) (conj v+(s : ℂ))‖ ≤ A*Real.exp (-b*s^2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs1
    exact hbound s hs1.le
  refine ⟨hmajor.integrableOn.mono' hcont.aestronglyMeasurable hpoint, ?_⟩
  have hnorm := norm_integral_le_of_norm_le hmajor.integrableOn hpoint
  have hwhole := setIntegral_le_integral (s := Ioi (-1)) hmajor
    (Eventually.of_forall (fun s : ℝ => (show 0 ≤ A*Real.exp (-b*s^2) from by dsimp [A]; positivity)))
  apply hnorm.trans (hwhole.trans_eq ?_)
  rw [integral_const_mul, integral_gaussian]

theorem relative_reflected_outer_bound (C : ℝ) (hC : 0 < C) (hscale : K ≤ C*(t*w.re^3))
    (z : ℂ) (hz : complexSlope t v= -(Complex.I*z)) (hy : z.im ≤ 0) :
    ‖(∫ s : ℝ in Ioi (-1), saddleWeight t (-z) (conj v+(s : ℂ)))/
      (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤
      3072000*Real.sqrt C*Real.exp (2*z.im*(v.re-1)) := by
  have hmass := (reflected_outer_mass_bound t K c₀ w v ht hK hr hi hn hcenter hs hE hv z hz hy).2
  have hQ : 0 < t*w.re^3 := by positivity
  have hroot : Real.sqrt K*Real.sqrt (Real.pi/(t*w.re^3/4096)) ≤ 128*Real.sqrt C := by
    have hKroot := Real.sqrt_le_sqrt hscale
    rw [Real.sqrt_mul hC.le] at hKroot
    have harg : Real.pi/(t*w.re^3/4096)=4096*Real.pi/(t*w.re^3) := by ring
    have hprod : Real.sqrt (t*w.re^3)*Real.sqrt (Real.pi/(t*w.re^3/4096))=Real.sqrt (4096*Real.pi) := by
      rw [← Real.sqrt_mul hQ.le, harg]
      congr 1
      field_simp
    have hpi : Real.sqrt (4096*Real.pi) ≤ 128 := by
      apply (Real.sqrt_le_iff).mpr
      constructor <;> nlinarith [Real.pi_lt_four]
    have hm := mul_le_mul_of_nonneg_right hKroot (Real.sqrt_nonneg (Real.pi/(t*w.re^3/4096)))
    rw [mul_assoc, hprod] at hm
    have hmC := mul_le_mul_of_nonneg_left hpi (Real.sqrt_nonneg C)
    nlinarith
  let W := saddleWeight t z v
  let G := ∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)
  let L := ∫ s : ℝ in Ioi (-1), saddleWeight t (-z) (conj v+(s : ℂ))
  let B := 3000*Real.exp (2*z.im*(v.re-1))*Real.sqrt (Real.pi/(t*w.re^3/4096))
  have hnum : ‖L‖ ≤ ‖W‖*B := hmass.trans_eq (by dsimp [W,B]; ring)
  have hnormal := gaussian_normalization_lower t K c₀ w v ht hK (by linarith) hi hn hcenter hs hE hv
  change 1 ≤ 8*Real.sqrt K*‖G‖ at hnormal
  have hG : G ≠ 0 := by intro h; norm_num [h] at hnormal
  have hg := corrected_geometry t K c₀ w v ht hK hr hi hn hcenter hs hE hv
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

theorem reflected_horizontal_split (z : ℂ) (hz : complexSlope t v= -(Complex.I*z)) (hy : z.im ≤ 0) :
    (∫ s : ℝ in Ioi 0, saddleWeight t (-z) ((s : ℂ)-(v.im : ℂ)*Complex.I))=
      (∫ s : ℝ in 0..v.re-1, saddleWeight t (-z) ((s : ℂ)-(v.im : ℂ)*Complex.I))+
      (∫ s : ℝ in Ioi (-1), saddleWeight t (-z) (conj v+(s : ℂ))) := by
  have hg := corrected_geometry t K c₀ w v ht hK hr hi hn hcenter hs hE hv
  have hmass := reflected_outer_mass_bound t K c₀ w v ht hK hr hi hn hcenter hs hE hv z hz hy
  have hsplit := RiemannQuarticFarHalfline.horizontal_decomposition t (-z) (conj v)
    (by simpa using hg.2.1) (-1) hmass.1
  simp only [Complex.conj_re, Complex.conj_im, Complex.ofReal_neg, neg_mul, neg_neg,
    ← sub_eq_add_neg] at hsplit
  have hrev : (∫ s : ℝ in (1 : ℝ)..(-1), saddleWeight t (-z) (conj v+(s : ℂ)))=
      -(∫ s : ℝ in (-1 : ℝ)..1, saddleWeight t (-z) (conj v+(s : ℂ))) :=
    intervalIntegral.integral_symm (-1) 1
  linear_combination hsplit+hrev

theorem reflected_outer_cutoff_bound (C : ℝ) (hC : 0 < C) (hscale : K ≤ C*(t*w.re^3))
    (z : ℂ) (hz : complexSlope t v= -(Complex.I*z))
    (hthreshold : z.im ≤ -reflectionCutoff C/w.re) :
    ‖(∫ s : ℝ in Ioi (-1), saddleWeight t (-z) (conj v+(s : ℂ)))/
      (saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)))‖ ≤ 1/8 := by
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
  apply (relative_reflected_outer_bound t K c₀ w v ht hK hr hi hn hcenter hs hE hv C hC hscale z hz hy).trans
  apply (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)).trans
  exact reflectionCutoff_small C hC

end Scaled

theorem eventually_uniform_nonzero_lower (C : ℝ) (hC : 0 < C) :
    ∀ᶠ Q : ℝ in atTop, ∀ (t K : ℝ) (c₀ w v z : ℂ),
      1 ≤ t → 8 ≤ K → 120020 ≤ w.re → |w.im| ≤ 1/2 → ‖w‖ ≤ 2*w.re → c₀.im ≤ 1 →
      modelDerivative t w= -(Complex.I*c₀) → ‖Complex.exp (4*w)‖ ≤ K → ‖v-w‖ ≤ 1/K →
      complexSlope t v= -(Complex.I*z) → Q=t*w.re^3 → K ≤ C*Q →
      z.im ≤ -reflectionCutoff C/w.re → RiemannQuarticFlow.flow t z ≠ 0 := by
  filter_upwards [eventually_uniform_horizontal_error C (1/4) hC (by norm_num),
    eventually_ge_atTop (1 : ℝ),
    (compact_budget_tendsto_zero C).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/8))]
    with Q hmain hQ hcompact
  intro t K c₀ w v z ht hK hr hi hn hcenter hs hE hv hstat hQid hscale hthreshold hzero
  have ha : 0 < w.re := by linarith
  have hy : z.im ≤ 0 := hthreshold.trans (div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (reflectionCutoff_pos C hC).le) ha.le)
  have hM := hmain t K c₀ w v z ht hK hr hi hn hcenter hs hE hv hstat (by linarith) hQid hscale
  have hCpt := relative_reflected_compact_bound t K c₀ w v ht hK hr hi hn hcenter hs hE hv z hstat hy
  rw [← hQid] at hCpt
  have hroot : Real.sqrt K ≤ Real.sqrt C*Q := by
    have hh : Real.sqrt Q ≤ Q := by nlinarith [Real.sq_sqrt (show 0 ≤ Q by linarith), Real.sqrt_nonneg Q]
    have hm := mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg C)
    have hk := Real.sqrt_le_sqrt hscale
    rw [Real.sqrt_mul hC.le] at hk
    linarith
  have hmul := mul_le_mul_of_nonneg_right hroot (show 0 ≤ 4224*Q*Real.exp (-Q/8) by positivity)
  let D := saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2))
  let M := ∫ s : ℝ in Ioi 0, saddleWeight t z ((s : ℂ)+(v.im : ℂ)*Complex.I)
  let O := ∫ s : ℝ in Ioi 0, saddleWeight t (-z) ((s : ℂ)-(v.im : ℂ)*Complex.I)
  let B := ∫ s : ℝ in 0..v.re-1, saddleWeight t (-z) ((s : ℂ)-(v.im : ℂ)*Complex.I)
  let T := ∫ s : ℝ in Ioi (-1), saddleWeight t (-z) (conj v+(s : ℂ))
  have hB : ‖B/D‖ < (1/8 : ℝ) := by
    change ‖B/D‖ ≤ _ at hCpt
    nlinarith
  have hT := reflected_outer_cutoff_bound t K c₀ w v ht hK hr hi hn hcenter hs hE hv C hC
    (by simpa only [hQid] using hscale) z hstat hthreshold
  change ‖T/D‖ ≤ (1/8 : ℝ) at hT
  have hsplit := reflected_horizontal_split t K c₀ w v ht hK hr hi hn hcenter hs hE hv z hstat hy
  change O=B+T at hsplit
  have hO : ‖O/D‖ ≤ (1/4 : ℝ) := by
    rw [hsplit, add_div]
    exact (norm_add_le _ _).trans (by linarith)
  have hg := corrected_geometry t K c₀ w v ht hK hr hi hn hcenter hs hE hv
  have hf := flow_eq_paired_horizontal t z v.im hg.2.1
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
    ∀ᶠ t : ℝ in atTop, ∀ u : ℝ, 65536*(M+7) ≤ u → RiemannQuarticSaddleTimes.phaseSlope t u=0 →
      ∀ z : ℂ, ‖z‖ ≤ M*RiemannQuarticTransitionSaddle.realScale u →
        z.im ≤ -(2*reflectionCutoff (128*(M+8)))/u → RiemannQuarticFlow.flow t z ≠ 0 := by
  let C := 128*(M+8)
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨U,hU⟩ := eventually_atTop.1 (eventually_uniform_nonzero_lower C hC)
  filter_upwards [eventually_ge_atTop (max U 1)] with t htU
  intro u hu hs z hz hy
  have ht : 1 ≤ t := (le_max_right U 1).trans htU
  have hu0 : 0 < u := by linarith
  have hL := reflectionCutoff_pos C hC
  have hy0 : z.im ≤ 0 := hy.trans (div_nonpos_of_nonpos_of_nonneg (by change -(2*reflectionCutoff C) ≤ 0; linarith) hu0.le)
  obtain ⟨w,hw,_⟩ := RiemannQuarticTransitionSaddle.existsUnique_transition_model_saddle
    t u M z ht hM hu hs (by linarith) hz
  have hd := transition_scale_data t u M z w ht hM hu hs (by linarith) hz hw.1 hw.2
  let K := (M+8)*RiemannQuarticTransitionSaddle.realScale u
  have hK0 : 0 < K := by dsimp [K]; positivity [RiemannQuarticTransitionSaddle.realScale_pos u]
  have hwpos : 0 < w.re := by linarith [hd.2.1]
  obtain ⟨v,hv,_⟩ := actual_scaled_frequency_disk t K z w z ht hd.1 hd.2.1 hd.2.2.1
    hd.2.2.2.1 (by linarith) hw.2 hd.2.2.2.2.1 hd.2.2.2.2.2 (by simp; positivity)
  have hvdist : ‖v-w‖ ≤ 1/K := by simpa only [mem_closedBall, dist_eq_norm] using hv.1
  have hg := RiemannQuarticTransitionSaddle.transition_model_geometry t u M z w ht hM hu hs (by linarith) hz hw.1 hw.2
  have hscale : K ≤ C*(t*w.re^3) := moving_scale_ratio_bound t u M w ht hM hu hs hg.1
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
  have hQ : U ≤ t*w.re^3 := by
    have hp : 1 ≤ w.re^3 := one_le_pow₀ (by linarith : 1 ≤ w.re)
    have hh := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ t)
    linarith [(le_max_left U 1).trans htU]
  exact hU (t*w.re^3) hQ t K z w v z ht hd.1 hlarge hd.2.2.1 hd.2.2.2.1
    (by linarith) hw.2 hd.2.2.2.2.1 hvdist hv.2 rfl hscale hthreshold

theorem bounded_ratio_zeros_shrinking_strip (M : ℝ) (hM : 0 ≤ M) :
    ∃ A : ℝ, 0 < A ∧ ∀ R : ℝ, 0 ≤ R →
      ∀ᶠ t : ℝ in atTop, ∃ u : ℝ, R ≤ u ∧ 65536*(M+7) ≤ u ∧
        RiemannQuarticSaddleTimes.phaseSlope t u=0 ∧
        ∀ z : ℂ, ‖z‖ ≤ M*RiemannQuarticTransitionSaddle.realScale u →
          RiemannQuarticFlow.flow t z=0 → |z.im| < A/u := by
  let A := 2*reflectionCutoff (128*(M+8))
  have hA : 0 < A := by
    dsimp [A]
    have h := reflectionCutoff_pos (128*(M+8)) (by positivity)
    linarith
  refine ⟨A,hA,?_⟩
  intro R hR
  filter_upwards [eventually_actual_nonzero_lower M hM,
    RiemannQuarticRealSaddle.maxima_escape (max R (65536*(M+7))) (by positivity)] with t hlow hescape
  obtain ⟨u,hu,hm⟩ := RiemannQuarticRealSaddle.exists_global_max t
  have hlarge := (hescape u hu hm).le
  have hRu : R ≤ u := (le_max_left _ _).trans hlarge
  have huM : 65536*(M+7) ≤ u := (le_max_right _ _).trans hlarge
  have hu0 : 0 < u := by linarith
  have hs := RiemannQuarticRealSaddle.max_real_stationary t u hu0 hm
  rw [← (RiemannQuarticRealSaddle.kernel_hasDerivAt u).deriv] at hs
  refine ⟨u,hRu,huM,hs,?_⟩
  intro z hz hzero
  have hlo : -A/u < z.im := lt_of_not_ge (fun h => hlow u huM hs z hz h hzero)
  have hconj : RiemannQuarticFlow.flow t (conj z)=0 := by
    rw [RiemannQuarticNormalizedAnalytic.flow_conj, hzero]
    simp
  have hhi : -A/u < (conj z).im := lt_of_not_ge (fun h =>
    hlow u huM hs (conj z) (by simpa using hz) h hconj)
  simp only [Complex.conj_im] at hhi
  rw [neg_div] at hlo hhi
  exact abs_lt.mpr ⟨hlo,by linarith⟩

end OperatorDerivativeRewrite.Foundation.RiemannQuarticTransitionReflection
