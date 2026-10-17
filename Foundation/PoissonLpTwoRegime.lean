import Foundation.StableLevyAnnuli
import Foundation.PoissonCharlierLadder
import Foundation.BanachLpDualityFour

/-! Exact fourth moments and two-regime norm bounds for actual compensated Poisson counts. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.PoissonLpTwoRegime
set_option backward.isDefEq.respectTransparency false
open PoissonDifferenceCore PoissonDifferenceOperators PoissonPolynomialExamples
open PoissonMoments PoissonLpLowerObstruction PoissonCharlierLadder PoissonCoordinateEvaluation

local instance : Fact (1 ≤ exponent) := ⟨by
  simpa [exponent] using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ 4/3 by norm_num)⟩
local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance : ENNReal.HolderConjugate exponent 4 := by
  apply ENNReal.HolderConjugate.of_toReal
  norm_num [exponent,Real.holderConjugate_iff]

theorem square_charlier_decomposition (r : ℝ≥0) (hr : 0 < r) :
    centeredCountSqL2 r hr=scalar r hr 2+scalar r hr 1+(r : ℝ) • scalar r hr 0 := by
  apply Lp.ext
  filter_upwards [] with k
  rw [centeredCountSqL2_apply,scalar_add_apply r hr,scalar_add_apply r hr,
    scalar_smul_apply r hr,scalar_apply,scalar_apply,scalar_apply]
  simp only [value_succ,value_zero]
  unfold centeredCount
  ring

theorem square_L2_energy (r : ℝ≥0) (hr : 0 < r) :
    ‖centeredCountSqL2 r hr‖^2=3*(r : ℝ)^2+r := by
  rw [← real_inner_self_eq_norm_sq,square_charlier_decomposition]
  simp only [inner_add_left,inner_add_right,real_inner_smul_left,inner_smul_right,scalar_inner]
  norm_num <;> ring

theorem fourth_moment (r : ℝ≥0) (hr : 0 < r) :
    (∫ k, centeredCount r k^4 ∂poissonLaw r)=3*(r : ℝ)^2+r := by
  calc
    _ = ∫ k, ‖centeredCountSqL2 r hr k‖^2 ∂poissonLaw r := by
      apply integral_congr_ae
      exact ae_of_all _ (fun k => by
        change centeredCount r k^4=‖centeredCountSqL2 r hr k‖^2
        rw [centeredCountSqL2_apply,Real.norm_eq_abs,sq_abs]
        ring)
    _ = ‖centeredCountSqL2 r hr‖^2 := (BochnerL2Dominated.norm_sq_integral _).symm
    _ = _ := square_L2_energy r hr

theorem count_memLp_four (r : ℝ≥0) (hr : 0 < r) :
    MemLp (centeredCount r) 4 (poissonLaw r) := by
  apply (memLp_norm_rpow_iff (p := 4) (q := 2)
    (centeredCount_memLp r hr).aestronglyMeasurable (by norm_num) (by norm_num)).mp
  have h42 : (4 : ℝ≥0∞)/2=2 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_div]
  simpa [h42,Real.rpow_two,Real.norm_eq_abs,sq_abs] using centeredCount_sq_memLp r hr

def outputFour (r : ℝ≥0) (hr : 0 < r) : Lp ℝ 4 (poissonLaw r) :=
  (count_memLp_four r hr).toLp (centeredCount r)

theorem outputFour_ae (r : ℝ≥0) (hr : 0 < r) :
    outputFour r hr =ᵐ[poissonLaw r] centeredCount r := MemLp.coeFn_toLp _

theorem outputFour_energy (r : ℝ≥0) (hr : 0 < r) :
    ‖outputFour r hr‖^4=3*(r : ℝ)^2+r := by
  rw [← BanachLpDualityFour.quartic_integral_eq_norm]
  have he : (∫ k, outputFour r hr k^4 ∂poissonLaw r)=
      ∫ k, centeredCount r k^4 ∂poissonLaw r := by
    apply integral_congr_ae
    filter_upwards [outputFour_ae r hr] with k hk
    rw [hk]
  rw [he,fourth_moment r hr]

theorem output_ae (r : ℝ≥0) (hr : 0 < r) :
    output r hr =ᵐ[poissonLaw r] centeredCount r := MemLp.coeFn_toLp _

theorem holder_lower (r : ℝ≥0) (hr : 0 < r) :
    (r : ℝ) ≤ ‖output r hr‖*‖outputFour r hr‖ := by
  let T := BanachLpAdjoint.boundedBanachDerivative
    (ContinuousLinearMap.id ℝ (Lp ℝ 4 (poissonLaw r))) (output r hr)
  have he : T (outputFour r hr)=(r : ℝ) := by
    dsimp only [T]
    rw [BanachLpAdjoint.boundedBanachDerivative_apply]
    have h : (∫ k, output r hr k*outputFour r hr k ∂poissonLaw r)=
        ∫ k, centeredCount r k^2 ∂poissonLaw r := by
      apply integral_congr_ae
      filter_upwards [output_ae r hr,outputFour_ae r hr] with k hk h4
      rw [hk,h4]
      ring
    simp only [ContinuousLinearMap.id_apply]
    rw [h,centered_variance r hr]
  have hn : ‖T‖ ≤ ‖output r hr‖ := by
    have h := BanachLpAdjoint.boundedBanachDerivative_norm_le
      (ContinuousLinearMap.id ℝ (Lp ℝ 4 (poissonLaw r))) (output r hr)
    apply h.trans
    calc
      _ ≤ ‖output r hr‖*1 := mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
      _ = _ := mul_one _
  have h := (T.le_opNorm (outputFour r hr)).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  rw [he,Real.norm_eq_abs,abs_of_nonneg r.coe_nonneg] at h
  exact h

theorem norm_four_lower_polynomial (r : ℝ≥0) (hr : 0 < r) :
    (r : ℝ)^4 ≤ ‖output r hr‖^4*(3*(r : ℝ)^2+r) := by
  have h := pow_le_pow_left₀ r.coe_nonneg (holder_lower r hr) 4
  rw [mul_pow,outputFour_energy r hr] at h
  exact h

theorem absolute_first_moment_bound (r : ℝ≥0) (hr : 0 < r) :
    (∫ k, |centeredCount r k| ∂poissonLaw r) ≤ 2*(r : ℝ) := by
  have hn : Integrable (fun k : ℕ => (k : ℝ)) (poissonLaw r) :=
    ((by simpa only [pow_one] using poisson_power_memLp_two r hr 1) :
      MemLp (fun k : ℕ => (k : ℝ)) 2 (poissonLaw r)).integrable (by norm_num)
  have hi := (centeredCount_memLp r hr).integrable (by norm_num)
  have hb (k : ℕ) : |centeredCount r k| ≤ (k : ℝ)+r := by
    simpa only [centeredCount,Real.norm_eq_abs,abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) by positivity),
      abs_of_nonneg r.coe_nonneg] using norm_sub_le (k : ℝ) (r : ℝ)
  have h := integral_mono_ae hi.abs (hn.add (integrable_const (r : ℝ))) (ae_of_all _ hb)
  simp only [Pi.add_apply] at h
  rw [integral_add hn (integrable_const _),integral_poisson_count r hr] at h
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul,two_mul] using h

local instance : ENNReal.HolderTriple 2 4 exponent := by
  apply ENNReal.HolderTriple.of_toReal
  norm_num [exponent,Real.holderTriple_iff]

def sqrtAbs (r : ℝ≥0) (k : ℕ) : ℝ := Real.sqrt |centeredCount r k|

theorem sqrtAbs_sq (r : ℝ≥0) (k : ℕ) : sqrtAbs r k^2=|centeredCount r k| :=
  Real.sq_sqrt (abs_nonneg _)

theorem sqrtAbs_memLp_two (r : ℝ≥0) (hr : 0 < r) : MemLp (sqrtAbs r) 2 (poissonLaw r) := by
  have h := ((centeredCount_memLp r hr).mono_exponent (show (1 : ℝ≥0∞) ≤ 2 by norm_num)).norm_rpow_div
    (ENNReal.ofReal (1/2 : ℝ))
  have he : (1 : ℝ≥0∞)/ENNReal.ofReal (1/2 : ℝ)=2 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_div]
  rw [he] at h
  change MemLp (fun k => Real.sqrt |centeredCount r k|) 2 (poissonLaw r)
  simpa [Real.sqrt_eq_rpow,Real.norm_eq_abs] using h

theorem sqrtAbs_memLp_four (r : ℝ≥0) (hr : 0 < r) : MemLp (sqrtAbs r) 4 (poissonLaw r) := by
  have h := (centeredCount_memLp r hr).norm_rpow_div (ENNReal.ofReal (1/2 : ℝ))
  have he : (2 : ℝ≥0∞)/ENNReal.ofReal (1/2 : ℝ)=4 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_div]
  rw [he] at h
  change MemLp (fun k => Real.sqrt |centeredCount r k|) 4 (poissonLaw r)
  simpa [Real.sqrt_eq_rpow,Real.norm_eq_abs] using h

def sqrtTwo (r : ℝ≥0) (hr : 0 < r) : Lp ℝ 2 (poissonLaw r) := (sqrtAbs_memLp_two r hr).toLp (sqrtAbs r)
def sqrtFour (r : ℝ≥0) (hr : 0 < r) : Lp ℝ 4 (poissonLaw r) := (sqrtAbs_memLp_four r hr).toLp (sqrtAbs r)

theorem sqrtTwo_ae (r : ℝ≥0) (hr : 0 < r) : sqrtTwo r hr =ᵐ[poissonLaw r] sqrtAbs r := MemLp.coeFn_toLp _
theorem sqrtFour_ae (r : ℝ≥0) (hr : 0 < r) : sqrtFour r hr =ᵐ[poissonLaw r] sqrtAbs r := MemLp.coeFn_toLp _

theorem sqrtTwo_energy_bound (r : ℝ≥0) (hr : 0 < r) : ‖sqrtTwo r hr‖^2 ≤ 2*(r : ℝ) := by
  rw [BochnerL2Dominated.norm_sq_integral]
  have he : (∫ k, ‖sqrtTwo r hr k‖^2 ∂poissonLaw r)=∫ k, |centeredCount r k| ∂poissonLaw r := by
    apply integral_congr_ae
    filter_upwards [sqrtTwo_ae r hr] with k hk
    rw [hk,Real.norm_eq_abs,sq_abs,sqrtAbs_sq]
  rw [he]
  exact absolute_first_moment_bound r hr

theorem sqrtFour_energy (r : ℝ≥0) (hr : 0 < r) : ‖sqrtFour r hr‖^4=(r : ℝ) := by
  rw [← BanachLpDualityFour.quartic_integral_eq_norm]
  have he : (∫ k, sqrtFour r hr k^4 ∂poissonLaw r)=∫ k, centeredCount r k^2 ∂poissonLaw r := by
    apply integral_congr_ae
    filter_upwards [sqrtFour_ae r hr] with k hk
    rw [hk]
    calc
      _ = (sqrtAbs r k^2)^2 := by ring
      _ = _ := by rw [sqrtAbs_sq,sq_abs]
  rw [he,centered_variance r hr]

theorem sqrt_product_bound (r : ℝ≥0) (hr : 0 < r) :
    ‖output r hr‖ ≤ ‖sqrtTwo r hr‖*‖sqrtFour r hr‖ := by
  have he : (sqrtTwo r hr • sqrtFour r hr : Lp ℝ exponent (poissonLaw r)) =ᵐ[poissonLaw r]
      fun k => ‖centeredCount r k‖ := by
    filter_upwards [Lp.coeFn_lpSMul (r := exponent) (sqrtTwo r hr) (sqrtFour r hr),sqrtTwo_ae r hr,sqrtFour_ae r hr]
      with k hp h2 h4
    rw [hp]
    change sqrtTwo r hr k*sqrtFour r hr k=‖centeredCount r k‖
    rw [h2,h4]
    rw [← pow_two,sqrtAbs_sq,Real.norm_eq_abs]
  have hn : ‖output r hr‖=‖(sqrtTwo r hr • sqrtFour r hr : Lp ℝ exponent (poissonLaw r))‖ := by
    rw [output,Lp.norm_toLp,Lp.norm_def,eLpNorm_congr_ae he,
      eLpNorm_norm _ (centeredCount_memLp r hr).aestronglyMeasurable]
  rw [hn]
  exact Lp.norm_smul_le _ _

theorem norm_four_upper_cubic (r : ℝ≥0) (hr : 0 < r) : ‖output r hr‖^4 ≤ 4*(r : ℝ)^3 := by
  have h := pow_le_pow_left₀ (norm_nonneg (output r hr)) (sqrt_product_bound r hr) 4
  rw [mul_pow,sqrtFour_energy r hr] at h
  have ha := sqrtTwo_energy_bound r hr
  have hs : ‖sqrtTwo r hr‖^4 ≤ 4*(r : ℝ)^2 := by
    nlinarith [sq_nonneg (‖sqrtTwo r hr‖^2-2*(r : ℝ))]
  nlinarith [mul_nonneg r.coe_nonneg (sub_nonneg.mpr hs)]

theorem norm_four_upper_quadratic (r : ℝ≥0) (hr : 0 < r) : ‖output r hr‖^4 ≤ (r : ℝ)^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (output r hr)) (output_norm_le_sqrt r hr) 4
  rw [show Real.sqrt (r : ℝ)^4=(Real.sqrt (r : ℝ)^2)^2 by ring,Real.sq_sqrt r.coe_nonneg] at h
  exact h

theorem small_rate_lower (r : ℝ≥0) (hr : 0 < r) (hr1 : (r : ℝ) ≤ 1) :
    (r : ℝ)^3 ≤ 4*‖output r hr‖^4 := by
  have h := norm_four_lower_polynomial r hr
  have hm : 3*(r : ℝ)^2+r ≤ 4*r := by nlinarith [r.coe_nonneg]
  have hb : (r : ℝ)^4 ≤ (4*‖output r hr‖^4)*(r : ℝ) := by
    nlinarith [mul_nonneg (pow_nonneg (norm_nonneg (output r hr)) 4) (sub_nonneg.mpr hm)]
  apply (mul_le_mul_iff_left₀ (show (0 : ℝ)<r by exact_mod_cast hr)).mp
  nlinarith [hb]

theorem large_rate_lower (r : ℝ≥0) (hr : 0 < r) (hr1 : (1 : ℝ) ≤ r) :
    (r : ℝ)^2 ≤ 4*‖output r hr‖^4 := by
  have h := norm_four_lower_polynomial r hr
  have hm : 3*(r : ℝ)^2+r ≤ 4*(r : ℝ)^2 := by nlinarith [r.coe_nonneg]
  have hb : (r : ℝ)^4 ≤ (4*‖output r hr‖^4)*(r : ℝ)^2 := by
    nlinarith [mul_nonneg (pow_nonneg (norm_nonneg (output r hr)) 4) (sub_nonneg.mpr hm)]
  apply (mul_le_mul_iff_left₀ (show (0 : ℝ)<(r : ℝ)^2 by positivity)).mp
  nlinarith [hb]

theorem two_regime_fourth_bounds (r : ℝ≥0) (hr : 0 < r) :
    (1/4 : ℝ)*min ((r : ℝ)^2) ((r : ℝ)^3) ≤ ‖output r hr‖^4 ∧
      ‖output r hr‖^4 ≤ 4*min ((r : ℝ)^2) ((r : ℝ)^3) := by
  by_cases hs : (r : ℝ) ≤ 1
  · have hm : (r : ℝ)^3 ≤ (r : ℝ)^2 := by
      nlinarith [mul_nonneg (sq_nonneg (r : ℝ)) (sub_nonneg.mpr hs)]
    rw [min_eq_right hm]
    constructor
    · nlinarith [small_rate_lower r hr hs]
    · exact norm_four_upper_cubic r hr
  · have hr1 : (1 : ℝ) ≤ r := le_of_lt (lt_of_not_ge hs)
    have hm : (r : ℝ)^2 ≤ (r : ℝ)^3 := by
      nlinarith [mul_nonneg (sq_nonneg (r : ℝ)) (sub_nonneg.mpr hr1)]
    rw [min_eq_left hm]
    constructor
    · nlinarith [large_rate_lower r hr hr1]
    · nlinarith [norm_four_upper_quadratic r hr,sq_nonneg (r : ℝ)]

def scale (r : ℝ≥0) : ℝ := min (Real.sqrt (r : ℝ)) ((r : ℝ)^(3/4 : ℝ))

theorem scale_nonneg (r : ℝ≥0) : 0 ≤ scale r :=
  le_min (Real.sqrt_nonneg _) (Real.rpow_nonneg r.coe_nonneg _)

theorem scale_fourth (r : ℝ≥0) : scale r^4=min ((r : ℝ)^2) ((r : ℝ)^3) := by
  have hs : Real.sqrt (r : ℝ)^4=(r : ℝ)^2 := by
    rw [show Real.sqrt (r : ℝ)^4=(Real.sqrt (r : ℝ)^2)^2 by ring,Real.sq_sqrt r.coe_nonneg]
  have hp : ((r : ℝ)^(3/4 : ℝ))^4=(r : ℝ)^3 := by
    rw [← Real.rpow_mul_natCast r.coe_nonneg]
    norm_num [Real.rpow_natCast]
  unfold scale
  by_cases h : Real.sqrt (r : ℝ) ≤ (r : ℝ)^(3/4 : ℝ)
  · rw [min_eq_left h,hs]
    have hm := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 4
    rw [hs,hp] at hm
    rw [min_eq_left hm]
  · have h' := le_of_lt (lt_of_not_ge h)
    rw [min_eq_right h',hp]
    have hm := pow_le_pow_left₀ (Real.rpow_nonneg r.coe_nonneg _) h' 4
    rw [hs,hp] at hm
    rw [min_eq_right hm]

theorem two_regime_bounds (r : ℝ≥0) (hr : 0 < r) :
    scale r/Real.sqrt 2 ≤ ‖output r hr‖ ∧ ‖output r hr‖ ≤ Real.sqrt 2*scale r := by
  have hb := two_regime_fourth_bounds r hr
  have h24 : Real.sqrt 2^4=(4 : ℝ) := by
    rw [show Real.sqrt 2^4=(Real.sqrt 2^2)^2 by ring,Real.sq_sqrt (by norm_num)]
    norm_num
  constructor
  · apply (pow_le_pow_iff_left₀ (div_nonneg (scale_nonneg r) (Real.sqrt_nonneg _))
      (norm_nonneg (output r hr)) (by decide : (4 : ℕ) ≠ 0)).mp
    rw [div_pow,h24,scale_fourth]
    nlinarith [hb.1]
  · apply (pow_le_pow_iff_left₀ (norm_nonneg (output r hr))
      (mul_nonneg (Real.sqrt_nonneg _) (scale_nonneg r)) (by decide : (4 : ℕ) ≠ 0)).mp
    rw [mul_pow,h24,scale_fourth]
    exact hb.2

theorem scale_rate {n : ℕ} (hn : 0 < n) : scale (rate n)=(n : ℝ)^2 := by
  have hs : Real.sqrt (rate n : ℝ)=(n : ℝ)^2 := by
    change Real.sqrt ((n : ℝ)^4)=(n : ℝ)^2
    rw [show (n : ℝ)^4=((n : ℝ)^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]
  have hp : ((rate n : ℝ≥0) : ℝ)^(3/4 : ℝ)=(n : ℝ)^3 := by
    rw [← input_norm (rate n),input_norm_rate]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hm : (n : ℝ)^2 ≤ (n : ℝ)^3 := by
    nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) (sub_nonneg.mpr hn1)]
  rw [scale,hs,hp,min_eq_left hm]

theorem rate_output_bounds {n : ℕ} (hn : 0 < n) :
    (n : ℝ)^2/Real.sqrt 2 ≤ ‖output (rate n) (rate_pos hn)‖ ∧
      ‖output (rate n) (rate_pos hn)‖ ≤ (n : ℝ)^2 := by
  have h := (two_regime_bounds (rate n) (rate_pos hn)).1
  rw [scale_rate hn] at h
  exact ⟨h,output_norm_rate hn⟩

theorem rate_ratio_bounds {n : ℕ} (hn : 0 < n) :
    1/(Real.sqrt 2*(n : ℝ)) ≤ ‖output (rate n) (rate_pos hn)‖/‖input (rate n)‖ ∧
      ‖output (rate n) (rate_pos hn)‖/‖input (rate n)‖ ≤ 1/(n : ℝ) := by
  refine ⟨?_,norm_ratio_le hn⟩
  rw [input_norm_rate]
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  apply (le_div_iff₀ (pow_pos hnR 3)).mpr
  calc
    _ = (n : ℝ)^2/Real.sqrt 2 := by field_simp <;> ring
    _ ≤ _ := (rate_output_bounds hn).1

theorem annulus_ratio_bounds {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (c : ℝ) (hc : 0 < c) (N : StableLevyAnnuli.FiniteCountLaws μ c)
    {n : ℕ} (hn : 0 < n) :
    1/(Real.sqrt 2*(n : ℝ)) ≤
      ‖lawOutput (N.count (StableLevyAnnuli.block c n)) (rate n) (rate_pos hn)
        (StableLevyAnnuli.block_count_law c hc N n)‖/
        (eLpNorm ((StableLevyAnnuli.block c n).indicator (fun _ => (1 : ℝ))) exponent
          (StableLevyAnnuli.controlMeasure c)).toReal ∧
    ‖lawOutput (N.count (StableLevyAnnuli.block c n)) (rate n) (rate_pos hn)
        (StableLevyAnnuli.block_count_law c hc N n)‖/
        (eLpNorm ((StableLevyAnnuli.block c n).indicator (fun _ => (1 : ℝ))) exponent
          (StableLevyAnnuli.controlMeasure c)).toReal ≤ 1/(n : ℝ) := by
  rw [lawOutput_norm,StableLevyAnnuli.block_norm c hc n,← input_norm_rate n]
  exact rate_ratio_bounds hn

end OperatorDerivativeRewrite.Foundation.PoissonLpTwoRegime
