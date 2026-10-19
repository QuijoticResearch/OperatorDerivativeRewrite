import Foundation.RiemannQuarticGaussianTail
/-! Actual nearby horizontal tails and fixed-window Gaussian comparison.
For real displacements abs(s)<=1/819200, the actual saddle weight has a
Gaussian norm envelope exp(-3*Q*s^2/4). Both nearby annulus sides are bounded
by Gaussian tails, without imposing the central small-error condition there.
The signed integral on a fixed small window is compared with the full Gaussian
normalization. Actual tails outside that window and global zero control remain
separate obligations. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticLocalTail
open RiemannQuarticSaddleBranch RiemannQuarticSaddleTimes RiemannQuarticFrequencyBranch
open RiemannQuarticSpatialPhase RiemannQuarticGaussianTail

theorem local_real_phase_upper (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/102400)) (hstat : complexSlope t w= -(Complex.I*z))
    (P : ℂ → ℂ) (hP0 : P 0=0)
    (hP : ∀ v ∈ ball (0 : ℂ) (1/102400), HasDerivAt P (complexSlope t (w+v)+Complex.I*z) v)
    (s : ℝ) (hsr : |s| ≤ 1/819200) :
    (P (s : ℂ)).re ≤ -(3/4 : ℝ)*(t*u^3+1)*s^2 := by
  let Q := t*u^3+1
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hv : ‖(s : ℂ)‖ < (1/102400 : ℝ) := by simpa using hsr.trans_lt (by norm_num : (1/819200 : ℝ)<1/102400)
  have hrem := local_phase_quadratic_remainder t u ht hu hs z w hw hstat P hP0 hP (s : ℂ) hv
  simp only [Complex.norm_real,Real.norm_eq_abs] at hrem
  have hc := gaussian_coefficient_lower t u ht hu hs w hw
  simp only [Complex.div_ofNat_re,Complex.neg_re] at hc
  have hquad : (deriv (complexSlope t) w*(s : ℂ)^2/2).re ≤ -Q*s^2 := by
    simp only [Complex.div_ofNat_re,Complex.mul_re,← Complex.ofReal_pow,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,sub_zero]
    have hp := mul_le_mul_of_nonneg_right (by linarith : (deriv (complexSlope t) w).re ≤ -2*Q) (sq_nonneg s)
    nlinarith
  have hp := mul_le_mul_of_nonneg_left hsr (by positivity : 0 ≤ 204800*Q)
  have hcoef : 204800*Q*|s| ≤ Q/4 := by nlinarith
  have hpow : |s|^3=|s| *s^2 := by
    calc
      _ = |s| *|s|^2 := by ring
      _ = _ := by rw [sq_abs]
  have hM : (204800*Q)*|s|^3 ≤ (Q/4)*s^2 := by
    rw [hpow]
    have hm := mul_le_mul_of_nonneg_right hcoef (sq_nonneg s)
    nlinarith
  have hre := Complex.re_le_norm (P (s : ℂ)-deriv (complexSlope t) w*(s : ℂ)^2/2)
  simp only [Complex.sub_re] at hre
  change ‖P (s : ℂ)-deriv (complexSlope t) w*(s : ℂ)^2/2‖ ≤ (204800*Q)*|s|^3 at hrem
  change (P (s : ℂ)).re ≤ -(3/4 : ℝ)*Q*s^2
  linarith

theorem actual_local_gaussian_envelope (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/102400)) (hstat : complexSlope t w= -(Complex.I*z))
    (s : ℝ) (hsr : |s| ≤ 1/819200) :
    ‖saddleWeight t z (w+(s : ℂ))‖ ≤ ‖saddleWeight t z w‖*
      Real.exp (-(3/4 : ℝ)*(t*u^3+1)*s^2) := by
  obtain ⟨P,hP0,hP⟩ := exists_local_phase t u hu z w hw
  have hv : ‖(s : ℂ)‖ < (1/102400 : ℝ) := by simpa using hsr.trans_lt (by norm_num : (1/819200 : ℝ)<1/102400)
  rw [local_weight_eq_exp_phase t u hu z w hw P hP0 hP (s : ℂ) hv,norm_mul,Complex.norm_exp]
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (local_real_phase_upper t u ht hu hs z w hw hstat P hP0 hP s hsr)) (norm_nonneg _)

theorem actual_annulus_side_bound (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/102400)) (hstat : complexSlope t w= -(Complex.I*z))
    (r R σ : ℝ) (hr : 0 < r) (hrR : r ≤ R) (hR : R ≤ 1/819200) (hσ : |σ|=1) :
    ‖∫ s : ℝ in r..R, saddleWeight t z (w+((σ*s : ℝ) : ℂ))‖ ≤
      ‖saddleWeight t z w‖*Real.exp (-(3/4 : ℝ)*(t*u^3+1)*r^2)/
        (2*((3/4 : ℝ)*(t*u^3+1))*r) := by
  let c := (3/4 : ℝ)*(t*u^3+1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hsq : σ^2=1 := by rw [← sq_abs σ,hσ]; norm_num
  have hpoint (s : ℝ) (hsi : s ∈ Ioc r R) :
      ‖saddleWeight t z (w+((σ*s : ℝ) : ℂ))‖ ≤ ‖saddleWeight t z w‖*Real.exp (-c*s^2) := by
    have hsr : |σ*s| ≤ 1/819200 := by rw [abs_mul,hσ,one_mul,abs_of_pos (lt_trans hr hsi.1)]; exact hsi.2.trans hR
    have h := actual_local_gaussian_envelope t u ht hu hs z w hw hstat (σ*s) hsr
    rw [mul_pow,hsq,one_mul] at h
    simpa only [c,neg_mul] using h
  have hg : IntervalIntegrable (fun s : ℝ => ‖saddleWeight t z w‖*Real.exp (-c*s^2)) volume r R :=
    (by fun_prop : Continuous (fun s : ℝ => ‖saddleWeight t z w‖*Real.exp (-c*s^2))).intervalIntegrable r R
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hrR (Eventually.of_forall hpoint) hg
  rw [intervalIntegral.integral_const_mul] at hnorm
  have htrunc : (∫ s : ℝ in r..R, Real.exp (-c*s^2)) ≤ ∫ s : ℝ in Ioi r, Real.exp (-c*s^2) := by
    rw [intervalIntegral.integral_of_le hrR]
    apply setIntegral_mono_set (integrable_exp_neg_mul_sq hc).integrableOn
    · exact Eventually.of_forall fun s => (Real.exp_pos _).le
    · exact Eventually.of_forall fun s hs => hs.1
  have htail := real_tail_bound c r hc hr
  calc
    _ ≤ ‖saddleWeight t z w‖*(∫ s : ℝ in r..R, Real.exp (-c*s^2)) := hnorm
    _ ≤ ‖saddleWeight t z w‖*(Real.exp (-c*r^2)/(2*c*r)) :=
      mul_le_mul_of_nonneg_left (htrunc.trans htail) (norm_nonneg _)
    _ = _ := by simp only [c,neg_mul] <;> ring


theorem fixed_window_gaussian_error (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/102400)) (hstat : complexSlope t w= -(Complex.I*z))
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) (hR : R ≤ 1/819200)
    (hsmall : (204800*(t*u^3+1))*r^3 ≤ 1) :
    ‖(∫ s : ℝ in -R..R, saddleWeight t z (w+(s : ℂ)))-
      saddleWeight t z w*((Real.pi : ℂ)/(-(deriv (complexSlope t) w)/2))^(1/2 : ℂ)‖ ≤
      ‖saddleWeight t z w‖*((819200*(t*u^3+1))*r^4+
        Real.exp (-(t*u^3+1)*r^2)/((t*u^3+1)*r)+
        Real.exp (-((3/4 : ℝ)*(t*u^3+1))*r^2)/(((3/4 : ℝ)*(t*u^3+1))*r)) := by
  let A := saddleWeight t z w
  let f := fun s : ℝ => saddleWeight t z (w+(s : ℂ))
  let G := ((Real.pi : ℂ)/(-(deriv (complexSlope t) w)/2))^(1/2 : ℂ)
  let c := (3/4 : ℝ)*(t*u^3+1)
  let E := Real.exp (-c*r^2)
  have hf := horizontal_weight_continuous t u z w hw
  have hsp1 := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume) (hf.intervalIntegrable (-R) (-r)) (hf.intervalIntegrable (-r) r)
  have hsp2 := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume) (hf.intervalIntegrable (-R) r) (hf.intervalIntegrable r R)
  have hneg := intervalIntegral.integral_comp_neg (f := f) (a := r) (b := R)
  have he : (∫ s : ℝ in -R..R, f s)-A*G=
      ((∫ s : ℝ in -r..r, f s)-A*G)+(∫ s : ℝ in r..R, f s)+(∫ s : ℝ in r..R, f (-s)) := by
    change (∫ s : ℝ in -R..-r, f s)+(∫ s : ℝ in -r..r, f s)=(∫ s : ℝ in -R..r, f s) at hsp1
    change (∫ s : ℝ in -R..r, f s)+(∫ s : ℝ in r..R, f s)=(∫ s : ℝ in -R..R, f s) at hsp2
    linear_combination -hsp1 -hsp2 -hneg
  have hp : ‖∫ s : ℝ in r..R, f s‖ ≤ ‖A‖*(E/(2*c*r)) := by
    have h := actual_annulus_side_bound t u ht hu hs z w hw hstat r R 1 hr hrR hR (by norm_num)
    convert h using 1 <;> simp only [one_mul,c,E,A,f,neg_mul] <;> ring
  have hm : ‖∫ s : ℝ in r..R, f (-s)‖ ≤ ‖A‖*(E/(2*c*r)) := by
    have h := actual_annulus_side_bound t u ht hu hs z w hw hstat r R (-1) hr hrR hR (by norm_num)
    convert h using 1 <;> simp only [neg_one_mul,c,E,A,f,neg_mul] <;> ring
  have hpair : ‖∫ s : ℝ in r..R, f s‖+‖∫ s : ℝ in r..R, f (-s)‖ ≤ ‖A‖*(E/(c*r)) := by
    have hfrac : E/(2*c*r)+E/(2*c*r)=E/(c*r) := by field_simp <;> ring
    calc
      _ ≤ ‖A‖*(E/(2*c*r))+‖A‖*(E/(2*c*r)) := add_le_add hp hm
      _ = _ := by rw [← mul_add,hfrac]
  have hrr : r < 1/102400 := (hrR.trans hR).trans_lt (by norm_num : (1/819200 : ℝ)<1/102400)
  have hcore := local_integral_full_gaussian_error t u ht hu hs z w hw hstat r hr hrr hsmall
  change ‖(∫ s : ℝ in -r..r, f s)-A*G‖ ≤ _ at hcore
  change ‖(∫ s : ℝ in -R..R, f s)-A*G‖ ≤ _
  rw [he]
  have hn := norm_add_le (((∫ s : ℝ in -r..r, f s)-A*G)+(∫ s : ℝ in r..R, f s))
    (∫ s : ℝ in r..R, f (-s))
  have hn2 := norm_add_le ((∫ s : ℝ in -r..r, f s)-A*G) (∫ s : ℝ in r..R, f s)
  change ‖_‖ ≤ ‖A‖*((819200*(t*u^3+1))*r^4+
    Real.exp (-(t*u^3+1)*r^2)/((t*u^3+1)*r)+E/(c*r))
  nlinarith

end OperatorDerivativeRewrite.Foundation.RiemannQuarticLocalTail
