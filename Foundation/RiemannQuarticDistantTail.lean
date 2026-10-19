import Foundation.RiemannQuarticLocalTail
import Foundation.RiemannQuarticShiftedAmplitude
/-! Actual complementary shifted-integrand tails outside a small saddle window.
Cauchy control gives the actual right-boundary slope <=-Q*R, Q=t*u^3+1.
For t>0,u>=2, an actual nearby saddle and Im(z)<=0, the infinite signed
right tail is bounded by norm(A)*exp(-3*Q*R^2/4)/(Q*R). The left segment
from1 to Re(w)-R is bounded by its length times the same boundary envelope.
The compact segment [0,1], relative Gaussian normalization, opposite-frequency
pairing and the global zero problem remain separate obligations. -/
noncomputable section
open Set Metric Complex Filter MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticDistantTail
open RiemannQuarticSaddleBranch RiemannQuarticSaddleTimes RiemannQuarticQuantitativeSaddle
open RiemannQuarticSpatialPhase RiemannQuarticSaddleNeighborhood RiemannQuarticSaddleGeometry
open RiemannQuarticFrequencyBranch RiemannQuarticGaussianTail RiemannQuarticLocalTail
open RiemannQuarticWeightedSlope RiemannQuarticShiftedAmplitude

theorem slope_local_linearization (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/102400)) (R : ℝ) (hR0 : 0 ≤ R) (hR : R ≤ 1/819200) :
    ‖complexSlope t (w+(R : ℂ))-complexSlope t w-deriv (complexSlope t) w*(R : ℂ)‖ ≤
      204800*(t*u^3+1)*R^2 := by
  let Q := t*u^3+1
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hinner (v : ℂ) (hv : v ∈ closedBall w R) : v ∈ closedBall (u : ℂ) (1/32) := by
    have hvd := mem_closedBall.mp hv
    have hwd := mem_closedBall.mp hw
    have hd := dist_triangle v w (u : ℂ)
    apply mem_closedBall.mpr
    linarith
  have hw32 := closedBall_subset_closedBall (by norm_num : (1/102400 : ℝ) ≤ 1/32) hw
  have h := scalar_linearization_bound (complexSlope t) w (deriv (complexSlope t) w) R (204800*Q*R)
    (fun v hv => (slope_analytic_on_neighborhood t u hu v
      (closedBall_subset_closedBall (by norm_num : (1/32 : ℝ)≤1/16) (hinner v hv))).differentiableAt)
    (fun v hv => (stationary_slope_deriv_inner_lipschitz t u ht hu hs w v hw32 (hinner v hv)).trans
      (mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using mem_closedBall.mp hv) (by positivity)))
    (w+(R : ℂ)) w (by simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hR0] using le_refl R) (by simp [hR0])
  simp only [add_sub_cancel_left,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hR0] at h
  change ‖complexSlope t (w+(R : ℂ))-complexSlope t w-deriv (complexSlope t) w*(R : ℂ)‖ ≤ _ at h
  convert h using 1 <;> ring

theorem saddle_right_boundary_slope (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/102400)) (hstat : complexSlope t w= -(Complex.I*z))
    (R : ℝ) (hR0 : 0 ≤ R) (hR : R ≤ 1/819200) :
    (complexSlope t (w+(R : ℂ))).re-z.im ≤ -(t*u^3+1)*R := by
  let Q := t*u^3+1
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hlin := slope_local_linearization t u ht hu hs w hw R hR0 hR
  have hre := Complex.re_le_norm (complexSlope t (w+(R : ℂ))-complexSlope t w-deriv (complexSlope t) w*(R : ℂ))
  have hc := gaussian_coefficient_lower t u ht hu hs w hw
  simp only [Complex.div_ofNat_re,Complex.neg_re] at hc
  simp [Complex.sub_re,Complex.mul_re,Complex.mul_im,hstat] at hre
  have hcurv := mul_le_mul_of_nonneg_right (by linarith : (deriv (complexSlope t) w).re ≤ -2*Q) hR0
  have hcoef : 204800*Q*R ≤ Q := by nlinarith
  have hrem := mul_le_mul_of_nonneg_right hcoef hR0
  rw [hstat] at hlin
  simp only [sub_neg_eq_add] at hlin
  change ‖complexSlope t (w+(R : ℂ))+Complex.I*z-deriv (complexSlope t) w*(R : ℂ)‖ ≤ 204800*Q*R^2 at hlin
  change (complexSlope t (w+(R : ℂ))).re-z.im ≤ -Q*R
  nlinarith

theorem saddle_right_distant_tail_yupper (t u : ℝ) (ht : 0 < t) (hu : 2 ≤ u) (hs : phaseSlope t u=0)
    (z w : ℂ) (hy : z.im ≤ t/4) (hw : w ∈ closedBall (u : ℂ) (1/102400))
    (hstat : complexSlope t w= -(Complex.I*z)) (R : ℝ) (hR0 : 0 < R) (hR : R ≤ 1/819200) :
    ‖∫ x : ℝ in Ioi (w.re+R), saddleWeight t z ((x : ℂ)+(w.im : ℂ)*Complex.I)‖ ≤
      ‖saddleWeight t z w‖*Real.exp (-((3/4 : ℝ)*(t*u^3+1))*R^2)/((t*u^3+1)*R) := by
  have hu1 : 1 ≤ u := by linarith
  have hdist : ‖w-(u : ℂ)‖ ≤ (1/102400 : ℝ) := by simpa only [mem_closedBall,dist_eq_norm] using hw
  have him := (Complex.abs_im_le_norm (w-(u : ℂ))).trans hdist
  simp only [Complex.sub_im,Complex.ofReal_im,sub_zero] at him
  have hre := (Complex.abs_re_le_norm (w-(u : ℂ))).trans hdist
  simp only [Complex.sub_re,Complex.ofReal_re] at hre
  have ha : 1 ≤ w.re+R := by linarith [(abs_le.mp hre).1]
  have hp : ((w.re+R : ℝ) : ℂ)+(w.im : ℂ)*Complex.I=w+(R : ℂ) := by apply Complex.ext <;> simp [sub_eq_add_neg]
  have hslope := saddle_right_boundary_slope t u ht.le hu1 hs z w hw hstat R hR0.le hR
  rw [← hp] at hslope
  have hk : 0 < (t*u^3+1)*R := by positivity
  have hi := (right_signed_tail_bound_yupper t w.im (w.re+R) ((t*u^3+1)*R) z ht him hy ha hk (by simpa only [neg_mul] using hslope)).2
  have hlocal := actual_local_gaussian_envelope t u ht.le hu1 hs z w hw hstat R
    (by simpa only [abs_of_pos hR0] using hR)
  rw [hp] at hi
  simpa only [neg_mul] using hi.trans (div_le_div_of_nonneg_right hlocal hk.le)


theorem saddle_right_distant_tail (t u : ℝ) (ht : 0 < t) (hu : 2 ≤ u) (hs : phaseSlope t u=0)
    (z w : ℂ) (hy : z.im ≤ 0) (hw : w ∈ closedBall (u : ℂ) (1/102400))
    (hstat : complexSlope t w= -(Complex.I*z)) (R : ℝ) (hR0 : 0 < R) (hR : R ≤ 1/819200) :
    ‖∫ x : ℝ in Ioi (w.re+R), saddleWeight t z ((x : ℂ)+(w.im : ℂ)*Complex.I)‖ ≤
      ‖saddleWeight t z w‖*Real.exp (-((3/4 : ℝ)*(t*u^3+1))*R^2)/((t*u^3+1)*R) := by
  exact saddle_right_distant_tail_yupper t u ht hu hs z w (by linarith) hw hstat R hR0 hR

theorem saddle_left_distant_segment_yupper (t u : ℝ) (ht : 0 < t) (hu : 2 ≤ u) (hs : phaseSlope t u=0)
    (z w : ℂ) (hy : z.im ≤ t/4) (hw : w ∈ closedBall (u : ℂ) (1/102400))
    (hstat : complexSlope t w= -(Complex.I*z)) (R : ℝ) (hR0 : 0 < R) (hR : R ≤ 1/819200) :
    ‖∫ x : ℝ in 1..(w.re-R), saddleWeight t z ((x : ℂ)+(w.im : ℂ)*Complex.I)‖ ≤
      (w.re-R-1)*(‖saddleWeight t z w‖*Real.exp (-((3/4 : ℝ)*(t*u^3+1))*R^2)) := by
  have hu1 : 1 ≤ u := by linarith
  have hdist : ‖w-(u : ℂ)‖ ≤ (1/102400 : ℝ) := by simpa only [mem_closedBall,dist_eq_norm] using hw
  have him := (Complex.abs_im_le_norm (w-(u : ℂ))).trans hdist
  simp only [Complex.sub_im,Complex.ofReal_im,sub_zero] at him
  have hre := (Complex.abs_re_le_norm (w-(u : ℂ))).trans hdist
  simp only [Complex.sub_re,Complex.ofReal_re] at hre
  have ha : 1 ≤ w.re-R := by linarith [(abs_le.mp hre).1]
  have hp0 : (w.re : ℂ)+(w.im : ℂ)*Complex.I=w := by apply Complex.ext <;> simp [sub_eq_add_neg]
  have hp : ((w.re-R : ℝ) : ℂ)+(w.im : ℂ)*Complex.I=w+((-R : ℝ) : ℂ) := by apply Complex.ext <;> simp [sub_eq_add_neg]
  have hsre : (complexSlope t ((w.re : ℂ)+(w.im : ℂ)*Complex.I)).re=z.im := by
    rw [hp0,hstat]
    simp [Complex.mul_re]
  have hshape := (horizontal_norm_sq_shape_yupper t w.im w.re z ht him hy (by linarith) hsre).1
  have hlocal := actual_local_gaussian_envelope t u ht.le hu1 hs z w hw hstat (-R)
    (by simpa only [abs_neg,abs_of_pos hR0] using hR)
  simp only [neg_sq] at hlocal
  have hpoint (x : ℝ) (hx : x ∈ Ioc 1 (w.re-R)) :
      ‖saddleWeight t z ((x : ℂ)+(w.im : ℂ)*Complex.I)‖ ≤
        ‖saddleWeight t z w‖*Real.exp (-((3/4 : ℝ)*(t*u^3+1))*R^2) := by
    have hm := hshape (show x ∈ Icc 1 w.re from ⟨hx.1.le,by linarith [hx.2]⟩)
      (show w.re-R ∈ Icc 1 w.re from ⟨ha,by linarith⟩) hx.2
    have hn := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hm
    rw [hp] at hn
    simpa only [neg_mul] using hn.trans hlocal
  have hg : IntervalIntegrable (fun _ : ℝ => ‖saddleWeight t z w‖*
      Real.exp (-((3/4 : ℝ)*(t*u^3+1))*R^2)) volume 1 (w.re-R) := intervalIntegrable_const
  have hb := intervalIntegral.norm_integral_le_of_norm_le ha (Eventually.of_forall hpoint) hg
  simpa only [intervalIntegral.integral_const,smul_eq_mul] using hb


theorem saddle_left_distant_segment (t u : ℝ) (ht : 0 < t) (hu : 2 ≤ u) (hs : phaseSlope t u=0)
    (z w : ℂ) (hy : z.im ≤ 0) (hw : w ∈ closedBall (u : ℂ) (1/102400))
    (hstat : complexSlope t w= -(Complex.I*z)) (R : ℝ) (hR0 : 0 < R) (hR : R ≤ 1/819200) :
    ‖∫ x : ℝ in 1..(w.re-R), saddleWeight t z ((x : ℂ)+(w.im : ℂ)*Complex.I)‖ ≤
      (w.re-R-1)*(‖saddleWeight t z w‖*Real.exp (-((3/4 : ℝ)*(t*u^3+1))*R^2)) := by
  exact saddle_left_distant_segment_yupper t u ht hu hs z w (by linarith) hw hstat R hR0 hR

end OperatorDerivativeRewrite.Foundation.RiemannQuarticDistantTail
