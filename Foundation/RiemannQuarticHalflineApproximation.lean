import Foundation.RiemannQuarticCompactSegment
import Foundation.RiemannQuarticGaussianNormalization
/-! Actual signed half-line saddle comparison with explicit relative error.
Exact shifted splitting combines the compact segment, local window and both
actual distant tails. Gaussian normalization converts this to a relative bound.
For an actual maximizing saddle branch and the stated frequency conditions,
the compact hypothesis is discharged; the unshifted positive half-line also
retains and controls its vertical endpoint contribution. The error budget is
explicit. Joint asymptotic limits, the opposite-frequency channel, zero counts
and unrestricted frequency far field remain unproved. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticHalflineApproximation
open RiemannQuarticFrequencyBranch RiemannQuarticContour RiemannQuarticSaddleNeighborhood
open RiemannQuarticSaddleBranch RiemannQuarticSaddleTimes RiemannQuarticLocalTail
open RiemannQuarticDistantTail RiemannQuarticCompactSegment RiemannQuarticGaussianNormalization
open RiemannQuarticDomain RiemannQuarticKernel RiemannQuarticEndpointSaddle RiemannQuarticSaddleGeometry

def horizontalBudget (Q a r R : ℝ) : ℝ :=
  819200*Q*r^4+Real.exp (-Q*r^2)/(Q*r)+Real.exp (-((3/4 : ℝ)*Q)*r^2)/(((3/4 : ℝ)*Q)*r)+
    (a-R-1)*Real.exp (-((3/4 : ℝ)*Q)*R^2)+Real.exp (-((3/4 : ℝ)*Q)*R^2)/(Q*R)

theorem actual_halfline_split (t : ℝ) (z w : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hw : |w.im| ≤ 1/16) (ha : 1 ≤ w.re-R) :
    (∫ x : ℝ in Ioi 0, saddleWeight t z ((x : ℂ)+(w.im : ℂ)*Complex.I))=
      (∫ x : ℝ in 0..1, saddleWeight t z ((x : ℂ)+(w.im : ℂ)*Complex.I))+
      (∫ x : ℝ in 1..(w.re-R), saddleWeight t z ((x : ℂ)+(w.im : ℂ)*Complex.I))+
      (∫ s : ℝ in -R..R, saddleWeight t z (w+(s : ℂ)))+
      (∫ x : ℝ in Ioi (w.re+R), saddleWeight t z ((x : ℂ)+(w.im : ℂ)*Complex.I)) := by
  let f := fun x : ℝ => saddleWeight t z ((x : ℂ)+(w.im : ℂ)*Complex.I)
  have hc := shifted_weight_continuous t z w.im hw
  have hi := shifted_weight_integrable t z w.im hw
  have hip : IntegrableOn f (Ioi (w.re+R)) := hi.mono_set
    (by intro x hx; change 0 < x; change w.re+R<x at hx; linarith)
  have hsplit := intervalIntegral.integral_interval_add_Ioi (f := f) hi hip
  have hs1 := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume) (hc.intervalIntegrable 0 1) (hc.intervalIntegrable 1 (w.re-R))
  have hs2 := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume) (hc.intervalIntegrable 0 (w.re-R)) (hc.intervalIntegrable (w.re-R) (w.re+R))
  have htranslate : (∫ s : ℝ in -R..R, saddleWeight t z (w+(s : ℂ)))=
      ∫ x : ℝ in (w.re-R)..(w.re+R), f x := by
    have h := intervalIntegral.integral_comp_add_left (f := f) (a := -R) (b := R) w.re
    have hf : (fun s : ℝ => saddleWeight t z (w+(s : ℂ)))=(fun s : ℝ => f (w.re+s)) := by
      funext s
      dsimp [f]
      congr 1
      apply Complex.ext <;> simp
    rw [hf]
    simpa only [sub_eq_add_neg] using h
  change (∫ x : ℝ in Ioi 0, f x)=(∫ x : ℝ in 0..1, f x)+(∫ x : ℝ in 1..(w.re-R), f x)+
    (∫ s : ℝ in -R..R, saddleWeight t z (w+(s : ℂ)))+(∫ x : ℝ in Ioi (w.re+R), f x)
  rw [htranslate]
  change (∫ x : ℝ in 0..1, f x)+(∫ x : ℝ in 1..(w.re-R), f x)=(∫ x : ℝ in 0..(w.re-R), f x) at hs1
  change (∫ x : ℝ in 0..(w.re-R), f x)+(∫ x : ℝ in (w.re-R)..(w.re+R), f x)=
    (∫ x : ℝ in 0..(w.re+R), f x) at hs2
  linear_combination -hsplit-hs1-hs2

theorem halfline_error_of_compact_bound (t u : ℝ) (ht : 0 < t) (hu : 2 ≤ u) (hs : phaseSlope t u=0)
    (z w : ℂ) (hy : z.im ≤ 0) (hw : w ∈ closedBall (u : ℂ) (1/102400))
    (hstat : complexSlope t w= -(Complex.I*z)) (r R B : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (hR : R ≤ 1/819200) (hsmall : 204800*(t*u^3+1)*r^3 ≤ 1)
    (hcompact : ‖∫ x : ℝ in 0..1, saddleWeight t z ((x : ℂ)+(w.im : ℂ)*Complex.I)‖ ≤
      ‖saddleWeight t z w‖*B) :
    ‖(∫ x : ℝ in Ioi 0, saddleWeight t z ((x : ℂ)+(w.im : ℂ)*Complex.I))-
      saddleWeight t z w*((Real.pi : ℂ)/(-(deriv (complexSlope t) w)/2))^(1/2 : ℂ)‖ ≤
      ‖saddleWeight t z w‖*(B+horizontalBudget (t*u^3+1) w.re r R) := by
  let A := saddleWeight t z w
  let G := ((Real.pi : ℂ)/(-(deriv (complexSlope t) w)/2))^(1/2 : ℂ)
  let f := fun x : ℝ => saddleWeight t z ((x : ℂ)+(w.im : ℂ)*Complex.I)
  have hR0 : 0 < R := hr.trans_le hrR
  have hdist : ‖w-(u : ℂ)‖ ≤ (1/102400 : ℝ) := by simpa only [mem_closedBall,dist_eq_norm] using hw
  have him := (Complex.abs_im_le_norm (w-(u : ℂ))).trans hdist
  simp only [Complex.sub_im,Complex.ofReal_im,sub_zero] at him
  have hre := (Complex.abs_re_le_norm (w-(u : ℂ))).trans hdist
  simp only [Complex.sub_re,Complex.ofReal_re] at hre
  have ha : 1 ≤ w.re-R := by linarith [(abs_le.mp hre).1]
  have hsplit := actual_halfline_split t z w R hR0.le (him.trans (by norm_num)) ha
  have hleft := saddle_left_distant_segment t u ht hu hs z w hy hw hstat R hR0 hR
  have hright := saddle_right_distant_tail t u ht hu hs z w hy hw hstat R hR0 hR
  have hwindow := fixed_window_gaussian_error t u ht.le (by linarith) hs z w hw hstat r R hr hrR hR hsmall
  have he : (∫ x : ℝ in Ioi 0, f x)-A*G=
      ((∫ x : ℝ in 0..1, f x)+(∫ x : ℝ in 1..(w.re-R), f x))+
      ((∫ s : ℝ in -R..R, saddleWeight t z (w+(s : ℂ)))-A*G)+
      (∫ x : ℝ in Ioi (w.re+R), f x) := by
    change (∫ x : ℝ in Ioi 0, f x)=(∫ x : ℝ in 0..1, f x)+(∫ x : ℝ in 1..(w.re-R), f x)+
      (∫ s : ℝ in -R..R, saddleWeight t z (w+(s : ℂ)))+(∫ x : ℝ in Ioi (w.re+R), f x) at hsplit
    rw [hsplit]
    ring
  change ‖(∫ x : ℝ in Ioi 0, f x)-A*G‖ ≤ _
  rw [he]
  have hn1 := norm_add_le ((∫ x : ℝ in 0..1, f x)+(∫ x : ℝ in 1..(w.re-R), f x)+
      ((∫ s : ℝ in -R..R, saddleWeight t z (w+(s : ℂ)))-A*G)) (∫ x : ℝ in Ioi (w.re+R), f x)
  have hn2 := norm_add_le ((∫ x : ℝ in 0..1, f x)+(∫ x : ℝ in 1..(w.re-R), f x))
      ((∫ s : ℝ in -R..R, saddleWeight t z (w+(s : ℂ)))-A*G)
  have hn3 := norm_add_le (∫ x : ℝ in 0..1, f x) (∫ x : ℝ in 1..(w.re-R), f x)
  dsimp [A,G,f] at hn1 hn2 hn3 ⊢
  simp only [horizontalBudget,neg_mul,div_eq_mul_inv] at hleft hright hwindow hn1 hn2 hn3 hcompact ⊢
  nlinarith

theorem halfline_relative_error_of_compact_bound (t u : ℝ) (ht : 0 < t) (hu : 2 ≤ u) (hs : phaseSlope t u=0)
    (z w : ℂ) (hy : z.im ≤ 0) (hw : w ∈ closedBall (u : ℂ) (1/102400))
    (hstat : complexSlope t w= -(Complex.I*z)) (r R B : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (hR : R ≤ 1/819200) (hsmall : 204800*(t*u^3+1)*r^3 ≤ 1)
    (hcompact : ‖∫ x : ℝ in 0..1, saddleWeight t z ((x : ℂ)+(w.im : ℂ)*Complex.I)‖ ≤
      ‖saddleWeight t z w‖*B) :
    ‖(∫ x : ℝ in Ioi 0, saddleWeight t z ((x : ℂ)+(w.im : ℂ)*Complex.I))/
      (saddleWeight t z w*((Real.pi : ℂ)/(-(deriv (complexSlope t) w)/2))^(1/2 : ℂ))-1‖ ≤
      40*Real.sqrt (t*u^3+1)*(B+horizontalBudget (t*u^3+1) w.re r R) := by
  let A := saddleWeight t z w
  let G := ((Real.pi : ℂ)/(-(deriv (complexSlope t) w)/2))^(1/2 : ℂ)
  let J := ∫ x : ℝ in Ioi 0, saddleWeight t z ((x : ℂ)+(w.im : ℂ)*Complex.I)
  let E := B+horizontalBudget (t*u^3+1) w.re r R
  let c := 40*Real.sqrt (t*u^3+1)
  have hu1 : 1 ≤ u := by linarith
  have hAne : A ≠ 0 := by
    dsimp [A,saddleWeight]
    exact mul_ne_zero (Complex.exp_ne_zero _) (kernel_nonzero_on_neighborhood u hu1 w
      (closedBall_subset_closedBall (by norm_num : (1/102400 : ℝ)≤1/16) hw))
  have hApos : 0 < ‖A‖ := norm_pos_iff.mpr hAne
  have hG := gaussian_norm_lower t u ht.le hu1 hs w hw
  change 1 ≤ c*‖G‖ at hG
  have hc : 0 < c := by dsimp [c]; positivity
  have hGpos : 0 < ‖G‖ := by nlinarith [norm_nonneg G]
  have hGne : G ≠ 0 := norm_pos_iff.mp hGpos
  have hmain := halfline_error_of_compact_bound t u ht hu hs z w hy hw hstat r R B hr hrR hR hsmall hcompact
  change ‖J-A*G‖ ≤ ‖A‖*E at hmain
  have hE : 0 ≤ E := by nlinarith [norm_nonneg (J-A*G)]
  have hm := mul_le_mul_of_nonneg_left hG (mul_nonneg hApos.le hE)
  have hscaled : ‖J-A*G‖ ≤ (c*E)*(‖A‖*‖G‖) := by nlinarith
  have hid : J/(A*G)-1=(J-A*G)/(A*G) := by field_simp [hAne,hGne]
  change ‖J/(A*G)-1‖ ≤ c*E
  rw [hid,norm_div,norm_mul]
  exact (div_le_iff₀ (mul_pos hApos hGpos)).mpr hscaled

theorem branch_halfline_relative_error (t u : ℝ) (ht : 0 < t) (hu : 2 ≤ u)
    (hm : IsMaxOn (weighted 0 t 0) (Ici 0) u) (hs : phaseSlope t u=0)
    (z : ℂ) (hz : ‖z‖ < (t*u^3+1)/51200) (hy : z.im ≤ 0) (hzt : ‖z‖ ≤ t)
    (hphase : (25600/(t*u^3+1)^2)*‖z‖^3 ≤ 1) (hregion : ‖z‖^2 ≤ t*(t*u^3+1))
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) (hR : R ≤ 1/819200)
    (hsmall : 204800*(t*u^3+1)*r^3 ≤ 1) :
    let w := branch t u ht.le (le_trans (by norm_num : (1 : ℝ)≤2) hu) hs z
    ‖(∫ x : ℝ in Ioi 0, saddleWeight t z ((x : ℂ)+(w.im : ℂ)*Complex.I))/
      (saddleWeight t z w*((Real.pi : ℂ)/(-(deriv (complexSlope t) w)/2))^(1/2 : ℂ))-1‖ ≤
      40*Real.sqrt (t*u^3+1)*((5676/kernel 3)*Real.exp (10-503*t/8)+
        horizontalBudget (t*u^3+1) w.re r R) := by
  let hu1 : 1 ≤ u := le_trans (by norm_num : (1 : ℝ)≤2) hu
  let w := branch t u ht.le hu1 hs z
  have hspec := branch_spec t u ht.le hu1 hs z hz.le
  have him := Complex.abs_im_le_norm (w-(u : ℂ))
  have hdist : ‖w-(u : ℂ)‖ ≤ (1/102400 : ℝ) := by simpa only [mem_closedBall,dist_eq_norm] using hspec.1
  simp only [Complex.sub_im,Complex.ofReal_im,sub_zero] at him
  have hh : |w.im| ≤ 1/16 := (him.trans hdist).trans (by norm_num)
  have hcompact := compact_relative_saddle_bound t u ht.le hu1 hm hs z hz hy hzt hphase hregion w.im hh
  have hApos : 0 < ‖saddleWeight t z w‖ := norm_pos_iff.mpr (saddleWeight_ne_zero t u ht.le hu1 hs z hz.le)
  have hc := (div_le_iff₀ hApos).mp hcompact
  have hc' : ‖∫ x : ℝ in 0..1, saddleWeight t z ((x : ℂ)+(w.im : ℂ)*Complex.I)‖ ≤
      ‖saddleWeight t z w‖*((5676/kernel 3)*Real.exp (10-503*t/8)) := by simpa only [mul_comm] using hc
  exact halfline_relative_error_of_compact_bound t u ht hu hs z w hy hspec.1 hspec.2 r R
    ((5676/kernel 3)*Real.exp (10-503*t/8)) hr hrR hR hsmall hc'

theorem unshifted_branch_relative_error (t u : ℝ) (ht : 0 < t) (hu : 2 ≤ u)
    (hm : IsMaxOn (weighted 0 t 0) (Ici 0) u) (hs : phaseSlope t u=0)
    (z : ℂ) (hz : ‖z‖ < (t*u^3+1)/51200) (hre : 0 ≤ z.re) (hy : z.im ≤ 0) (hzt : ‖z‖ ≤ t)
    (hphase : (25600/(t*u^3+1)^2)*‖z‖^3 ≤ 1) (hregion : ‖z‖^2 ≤ t*(t*u^3+1))
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) (hR : R ≤ 1/819200)
    (hsmall : 204800*(t*u^3+1)*r^3 ≤ 1) :
    let w := branch t u ht.le (le_trans (by norm_num : (1 : ℝ)≤2) hu) hs z
    ‖(∫ x : ℝ in Ioi 0, saddleWeight t z (x : ℂ))/
      (saddleWeight t z w*((Real.pi : ℂ)/(-(deriv (complexSlope t) w)/2))^(1/2 : ℂ))-1‖ ≤
      40*Real.sqrt (t*u^3+1)*((5676/kernel 3)*Real.exp (10-503*t/8)+
        horizontalBudget (t*u^3+1) w.re r R+(5676/(16*kernel 1))*Real.exp (1-3*t/8)) := by
  let hu1 : 1 ≤ u := le_trans (by norm_num : (1 : ℝ)≤2) hu
  let w := branch t u ht.le hu1 hs z
  let A := saddleWeight t z w
  let G := ((Real.pi : ℂ)/(-(deriv (complexSlope t) w)/2))^(1/2 : ℂ)
  let J := ∫ x : ℝ in Ioi 0, saddleWeight t z (x : ℂ)
  let Jh := ∫ x : ℝ in Ioi 0, saddleWeight t z ((x : ℂ)+(w.im : ℂ)*Complex.I)
  let V := ∫ y : ℝ in 0..w.im, saddleWeight t z ((y : ℂ)*Complex.I)
  let c := 40*Real.sqrt (t*u^3+1)
  let Ce := (5676/(16*kernel 1))*Real.exp (1-3*t/8)
  have hspec := branch_spec t u ht.le hu1 hs z hz.le
  have hgeom := branch_geometry t u ht.le hu1 hs z hz.le hre
  have hApos : 0 < ‖A‖ := norm_pos_iff.mpr (saddleWeight_ne_zero t u ht.le hu1 hs z hz.le)
  have hG := gaussian_norm_lower t u ht.le hu1 hs w hspec.1
  change 1 ≤ c*‖G‖ at hG
  have hc : 0 < c := by dsimp [c]; positivity
  have hGpos : 0 < ‖G‖ := by nlinarith [norm_nonneg G]
  have hCe : 0 ≤ Ce := by dsimp [Ce]; positivity [kernel_pos 1 (by norm_num)]
  have he := left_segment_relative_saddle_bound t u ht.le hu1 hm hs z hz hre hy hphase hregion
    w.im hgeom.2.1 (by linarith [hgeom.2.2])
  change ‖V‖/‖A‖ ≤ Ce at he
  have hv := (div_le_iff₀ hApos).mp he
  have hmG := mul_le_mul_of_nonneg_left hG (mul_nonneg hApos.le hCe)
  have hvscaled : ‖V‖ ≤ (c*Ce)*(‖A‖*‖G‖) := by nlinarith
  have hvrelative : ‖Complex.I*V/(A*G)‖ ≤ c*Ce := by
    simp only [norm_div,norm_mul,Complex.norm_I,one_mul]
    exact (div_le_iff₀ (mul_pos hApos hGpos)).mpr hvscaled
  have hshift := halfline_shift_through_saddle t u ht.le hu1 hs z hz.le hre
  change J=Jh+Complex.I*V at hshift
  have hid : J/(A*G)-1=(Jh/(A*G)-1)+Complex.I*V/(A*G) := by rw [hshift]; ring
  have hh := branch_halfline_relative_error t u ht hu hm hs z hz hy hzt hphase hregion r R hr hrR hR hsmall
  change ‖Jh/(A*G)-1‖ ≤ c*((5676/kernel 3)*Real.exp (10-503*t/8)+horizontalBudget (t*u^3+1) w.re r R) at hh
  change ‖J/(A*G)-1‖ ≤ c*((5676/kernel 3)*Real.exp (10-503*t/8)+horizontalBudget (t*u^3+1) w.re r R+Ce)
  rw [hid]
  calc
    _ ≤ ‖Jh/(A*G)-1‖+‖Complex.I*V/(A*G)‖ := norm_add_le _ _
    _ ≤ c*((5676/kernel 3)*Real.exp (10-503*t/8)+horizontalBudget (t*u^3+1) w.re r R)+c*Ce :=
      add_le_add hh hvrelative
    _ = _ := by ring

end OperatorDerivativeRewrite.Foundation.RiemannQuarticHalflineApproximation
