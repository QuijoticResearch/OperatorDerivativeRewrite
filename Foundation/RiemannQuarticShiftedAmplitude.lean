import Foundation.RiemannQuarticWeightedSlope
import Mathlib.Analysis.InnerProductSpace.Calculus
/-! Actual shifted-amplitude shape and signed right-tail estimates.
The exact derivative of norm(W)^2 and actual weighted-slope monotonicity
show increase before a shifted stationary point and decrease afterward on x>=1.
A boundary slope <=-k, k>0, gives exponential decay and an actual signed tail
integral bound norm(W(boundary))/k. The boundary slope and its quantitative
relation to the saddle remain explicit hypotheses; global Fourier zero control
is not inferred. -/
noncomputable section
open Set Metric Complex Filter MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticShiftedAmplitude
open RiemannQuarticWeightedSlope RiemannQuarticSaddleNeighborhood RiemannQuarticSaddleBranch
open RiemannQuarticSpatialPhase RiemannQuarticFrequencyBranch

theorem horizontal_weight_hasDerivAt (t h x : ℝ) (z : ℂ) (hx : 1 ≤ x)
    (hh : |h| ≤ 1/102400) :
    HasDerivAt (fun v : ℝ => saddleWeight t z ((v : ℂ)+(h : ℂ)*Complex.I))
      ((complexSlope t ((x : ℂ)+(h : ℂ)*Complex.I)+Complex.I*z)*
        saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)) x := by
  let w := (x : ℂ)+(h : ℂ)*Complex.I
  have hw : w ∈ closedBall (x : ℂ) (1/16) := horizontal_point_mem x h _ (hh.trans (by norm_num))
  have hdom := neighborhood_domain x hx w hw
  have hn := kernel_nonzero_on_neighborhood x hx w hw
  have hd := (spatial_weight_hasDerivAt t z w (by linarith [hdom.2]) hn).comp (x : ℂ)
    ((hasDerivAt_id (x : ℂ)).add_const ((h : ℂ)*Complex.I))
  have hd' : HasDerivAt (fun v : ℂ => saddleWeight t z (v+(h : ℂ)*Complex.I))
      ((complexSlope t w+Complex.I*z)*saddleWeight t z w) (x : ℂ) := by
    convert hd using 1 <;> first | rfl | simp only [mul_one]
  exact hd'.comp_ofReal

theorem horizontal_norm_sq_hasDerivAt (t h x : ℝ) (z : ℂ) (hx : 1 ≤ x)
    (hh : |h| ≤ 1/102400) :
    HasDerivAt (fun v : ℝ => ‖saddleWeight t z ((v : ℂ)+(h : ℂ)*Complex.I)‖^2)
      (2*((complexSlope t ((x : ℂ)+(h : ℂ)*Complex.I)).re-z.im)*
        ‖saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)‖^2) x := by
  have hd := (horizontal_weight_hasDerivAt t h x z hx hh).norm_sq
  convert hd using 1
  simp [Complex.inner,mul_assoc,Complex.mul_conj',Complex.mul_re,Complex.mul_im,
    ← Complex.ofReal_pow,sub_eq_add_neg]

theorem horizontal_norm_sq_shape_yupper (t h a : ℝ) (z : ℂ) (ht : 0 < t)
    (hh : |h| ≤ 1/102400) (hy : z.im ≤ t/4) (ha : 1 ≤ a)
    (hs : (complexSlope t ((a : ℂ)+(h : ℂ)*Complex.I)).re=z.im) :
    MonotoneOn (fun x : ℝ => ‖saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)‖^2) (Icc 1 a) ∧
    AntitoneOn (fun x : ℝ => ‖saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)‖^2) (Ici a) := by
  have hsign := shifted_slope_signs_yupper t h z.im a ht hh hy ha hs
  constructor
  · apply monotoneOn_of_deriv_nonneg (convex_Icc 1 a)
    · intro x hx
      exact (horizontal_norm_sq_hasDerivAt t h x z hx.1 hh).continuousAt.continuousWithinAt
    · intro x hx
      exact (horizontal_norm_sq_hasDerivAt t h x z (interior_subset hx).1 hh).differentiableAt.differentiableWithinAt
    · intro x hx
      have hxa : x < a := (by simpa only [interior_Icc,mem_Ioo] using hx : 1 < x ∧ x < a).2
      have hx1 : 1 ≤ x := (interior_subset hx).1
      rw [(horizontal_norm_sq_hasDerivAt t h x z hx1 hh).deriv]
      exact mul_nonneg (by linarith [hsign.1 x hx1 hxa]) (sq_nonneg _)
  · apply antitoneOn_of_deriv_nonpos (convex_Ici a)
    · intro x hx
      exact (horizontal_norm_sq_hasDerivAt t h x z (le_trans ha hx) hh).continuousAt.continuousWithinAt
    · intro x hx
      exact (horizontal_norm_sq_hasDerivAt t h x z (le_trans ha (interior_subset hx)) hh).differentiableAt.differentiableWithinAt
    · intro x hx
      have hax : a < x := by simpa only [interior_Ici,mem_Ioi] using hx
      rw [(horizontal_norm_sq_hasDerivAt t h x z (le_trans ha hax.le) hh).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hsign.2 x hax]) (sq_nonneg _)


theorem horizontal_norm_sq_shape (t h a : ℝ) (z : ℂ) (ht : 0 < t)
    (hh : |h| ≤ 1/102400) (hy : z.im ≤ 0) (ha : 1 ≤ a)
    (hs : (complexSlope t ((a : ℂ)+(h : ℂ)*Complex.I)).re=z.im) :
    MonotoneOn (fun x : ℝ => ‖saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)‖^2) (Icc 1 a) ∧
    AntitoneOn (fun x : ℝ => ‖saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)‖^2) (Ici a) := by
  exact horizontal_norm_sq_shape_yupper t h a z ht hh (by linarith) ha hs

theorem right_slope_bound_yupper (t h y b : ℝ) (ht : 0 < t)
    (hh : |h| ≤ 1/102400) (hy : y ≤ t/4) (hb : 1 ≤ b)
    (hneg : (complexSlope t ((b : ℂ)+(h : ℂ)*Complex.I)).re-y ≤ 0)
    (x : ℝ) (hbx : b ≤ x) :
    (complexSlope t ((x : ℂ)+(h : ℂ)*Complex.I)).re-y ≤
      (complexSlope t ((b : ℂ)+(h : ℂ)*Complex.I)).re-y := by
  have hm := (normalizedSlope_strictAntiOn_yupper t h y ht hh hy).antitoneOn hb (hb.trans hbx) hbx
  have he : Real.exp (-4*x) ≤ Real.exp (-4*b) := Real.exp_le_exp.mpr (by linarith)
  have hp := mul_le_mul_of_nonpos_right he hneg
  exact (mul_le_mul_iff_right₀ (Real.exp_pos (-4*x))).mp (hm.trans hp)


theorem right_slope_bound (t h y b : ℝ) (ht : 0 < t)
    (hh : |h| ≤ 1/102400) (hy : y ≤ 0) (hb : 1 ≤ b)
    (hneg : (complexSlope t ((b : ℂ)+(h : ℂ)*Complex.I)).re-y ≤ 0)
    (x : ℝ) (hbx : b ≤ x) :
    (complexSlope t ((x : ℂ)+(h : ℂ)*Complex.I)).re-y ≤
      (complexSlope t ((b : ℂ)+(h : ℂ)*Complex.I)).re-y := by
  exact right_slope_bound_yupper t h y b ht hh (by linarith) hb hneg x hbx

theorem tilted_norm_sq_hasDerivAt (t h b k x : ℝ) (z : ℂ) (hx : 1 ≤ x)
    (hh : |h| ≤ 1/102400) :
    HasDerivAt (fun v : ℝ => Real.exp (2*k*(v-b))*‖saddleWeight t z ((v : ℂ)+(h : ℂ)*Complex.I)‖^2)
      (2*Real.exp (2*k*(x-b))*((complexSlope t ((x : ℂ)+(h : ℂ)*Complex.I)).re-z.im+k)*
        ‖saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)‖^2) x := by
  have he := ((((hasDerivAt_id x).sub_const b).const_mul (2*k)).exp).mul
    (horizontal_norm_sq_hasDerivAt t h x z hx hh)
  convert he using 1
  · funext v; rfl
  · dsimp
    ring

theorem right_weight_exponential_decay_yupper (t h b k : ℝ) (z : ℂ) (ht : 0 < t)
    (hh : |h| ≤ 1/102400) (hy : z.im ≤ t/4) (hb : 1 ≤ b) (hk : 0 ≤ k)
    (hslope : (complexSlope t ((b : ℂ)+(h : ℂ)*Complex.I)).re-z.im ≤ -k)
    (x : ℝ) (hbx : b ≤ x) :
    ‖saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)‖ ≤
      ‖saddleWeight t z ((b : ℂ)+(h : ℂ)*Complex.I)‖*Real.exp (-k*(x-b)) := by
  have hanti : AntitoneOn (fun v : ℝ => Real.exp (2*k*(v-b))*
      ‖saddleWeight t z ((v : ℂ)+(h : ℂ)*Complex.I)‖^2) (Ici b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici b)
    · intro v hv
      exact (tilted_norm_sq_hasDerivAt t h b k v z (hb.trans hv) hh).continuousAt.continuousWithinAt
    · intro v hv
      exact (tilted_norm_sq_hasDerivAt t h b k v z (hb.trans (interior_subset hv)) hh).differentiableAt.differentiableWithinAt
    · intro v hv
      have hbv : b ≤ v := interior_subset hv
      have hs := right_slope_bound_yupper t h z.im b ht hh hy hb (by linarith) v hbv
      rw [(tilted_norm_sq_hasDerivAt t h b k v z (hb.trans hbv) hh).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)) (sq_nonneg _)
  have hi := hanti (by simp : b ∈ Set.Ici b) hbx hbx
  simp only [sub_self,mul_zero,Real.exp_zero,one_mul] at hi
  rw [show 2*k*(x-b)=k*(x-b)+k*(x-b) by ring,Real.exp_add] at hi
  have hs : (Real.exp (k*(x-b))*‖saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)‖)^2 ≤
      ‖saddleWeight t z ((b : ℂ)+(h : ℂ)*Complex.I)‖^2 := by nlinarith [hi]
  have hl := (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp hs
  calc
    _ = Real.exp (-k*(x-b))*(Real.exp (k*(x-b))*‖saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)‖) := by
      rw [← mul_assoc,← Real.exp_add]
      simp
    _ ≤ Real.exp (-k*(x-b))*‖saddleWeight t z ((b : ℂ)+(h : ℂ)*Complex.I)‖ :=
      mul_le_mul_of_nonneg_left hl (Real.exp_pos _).le
    _ = _ := mul_comm _ _


theorem right_weight_exponential_decay (t h b k : ℝ) (z : ℂ) (ht : 0 < t)
    (hh : |h| ≤ 1/102400) (hy : z.im ≤ 0) (hb : 1 ≤ b) (hk : 0 ≤ k)
    (hslope : (complexSlope t ((b : ℂ)+(h : ℂ)*Complex.I)).re-z.im ≤ -k)
    (x : ℝ) (hbx : b ≤ x) :
    ‖saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)‖ ≤
      ‖saddleWeight t z ((b : ℂ)+(h : ℂ)*Complex.I)‖*Real.exp (-k*(x-b)) := by
  exact right_weight_exponential_decay_yupper t h b k z ht hh (by linarith) hb hk hslope x hbx

theorem right_signed_tail_bound_yupper (t h b k : ℝ) (z : ℂ) (ht : 0 < t)
    (hh : |h| ≤ 1/102400) (hy : z.im ≤ t/4) (hb : 1 ≤ b) (hk : 0 < k)
    (hslope : (complexSlope t ((b : ℂ)+(h : ℂ)*Complex.I)).re-z.im ≤ -k) :
    IntegrableOn (fun x : ℝ => saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)) (Ioi b) ∧
    ‖∫ x : ℝ in Ioi b, saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)‖ ≤
      ‖saddleWeight t z ((b : ℂ)+(h : ℂ)*Complex.I)‖/k := by
  let B := ‖saddleWeight t z ((b : ℂ)+(h : ℂ)*Complex.I)‖
  have hg : IntegrableOn (fun x : ℝ => (B*Real.exp (k*b))*Real.exp ((-k)*x)) (Ioi b) :=
    (exp_neg_integrableOn_Ioi b hk).const_mul _
  have hbound : ∀ᵐ (x : ℝ) ∂volume.restrict (Ioi b),
      ‖saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)‖ ≤ (B*Real.exp (k*b))*Real.exp ((-k)*x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hd := right_weight_exponential_decay_yupper t h b k z ht hh hy hb hk.le hslope x (show b ≤ x from le_of_lt hx)
    convert hd using 1
    rw [mul_assoc,← Real.exp_add]
    congr 1
    ring
  constructor
  · exact (RiemannQuarticContour.shifted_weight_integrable t z h (hh.trans (by norm_num))).mono_set
      (by intro x hx; exact lt_trans (by linarith : (0 : ℝ)<b) hx)
  · calc
      _ ≤ ∫ x : ℝ in Ioi b, (B*Real.exp (k*b))*Real.exp ((-k)*x) := norm_integral_le_of_norm_le hg hbound
      _ = B/k := by
        rw [integral_const_mul,integral_exp_mul_Ioi (neg_lt_zero.mpr hk)]
        have he : Real.exp (k*b)*Real.exp ((-k)*b)=1 := by rw [← Real.exp_add]; simp [neg_mul]
        calc
          _ = B*(Real.exp (k*b)*Real.exp ((-k)*b))/k := by ring
          _ = _ := by rw [he,mul_one]


theorem right_signed_tail_bound (t h b k : ℝ) (z : ℂ) (ht : 0 < t)
    (hh : |h| ≤ 1/102400) (hy : z.im ≤ 0) (hb : 1 ≤ b) (hk : 0 < k)
    (hslope : (complexSlope t ((b : ℂ)+(h : ℂ)*Complex.I)).re-z.im ≤ -k) :
    IntegrableOn (fun x : ℝ => saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)) (Ioi b) ∧
    ‖∫ x : ℝ in Ioi b, saddleWeight t z ((x : ℂ)+(h : ℂ)*Complex.I)‖ ≤
      ‖saddleWeight t z ((b : ℂ)+(h : ℂ)*Complex.I)‖/k := by
  exact right_signed_tail_bound_yupper t h b k z ht hh (by linarith) hb hk hslope

end OperatorDerivativeRewrite.Foundation.RiemannQuarticShiftedAmplitude
