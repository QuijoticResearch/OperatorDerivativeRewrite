import Foundation.RiemannRealOrderUniformAsymptotic

/-! A uniform frequency rate for the actual fractional cutoff sine transform.
The reciprocal-frequency parameter stays in a common principal-power domain. -/
noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderCutoffRate
open RiemannRealOrderUniformCutoff RiemannRealOrderCutoffBoundary
open RiemannRealOrderFractionalJets RiemannRealOrderFractionalCoefficient

def reciprocalBase (y : ℝ) : ℂ := ((y : ℂ)-Complex.I)⁻¹
def profile (t a y : ℝ) : ℂ := regularized t (reciprocalBase y) a
def profileDerivative (t a y : ℝ) : ℂ :=
  (mass a t : ℂ)*((2*a-2 : ℝ) : ℂ)*(reciprocalBase y)^((2*a-3 : ℝ) : ℂ)*
    (-(((y : ℂ)-Complex.I)^2)⁻¹)

private theorem denominator_ne_zero (y : ℝ) : (y : ℂ)-Complex.I≠0 := by
  intro h
  have hi := congrArg Complex.im h
  simp at hi

private theorem reciprocalBase_slit (y : ℝ) : reciprocalBase y ∈ Complex.slitPlane := by
  have hn := Complex.normSq_pos.mpr (denominator_ne_zero y)
  apply Complex.mem_slitPlane_iff.mpr
  right
  apply ne_of_gt
  unfold reciprocalBase
  rw [Complex.inv_im]
  simpa only [Complex.sub_im,Complex.ofReal_im,Complex.I_im,zero_sub,neg_neg] using
    one_div_pos.mpr hn

theorem profile_hasDerivAt (t a y : ℝ) :
    HasDerivAt (profile t a) (profileDerivative t a y) y := by
  have hd : HasDerivAt (fun v : ℂ => v-Complex.I) 1 (y : ℂ) :=
    (hasDerivAt_id (y : ℂ)).sub_const Complex.I
  have hi := hd.inv (denominator_ne_zero y)
  have hp := hi.cpow_const (c := ((2*a-2 : ℝ) : ℂ)) (reciprocalBase_slit y)
  have h := hp.const_mul (mass a t : ℂ)
  convert h.comp_ofReal using 1
  · rfl
  · dsimp only [profileDerivative,reciprocalBase,Pi.inv_apply]
    rw [show (((2*a-3 : ℝ) : ℂ))=(((2*a-2 : ℝ) : ℂ))-1 by push_cast; ring]
    ring

theorem profileDerivative_joint_continuousAt (t : ℝ) (p : ℝ × ℝ) (ha : 0 ≤ p.1) :
    ContinuousAt (fun q : ℝ × ℝ => profileDerivative t q.1 q.2) p := by
  have hm : ContinuousAt (fun q : ℝ × ℝ => (mass q.1 t : ℂ)) p :=
    Complex.continuous_ofReal.continuousAt.comp
      ((mass_continuousAt p.1 t ha).comp continuousAt_fst)
  have hd : ContinuousAt (fun q : ℝ × ℝ => (q.2 : ℂ)-Complex.I) p := by fun_prop
  have hb : ContinuousAt (fun q : ℝ × ℝ => reciprocalBase q.2) p :=
    hd.inv₀ (denominator_ne_zero p.2)
  have hp := hb.cpow
    (show ContinuousAt (fun q : ℝ × ℝ => ((2*q.1-3 : ℝ) : ℂ)) p by fun_prop)
    (reciprocalBase_slit p.2)
  have hinv := (hd.pow 2).inv₀ (pow_ne_zero 2 (denominator_ne_zero p.2))
  have he : ContinuousAt (fun q : ℝ × ℝ => ((2*q.1-2 : ℝ) : ℂ)) p := by fun_prop
  exact ((hm.mul he).mul hp).mul hinv.neg

theorem profile_uniform_lipschitz_bound (t : ℝ) : ∃ M : ℝ, 0 ≤ M ∧
    ∀ a : ℝ, 1 ≤ a → a ≤ 5/4 → ∀ y ∈ Icc (0 : ℝ) 1,
      ‖profile t a y-profile t a 0‖ ≤ M*y := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => profileDerivative t p.1 p.2)
      (Icc 1 (5/4) ×ˢ Icc 0 1) := by
    intro p hp
    exact (profileDerivative_joint_continuousAt t p (by linarith [hp.1.1])).continuousWithinAt
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc
  refine ⟨max M 0,le_max_right _ _,?_⟩
  intro a ha ha5 y hy
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := (0 : ℝ)) (b := 1) (C := max M 0)
    (fun v _ => (profile_hasDerivAt t a v).hasDerivWithinAt)
    (fun v hv => (hM (a,v) ⟨⟨ha,ha5⟩,⟨hv.1,hv.2.le⟩⟩).trans (le_max_left M 0)) y hy
  simpa only [sub_zero] using h

theorem regularized_uniform_rate (t : ℝ) : ∃ M : ℝ, 0 ≤ M ∧
    ∀ a : ℝ, 1 ≤ a → a ≤ 5/4 → ∀ x : ℝ, 1 ≤ x →
      ‖regularized t (scaledBase x) a-regularized t Complex.I a‖ ≤ M*x⁻¹ := by
  obtain ⟨M,hM,h⟩ := profile_uniform_lipschitz_bound t
  refine ⟨M,hM,?_⟩
  intro a ha ha5 x hx
  have hx0 : 0 < x := by linarith
  have hinv : x⁻¹ ∈ Icc (0 : ℝ) 1 := ⟨(inv_pos.mpr hx0).le,by
    simpa only [one_div,inv_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hx⟩
  simpa only [profile,reciprocalBase,Complex.ofReal_zero,zero_sub,inv_neg,Complex.inv_I,
    neg_neg,scaledBase] using h a ha ha5 x⁻¹ hinv

theorem actual_cutoff_sine_uniform_rate (t : ℝ) : ∃ M : ℝ, 0 ≤ M ∧
    ∀ a : ℝ, 1 < a → a ≤ 5/4 → ∀ x : ℝ, 1 ≤ x →
      ‖((x^(2*a-2) : ℝ) : ℂ)*(∫ u : ℝ in Ioi 0, cutoff a t u*(Real.sin (x*u) : ℂ))-
        (leading a t : ℂ)‖ ≤ M*x⁻¹ := by
  obtain ⟨M,hM,h⟩ := regularized_uniform_rate t
  refine ⟨M,hM,?_⟩
  intro a ha ha5 x hx
  rw [scaled_cutoff_sine_eq a t x ha (by linarith),← regularized_I_im t a,
    ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  exact (show |(regularized t (scaledBase x) a).im-(regularized t Complex.I a).im| ≤
    ‖regularized t (scaledBase x) a-regularized t Complex.I a‖ from by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm
        (regularized t (scaledBase x) a-regularized t Complex.I a)).trans (h a ha.le ha5 x hx)

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderCutoffRate
