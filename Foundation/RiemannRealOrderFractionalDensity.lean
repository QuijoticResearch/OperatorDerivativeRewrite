import Foundation.RiemannRealOrderCubicDensity
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! A principal-power germ for the actual positive-axis density. Analyticity
is asserted away from the power cut and the arithmetic kernel's strip boundary.
Derivative tail bounds are uniform in the real order on [0,2]; no endpoint
regularity or derivative integrability at zero is inferred. -/
noncomputable section
open MeasureTheory Set Filter Metric Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderFractionalDensity
open RiemannThetaComplexKernel RiemannQuarticKernel

def density (a t : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((t : ℂ)*z^((2*a : ℝ) : ℂ))*kernelComplex z

def tailMajorant (n : ℕ) (t u : ℝ) : ℝ :=
  n.factorial*(88*Real.exp 18*RiemannEvenDomain.weighted 2 0 (81*|t|) 0 (u-1))/(1/16)^n

theorem density_real_agrees (a t u : ℝ) (hu : 0 ≤ u) :
    density a t (u : ℂ) = (RiemannRealOrderFlow.weighted a 0 t 0 u : ℂ) := by
  simp only [density,RiemannRealOrderFlow.weighted,pow_zero,one_mul,zero_mul,add_zero,
    abs_of_nonneg hu]
  rw [← Complex.ofReal_cpow hu,← Complex.ofReal_mul,← Complex.ofReal_exp,
    kernelComplex_real,← Complex.ofReal_mul]

theorem density_analyticAt (a t : ℝ) (z : ℂ) (hz : 0 < z.re)
    (hK : 0 < (Complex.exp (4*z)).re) : AnalyticAt ℂ (density a t) z :=
  (analyticAt_const.mul (analyticAt_id.cpow analyticAt_const
    (Complex.mem_slitPlane_iff.mpr (Or.inl hz)))).cexp.mul
      (kernelComplex_analyticAt z hK)

private theorem disk_domain (u : ℝ) (hu : 2 ≤ u) (w : ℂ)
    (hw : w ∈ closedBall (u : ℂ) (1/16)) :
    0 < w.re ∧ 0 < (Complex.exp (4*w)).re := by
  have hd : ‖w-(u : ℂ)‖ ≤ 1/16 := by simpa only [mem_closedBall,dist_eq_norm] using hw
  have hr := (Complex.abs_re_le_norm (w-(u : ℂ))).trans hd
  have hi := (Complex.abs_im_le_norm (w-(u : ℂ))).trans hd
  simp only [Complex.sub_re,Complex.ofReal_re] at hr
  simp only [Complex.sub_im,Complex.ofReal_im,sub_zero] at hi
  refine ⟨by linarith [(abs_le.mp hr).1],?_⟩
  rw [Complex.exp_re]
  apply mul_pos (Real.exp_pos _)
  apply Real.cos_pos_of_mem_Ioo
  norm_num [Complex.mul_im]
  constructor <;> linarith [(abs_le.mp hi).1,(abs_le.mp hi).2,Real.pi_gt_three]

theorem power_disk_bound (a u : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2) (hu : 2 ≤ u) (w : ℂ)
    (hw : w ∈ closedBall (u : ℂ) (1/16)) :
    ‖w^((2*a : ℝ) : ℂ)‖ ≤ 81*(u-1)^4 := by
  have hd : ‖w-(u : ℂ)‖ ≤ 1/16 := by simpa only [mem_closedBall,dist_eq_norm] using hw
  have hn : ‖w‖ ≤ u+1 := by
    have ht := norm_add_le (w-(u : ℂ)) (u : ℂ)
    rw [sub_add_cancel,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ u)] at ht
    linarith
  calc
    _ = ‖w‖^(2*a) := Complex.norm_cpow_real w (2*a)
    _ ≤ (u+1)^(2*a) := Real.rpow_le_rpow (norm_nonneg w) hn (by positivity)
    _ ≤ (u+1)^(4 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = (u+1)^4 := by norm_num
    _ ≤ (3*(u-1))^4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
    _ = _ := by ring

theorem density_disk_bound (a t u : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2) (hu : 2 ≤ u) (w : ℂ)
    (hw : w ∈ closedBall (u : ℂ) (1/16)) :
    ‖density a t w‖ ≤ 88*Real.exp 18*RiemannEvenDomain.weighted 2 0 (81*|t|) 0 (u-1) := by
  have he : ‖Complex.exp ((t : ℂ)*w^((2*a : ℝ) : ℂ))‖ ≤
      Real.exp ((81*|t|)*(u-1)^4) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hr := Complex.re_le_norm ((t : ℂ)*w^((2*a : ℝ) : ℂ))
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs] at hr
    have hm := mul_le_mul_of_nonneg_left (power_disk_bound a u ha ha2 hu w hw) (abs_nonneg t)
    nlinarith
  rw [density,norm_mul]
  calc
    _ ≤ Real.exp ((81*|t|)*(u-1)^4)*(88*Real.exp 18*kernel (u-1)) :=
      mul_le_mul he (RiemannRealOrderCubicDensity.kernel_disk_shift_bound u hu w hw)
        (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by
      simp only [RiemannEvenDomain.weighted,pow_zero,one_mul,zero_mul,add_zero]
      ring

theorem density_iteratedDeriv_bound (n : ℕ) (a t u : ℝ)
    (ha : 0 ≤ a) (ha2 : a ≤ 2) (hu : 2 ≤ u) :
    ‖iteratedDeriv n (density a t) (u : ℂ)‖ ≤ tailMajorant n t u := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by norm_num)
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball (u : ℂ) (by norm_num : (1/16 : ℝ) ≠ 0)]
    intro w hw
    have hd := disk_domain u hu w hw
    exact (density_analyticAt a t w hd.1 hd.2).differentiableAt.differentiableWithinAt
  · intro w hw
    exact density_disk_bound a t u ha ha2 hu w (sphere_subset_closedBall hw)

theorem density_iteratedDeriv_continuousOn (n : ℕ) (a t : ℝ) :
    ContinuousOn (fun u : ℝ => iteratedDeriv n (density a t) (u : ℂ)) (Ioi 0) := by
  intro u hu
  have he : 0 < (Complex.exp (4*(u : ℂ))).re := by
    simpa [Complex.exp_re,Complex.mul_re,Complex.mul_im] using Real.exp_pos (4*u)
  have ha : AnalyticAt ℂ (iteratedDeriv n (density a t)) (u : ℂ) := by
    rw [iteratedDeriv_eq_iterate]
    exact (density_analyticAt a t (u : ℂ) hu he).iterated_deriv n
  exact (ha.continuousAt.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt

theorem density_profile_hasDerivAt (n : ℕ) (a t u : ℝ) (hu : 0 < u) :
    HasDerivAt (fun v : ℝ => iteratedDeriv n (density a t) (v : ℂ))
      (iteratedDeriv (n+1) (density a t) (u : ℂ)) u := by
  have he : 0 < (Complex.exp (4*(u : ℂ))).re := by
    simpa [Complex.exp_re,Complex.mul_re,Complex.mul_im] using Real.exp_pos (4*u)
  have han : AnalyticAt ℂ (iteratedDeriv n (density a t)) (u : ℂ) := by
    rw [iteratedDeriv_eq_iterate]
    exact (density_analyticAt a t (u : ℂ) hu he).iterated_deriv n
  have hd : HasDerivAt (iteratedDeriv n (density a t))
      (iteratedDeriv (n+1) (density a t) (u : ℂ)) (u : ℂ) := by
    rw [iteratedDeriv_succ]
    exact han.differentiableAt.hasDerivAt
  exact hd.comp_ofReal

theorem tailMajorant_integrable (n : ℕ) (t : ℝ) :
    IntegrableOn (tailMajorant n t) (Ici 2) := by
  have hweight : IntegrableOn (RiemannEvenDomain.weighted 2 0 (81*|t|) 0) (Ici (0 : ℝ)) :=
    RiemannEvenDomain.weighted_integrable 2 0 (81*|t|) 0
  have htrans := (measurePreserving_add_right (volume : Measure ℝ) (-1 : ℝ)).integrableOn_comp_preimage
    ((MeasurableEquiv.addRight (-1 : ℝ)).measurableEmbedding)
    (f := RiemannEvenDomain.weighted 2 0 (81*|t|) 0) (s := Ici (0 : ℝ))
  have hset : (fun u : ℝ => u+(-1)) ⁻¹' Ici 0 = Ici 1 := by
    ext u
    simp only [mem_preimage,mem_Ici]
    constructor <;> intro h <;> linarith
  have hshift : IntegrableOn (fun u : ℝ => RiemannEvenDomain.weighted 2 0 (81*|t|) 0 (u-1)) (Ici 1) := by
    have h := htrans.mpr hweight
    rw [hset] at h
    change IntegrableOn (fun u : ℝ => RiemannEvenDomain.weighted 2 0 (81*|t|) 0 (u+(-1))) (Ici 1) at h
    simpa only [Function.comp_apply,sub_eq_add_neg] using h
  exact (((hshift.mono_set (Ici_subset_Ici.mpr (by norm_num : (1 : ℝ) ≤ 2))).const_mul
    (88*Real.exp 18)).const_mul (n.factorial : ℝ)).div_const ((1/16 : ℝ)^n)

theorem density_iteratedDeriv_integrable_on_tail (n : ℕ) (a t : ℝ)
    (ha : 0 ≤ a) (ha2 : a ≤ 2) :
    IntegrableOn (fun u : ℝ => iteratedDeriv n (density a t) (u : ℂ)) (Ici 2) := by
  have hc := (density_iteratedDeriv_continuousOn n a t).mono
    (show Ici (2 : ℝ) ⊆ Ioi 0 by intro u hu; change 2 ≤ u at hu; exact lt_of_lt_of_le (by norm_num) hu)
  apply (tailMajorant_integrable n t).mono' (hc.aestronglyMeasurable measurableSet_Ici)
  filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
  exact density_iteratedDeriv_bound n a t u ha ha2 hu

theorem tailMajorant_tendsto_zero (n : ℕ) (t : ℝ) :
    Tendsto (tailMajorant n t) atTop (𝓝 0) := by
  have hexp : Tendsto (fun u : ℝ => Real.exp (-u)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hweight : Tendsto (RiemannEvenDomain.weighted 2 0 (81*|t|) 0) atTop (𝓝 0) :=
    (RiemannEvenDomain.weighted_isBigO 2 0 (81*|t|) 0).trans_tendsto hexp
  have hshift : Tendsto (fun u : ℝ => u-1) atTop atTop := by
    simpa only [sub_eq_add_neg,id_eq] using
      (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id)
  have h := (((hweight.comp hshift).const_mul (88*Real.exp 18)).const_mul
    (n.factorial : ℝ)).div_const ((1/16 : ℝ)^n)
  change Tendsto (fun u : ℝ => (n.factorial : ℝ)*
    (88*Real.exp 18*RiemannEvenDomain.weighted 2 0 (81*|t|) 0 (u-1))/(1/16)^n) atTop (𝓝 0)
  simpa only [Function.comp_def,mul_zero,zero_div] using h

theorem uniformly_vanishing_derivatives (n : ℕ) (t ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ u : ℝ in atTop, ∀ a : ℝ, 0 ≤ a → a ≤ 2 →
      ‖iteratedDeriv n (density a t) (u : ℂ)‖ < ε := by
  have h := (Metric.tendsto_nhds.mp (tailMajorant_tendsto_zero n t)) ε hε
  filter_upwards [h,eventually_ge_atTop (2 : ℝ)] with u he hu
  intro a ha ha2
  apply (density_iteratedDeriv_bound n a t u ha ha2 hu).trans_lt
  exact (le_abs_self _).trans_lt (by simpa [Real.dist_eq] using he)

theorem density_iteratedDeriv_tendsto_zero (n : ℕ) (a t : ℝ)
    (ha : 0 ≤ a) (ha2 : a ≤ 2) :
    Tendsto (fun u : ℝ => iteratedDeriv n (density a t) (u : ℂ)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall fun u => norm_nonneg _)
    ((eventually_ge_atTop (2 : ℝ)).mono fun u hu => density_iteratedDeriv_bound n a t u ha ha2 hu)
    (tailMajorant_tendsto_zero n t)

theorem density_iteratedDeriv_integrable_away_zero (n : ℕ) (a t δ : ℝ)
    (ha : 0 ≤ a) (ha2 : a ≤ 2) (hδ : 0 < δ) :
    IntegrableOn (fun u : ℝ => iteratedDeriv n (density a t) (u : ℂ)) (Ici δ) := by
  have hc : ContinuousOn (fun u : ℝ => iteratedDeriv n (density a t) (u : ℂ)) (Icc δ 2) :=
    (density_iteratedDeriv_continuousOn n a t).mono
      (by intro u hu; exact lt_of_lt_of_le hδ hu.1)
  have hsub : Ici δ ⊆ Icc δ 2 ∪ Ici 2 := by
    intro u hu
    rcases le_total u 2 with hle | hge
    · exact Or.inl ⟨hu,hle⟩
    · exact Or.inr hge
  exact (hc.integrableOn_Icc.union (density_iteratedDeriv_integrable_on_tail n a t ha ha2)).mono_set hsub

theorem uniformly_small_integral_tails (n : ℕ) (t ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ a : ℝ, 0 ≤ a → a ≤ 2 →
      (∫ u : ℝ in Ici R, ‖iteratedDeriv n (density a t) (u : ℂ)‖) < ε := by
  have hm : Tendsto (fun R : ℝ => ∫ u : ℝ in Ici R, tailMajorant n t u) atTop (𝓝 0) :=
    tendsto_integral_Ici_zero tendsto_id
  have he := (Metric.tendsto_nhds.mp hm) ε hε
  filter_upwards [he,eventually_ge_atTop (2 : ℝ)] with R hR hR2
  intro a ha ha2
  have hs : Ici R ⊆ Ici (2 : ℝ) := Ici_subset_Ici.mpr hR2
  have hd := (density_iteratedDeriv_integrable_on_tail n a t ha ha2).mono_set hs
  have hb := (tailMajorant_integrable n t).mono_set hs
  have hle : (∫ u : ℝ in Ici R, ‖iteratedDeriv n (density a t) (u : ℂ)‖) ≤
      ∫ u : ℝ in Ici R, tailMajorant n t u := by
    apply integral_mono_ae hd.norm hb
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    exact density_iteratedDeriv_bound n a t u ha ha2 (hR2.trans hu)
  exact hle.trans_lt ((le_abs_self _).trans_lt (by simpa [Real.dist_eq] using hR))

theorem actual_flow_density_integral (a t : ℝ) (ha : 0 ≤ a) (z : ℂ) :
    Integrable (fun u : ℝ => density a t (u : ℂ)*Complex.cos ((u : ℂ)*z))
      RiemannQuarticFlow.halfLine ∧
    RiemannRealOrderFlow.flow a t z =
      ∫ u : ℝ, density a t (u : ℂ)*Complex.cos ((u : ℂ)*z) ∂RiemannQuarticFlow.halfLine := by
  have he : (fun u : ℝ => (RiemannRealOrderFlow.weighted a 0 t 0 u : ℂ)*
      Complex.cos ((u : ℂ)*z)) =ᵐ[RiemannQuarticFlow.halfLine]
      (fun u : ℝ => density a t (u : ℂ)*Complex.cos ((u : ℂ)*z)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    rw [density_real_agrees a t u hu]
  refine ⟨(RiemannRealOrderFlow.cosine_integrable a ha t z).congr he,?_⟩
  rw [RiemannRealOrderFlow.flow_eq_cosine_integral a ha]
  exact integral_congr_ae he

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderFractionalDensity
