import Foundation.RiemannRealOrderRealUniform
import Foundation.RiemannThetaDerivativeBounds
import Mathlib.Analysis.Complex.Liouville

/-! Actual half-line cubic densities and shifted arithmetic-kernel bounds
for their derivatives. No Fourier asymptotic or zero conclusion is asserted. -/
noncomputable section
open MeasureTheory Set Filter Metric Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderCubicDensity
open RiemannThetaComplexKernel RiemannThetaDerivativeBounds RiemannQuarticKernel

def density (t : ℝ) (z : ℂ) : ℂ := Complex.exp ((t : ℂ)*z^3)*kernelComplex z

private theorem disk_geometry (u : ℝ) (hu : 2 ≤ u) (w : ℂ)
    (hw : w ∈ closedBall (u : ℂ) (1/16)) :
    0 ≤ w.re ∧ w.re ≤ u+1 ∧ Real.exp (4*(u-1)) ≤ (Complex.exp (4*w)).re := by
  have hd : ‖w-(u : ℂ)‖ ≤ 1/16 := by simpa only [mem_closedBall,dist_eq_norm] using hw
  have hr := (Complex.abs_re_le_norm (w-(u : ℂ))).trans hd
  have hi := (Complex.abs_im_le_norm (w-(u : ℂ))).trans hd
  simp only [Complex.sub_re,Complex.ofReal_re] at hr
  simp only [Complex.sub_im,Complex.ofReal_im,sub_zero] at hi
  have hcos : 1/2 ≤ Real.cos (4*w.im) := by
    have hprod : 0 ≤ (1/16-w.im)*(1/16+w.im) :=
      mul_nonneg (by linarith [(abs_le.mp hi).2]) (by linarith [(abs_le.mp hi).1])
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := 4*w.im)]
  have he : 2*Real.exp (4*(u-1)) ≤ Real.exp (4*w.re) := by
    have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    calc
      _ = Real.exp (4*(u-1))*2 := by ring
      _ ≤ Real.exp (4*(u-1))*Real.exp 2 :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = Real.exp (4*(u-1)+2) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (4*w.re) := Real.exp_le_exp.mpr (by linarith [(abs_le.mp hr).1])
  have hE : (Complex.exp (4*w)).re = Real.exp (4*w.re)*Real.cos (4*w.im) := by
    simp [Complex.exp_re,Complex.mul_re,Complex.mul_im]
  refine ⟨by linarith [(abs_le.mp hr).1],by linarith [(abs_le.mp hr).2],?_⟩
  rw [hE]
  calc
    _ = (2*Real.exp (4*(u-1)))*(1/2) := by ring
    _ ≤ _ := mul_le_mul he hcos (by norm_num) (Real.exp_pos _).le

private theorem leading_upper (w : ℂ) (hw : 0 ≤ w.re) :
    ‖leading w‖ ≤ 44*Real.exp (9*w.re)*Real.exp (-Real.pi*(Complex.exp (4*w)).re) := by
  have h9 : ‖Complex.exp (9*w)‖ = Real.exp (9*w.re) := by simpa using norm_exp_scaled 9 w
  have h5 : ‖Complex.exp (5*w)‖ = Real.exp (5*w.re) := by simpa using norm_exp_scaled 5 w
  have he : ‖Complex.exp (-(Real.pi : ℂ)*Complex.exp (4*w))‖ =
      Real.exp (-Real.pi*(Complex.exp (4*w)).re) := by
    simpa only [Complex.ofReal_neg] using norm_exp_scaled (-Real.pi) (Complex.exp (4*w))
  have hc9 : ‖2*(Real.pi : ℂ)^2*Complex.exp (9*w)‖ = 2*Real.pi^2*Real.exp (9*w.re) := by
    simp only [norm_mul,norm_pow,norm_pi,h9,Complex.norm_ofNat]
  have hc5 : ‖3*(Real.pi : ℂ)*Complex.exp (5*w)‖ = 3*Real.pi*Real.exp (5*w.re) := by
    simp only [norm_mul,norm_pi,h5,Complex.norm_ofNat]
  have h59 : Real.exp (5*w.re) ≤ Real.exp (9*w.re) := Real.exp_le_exp.mpr (by linarith)
  have hpi2 : Real.pi^2 ≤ 16 := by
    have h := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_four.le 2
    norm_num at h
    exact h
  have hc : 2*Real.pi^2+3*Real.pi ≤ 44 := by linarith [Real.pi_lt_four]
  have hb : ‖2*(Real.pi : ℂ)^2*Complex.exp (9*w)-3*(Real.pi : ℂ)*Complex.exp (5*w)‖ ≤
      44*Real.exp (9*w.re) := by
    calc
      _ ≤ 2*Real.pi^2*Real.exp (9*w.re)+3*Real.pi*Real.exp (5*w.re) := by
        have ht := norm_sub_le
          (2*(Real.pi : ℂ)^2*Complex.exp (9*w)) (3*(Real.pi : ℂ)*Complex.exp (5*w))
        rw [hc9,hc5] at ht
        exact ht
      _ ≤ (2*Real.pi^2+3*Real.pi)*Real.exp (9*w.re) := by
        nlinarith [mul_le_mul_of_nonneg_left h59 (show 0 ≤ 3*Real.pi by positivity)]
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
  rw [leading,norm_mul,he]
  exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le

theorem kernel_disk_shift_bound (u : ℝ) (hu : 2 ≤ u) (w : ℂ)
    (hw : w ∈ closedBall (u : ℂ) (1/16)) :
    ‖kernelComplex w‖ ≤ 88*Real.exp 18*kernel (u-1) := by
  have hg := disk_geometry u hu w hw
  have hE1 : 1 ≤ (Complex.exp (4*w)).re :=
    (Real.one_le_exp_iff.mpr (by linarith : 0 ≤ 4*(u-1))).trans hg.2.2
  have hr := kernel_relative_eighth w hg.1 hE1
  have ht := norm_add_le (kernelComplex w-leading w) (leading w)
  rw [sub_add_cancel] at ht
  have hK : ‖kernelComplex w‖ ≤ 2*‖leading w‖ := by nlinarith [norm_nonneg (leading w)]
  have h9 : Real.exp (9*w.re) ≤ Real.exp 18*Real.exp (9*(u-1)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [hg.2.1])
  have hdec : Real.exp (-Real.pi*(Complex.exp (4*w)).re) ≤
      Real.exp (-Real.pi*Real.exp (4*(u-1))) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hg.2.2,Real.pi_pos]
  have hv0 : 0 ≤ u-1 := by linarith
  have hEr : (Complex.exp (4*((u-1 : ℝ) : ℂ))).re = Real.exp (4*(u-1)) := by
    simp [Complex.exp_re,Complex.mul_re,Complex.mul_im]
  have hlo := kernel_norm_lower ((u-1 : ℝ) : ℂ) (by simpa using hv0)
    (by rw [hEr]; exact Real.one_le_exp_iff.mpr (by linarith))
  rw [kernelComplex_real,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (kernel_pos (u-1) hv0)] at hlo
  simp only [Complex.ofReal_re,hEr] at hlo
  have hbase : Real.exp (9*(u-1))*Real.exp (-Real.pi*Real.exp (4*(u-1))) ≤ kernel (u-1) := by
    have hc : (1 : ℝ) ≤ (21/8)*Real.pi := by linarith [Real.pi_gt_three]
    calc
      _ ≤ ((21/8)*Real.pi)*(Real.exp (9*(u-1))*
          Real.exp (-Real.pi*Real.exp (4*(u-1)))) :=
        le_mul_of_one_le_left (by positivity) hc
      _ ≤ _ := by nlinarith [hlo]
  calc
    _ ≤ 2*(44*Real.exp (9*w.re)*Real.exp (-Real.pi*(Complex.exp (4*w)).re)) :=
      hK.trans (mul_le_mul_of_nonneg_left (leading_upper w hg.1) (by norm_num))
    _ ≤ 88*(Real.exp 18*Real.exp (9*(u-1)))*
        Real.exp (-Real.pi*Real.exp (4*(u-1))) := by
      have hm := mul_le_mul h9 hdec (Real.exp_pos _).le
        (by positivity : 0 ≤ Real.exp 18*Real.exp (9*(u-1)))
      nlinarith [hm]
    _ = (88*Real.exp 18)*(Real.exp (9*(u-1))*
        Real.exp (-Real.pi*Real.exp (4*(u-1)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbase (by positivity)

theorem density_analyticAt (t : ℝ) (z : ℂ) (hz : 0 < (Complex.exp (4*z)).re) :
    AnalyticAt ℂ (density t) z :=
  (analyticAt_const.mul (analyticAt_id.pow 3)).cexp.mul (kernelComplex_analyticAt z hz)

theorem density_real_agrees (t u : ℝ) (hu : 0 ≤ u) :
    density t (u : ℂ) = (RiemannRealOrderFlow.weighted (3/2) 0 t 0 u : ℂ) := by
  simpa only [density,Nat.cast_ofNat] using
    (RiemannRealOrderBranchObstruction.positive_half_line_density_extension 3 t).2 u hu

theorem density_disk_bound (t u : ℝ) (hu : 2 ≤ u) (w : ℂ)
    (hw : w ∈ closedBall (u : ℂ) (1/16)) :
    ‖density t w‖ ≤ 88*Real.exp 18*RiemannEvenDomain.weighted 2 0 (27*|t|) 0 (u-1) := by
  have hd : ‖w-(u : ℂ)‖ ≤ 1/16 := by simpa only [mem_closedBall,dist_eq_norm] using hw
  have hnormu : ‖(u : ℂ)‖ = u := by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ u)]
  have hn := norm_add_le (w-(u : ℂ)) (u : ℂ)
  rw [sub_add_cancel,hnormu] at hn
  have hwu : ‖w‖ ≤ u+1 := by linarith
  have hp3 := pow_le_pow_left₀ (by linarith : 0 ≤ u+1)
    (by linarith : u+1 ≤ 3*(u-1)) 3
  have hp34 : (u-1)^3 ≤ (u-1)^4 := by
    have h := mul_nonneg (by linarith : 0 ≤ u-2) (pow_nonneg (by linarith : 0 ≤ u-1) 3)
    nlinarith
  have hpoly : (u+1)^3 ≤ 27*(u-1)^4 := by nlinarith
  have he : ‖Complex.exp ((t : ℂ)*w^3)‖ ≤ Real.exp ((27*|t|)*(u-1)^4) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hr := Complex.re_le_norm ((t : ℂ)*w^3)
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs] at hr
    have hpow := pow_le_pow_left₀ (norm_nonneg w) hwu 3
    have hm := mul_le_mul_of_nonneg_left (hpow.trans hpoly) (abs_nonneg t)
    nlinarith
  rw [density,norm_mul]
  calc
    _ ≤ Real.exp ((27*|t|)*(u-1)^4)*(88*Real.exp 18*kernel (u-1)) :=
      mul_le_mul he (kernel_disk_shift_bound u hu w hw) (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by
      simp only [RiemannEvenDomain.weighted,pow_zero,one_mul,zero_mul,add_zero]
      ring

theorem density_iteratedDeriv_bound (n : ℕ) (t u : ℝ) (hu : 2 ≤ u) :
    ‖iteratedDeriv n (density t) (u : ℂ)‖ ≤
      n.factorial*(88*Real.exp 18*RiemannEvenDomain.weighted 2 0 (27*|t|) 0 (u-1))/(1/16)^n := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by norm_num)
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball (u : ℂ) (by norm_num : (1/16 : ℝ) ≠ 0)]
    intro w hw
    exact (density_analyticAt t w ((Real.exp_pos _).trans_le
      (disk_geometry u hu w hw).2.2)).differentiableAt.differentiableWithinAt
  · intro w hw
    exact density_disk_bound t u hu w (sphere_subset_closedBall hw)

theorem density_iteratedDeriv_continuous (n : ℕ) (t : ℝ) :
    Continuous (fun u : ℝ => iteratedDeriv n (density t) (u : ℂ)) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  have he : 0 < (Complex.exp (4*(u : ℂ))).re := by
    simpa [Complex.exp_re,Complex.mul_re,Complex.mul_im] using Real.exp_pos (4*u)
  have ha : AnalyticAt ℂ (iteratedDeriv n (density t)) (u : ℂ) := by
    rw [iteratedDeriv_eq_iterate]
    exact (density_analyticAt t (u : ℂ) he).iterated_deriv n
  exact ha.continuousAt.comp Complex.continuous_ofReal.continuousAt

theorem density_profile_hasDerivAt (n : ℕ) (t u : ℝ) :
    HasDerivAt (fun v : ℝ => iteratedDeriv n (density t) (v : ℂ))
      (iteratedDeriv (n+1) (density t) (u : ℂ)) u := by
  have he : 0 < (Complex.exp (4*(u : ℂ))).re := by
    simpa [Complex.exp_re,Complex.mul_re,Complex.mul_im] using Real.exp_pos (4*u)
  have ha : AnalyticAt ℂ (iteratedDeriv n (density t)) (u : ℂ) := by
    rw [iteratedDeriv_eq_iterate]
    exact (density_analyticAt t (u : ℂ) he).iterated_deriv n
  have hd : HasDerivAt (iteratedDeriv n (density t))
      (iteratedDeriv (n+1) (density t) (u : ℂ)) (u : ℂ) := by
    rw [iteratedDeriv_succ]
    exact ha.differentiableAt.hasDerivAt
  exact hd.comp_ofReal

theorem density_iteratedDeriv_integrable (n : ℕ) (t : ℝ) :
    Integrable (fun u : ℝ => iteratedDeriv n (density t) (u : ℂ)) RiemannQuarticFlow.halfLine := by
  have hc := density_iteratedDeriv_continuous n t
  have hweight : IntegrableOn (RiemannEvenDomain.weighted 2 0 (27*|t|) 0) (Ici (0 : ℝ)) :=
    RiemannEvenDomain.weighted_integrable 2 0 (27*|t|) 0
  have htrans := (measurePreserving_add_right (volume : Measure ℝ) (-1 : ℝ)).integrableOn_comp_preimage
    ((MeasurableEquiv.addRight (-1 : ℝ)).measurableEmbedding)
    (f := RiemannEvenDomain.weighted 2 0 (27*|t|) 0) (s := Ici (0 : ℝ))
  have hset : (fun u : ℝ => u+(-1)) ⁻¹' Ici 0 = Ici 1 := by
    ext u
    simp only [mem_preimage,mem_Ici]
    constructor <;> intro h <;> linarith
  have hshift : IntegrableOn (fun u : ℝ => RiemannEvenDomain.weighted 2 0 (27*|t|) 0 (u-1)) (Ici 1) := by
    have h := htrans.mpr hweight
    rw [hset] at h
    change IntegrableOn (fun u : ℝ => RiemannEvenDomain.weighted 2 0 (27*|t|) 0 (u+(-1))) (Ici 1) at h
    simpa only [Function.comp_apply,sub_eq_add_neg] using h
  have hmajor : IntegrableOn (fun u : ℝ => n.factorial*
      (88*Real.exp 18*RiemannEvenDomain.weighted 2 0 (27*|t|) 0 (u-1))/(1/16)^n) (Ici 2) :=
    (((hshift.mono_set (Ici_subset_Ici.mpr (by norm_num : (1 : ℝ) ≤ 2))).const_mul
      (88*Real.exp 18)).const_mul (n.factorial : ℝ)).div_const ((1/16 : ℝ)^n)
  have htail : IntegrableOn (fun u : ℝ => iteratedDeriv n (density t) (u : ℂ)) (Ici 2) := by
    apply hmajor.mono' hc.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    exact density_iteratedDeriv_bound n t u hu
  have hcompact : IntegrableOn (fun u : ℝ => iteratedDeriv n (density t) (u : ℂ)) (Icc 0 2) :=
    hc.integrableOn_Icc
  have hsub : Ici (0 : ℝ) ⊆ Icc 0 2 ∪ Ici 2 := by
    intro u hu
    rcases le_total u 2 with hle | hge
    · exact Or.inl ⟨hu,hle⟩
    · exact Or.inr hge
  exact (hcompact.union htail).mono_set hsub

theorem density_iteratedDeriv_tendsto_zero (n : ℕ) (t : ℝ) :
    Tendsto (fun u : ℝ => iteratedDeriv n (density t) (u : ℂ)) atTop (𝓝 0) := by
  have hexp : Tendsto (fun u : ℝ => Real.exp (-u)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hweight : Tendsto (RiemannEvenDomain.weighted 2 0 (27*|t|) 0) atTop (𝓝 0) :=
    (RiemannEvenDomain.weighted_isBigO 2 0 (27*|t|) 0).trans_tendsto hexp
  have hshift : Tendsto (fun u : ℝ => u-1) atTop atTop := by
    simpa only [sub_eq_add_neg,id_eq] using
      (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id)
  have hmajor := (((hweight.comp hshift).const_mul (88*Real.exp 18)).const_mul
    (n.factorial : ℝ)).div_const ((1/16 : ℝ)^n)
  simp only [mul_zero,zero_div] at hmajor
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall fun u => norm_nonneg _)
    ((eventually_ge_atTop (2 : ℝ)).mono fun u hu => density_iteratedDeriv_bound n t u hu)
    hmajor

theorem actual_flow_density_integral (t : ℝ) (z : ℂ) :
    Integrable (fun u : ℝ => density t (u : ℂ)*Complex.cos ((u : ℂ)*z))
      RiemannQuarticFlow.halfLine ∧
    RiemannRealOrderFlow.flow (3/2) t z =
      ∫ u : ℝ, density t (u : ℂ)*Complex.cos ((u : ℂ)*z) ∂RiemannQuarticFlow.halfLine := by
  have he : (fun u : ℝ => (RiemannRealOrderFlow.weighted (3/2) 0 t 0 u : ℂ)*
      Complex.cos ((u : ℂ)*z)) =ᵐ[RiemannQuarticFlow.halfLine]
      (fun u : ℝ => density t (u : ℂ)*Complex.cos ((u : ℂ)*z)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    rw [density_real_agrees t u hu]
  refine ⟨(RiemannRealOrderFlow.cosine_integrable (3/2) (by norm_num) t z).congr he,?_⟩
  rw [RiemannRealOrderFlow.flow_eq_cosine_integral (3/2) (by norm_num)]
  exact integral_congr_ae he

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderCubicDensity
