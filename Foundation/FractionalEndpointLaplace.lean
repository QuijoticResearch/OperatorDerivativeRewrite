import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! Absolutely convergent exponential cutoffs for fractional endpoint singularities.
The damping parameter is genuinely complex, on its open right half-plane. -/
noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FractionalEndpointLaplace

def profile (b : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  (u ^ (b-1) : ℝ) * Complex.exp (-z * (u : ℂ))

def transform (b : ℝ) (z : ℂ) : ℂ := ∫ u : ℝ in Ioi 0, profile b z u

theorem majorant_integrable (b r : ℝ) (hb : 0 < b) (hr : 0 < r) :
    IntegrableOn (fun u : ℝ => u^(b-1)*Real.exp (-r*u)) (Ioi 0) := by
  simpa using integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := 1) (s := b-1) (by linarith) zero_lt_one hr

theorem profile_norm (b : ℝ) (z : ℂ) (u : ℝ) (hu : 0 < u) :
    ‖profile b z u‖ = u^(b-1)*Real.exp (-z.re*u) := by
  simp [profile,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hu _),Complex.norm_exp,Complex.mul_re]

theorem profile_integrable (b : ℝ) (hb : 0 < b) (z : ℂ) (hz : 0 < z.re) :
    IntegrableOn (profile b z) (Ioi 0) := by
  refine (majorant_integrable b z.re hb hz).mono' ?_ ?_
  · have hm : Measurable (profile b z) := by unfold profile; fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (profile_norm b z u hu).le

theorem profile_hasDerivAt (b u : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => profile b w u) (-(u : ℂ)*profile b z u) z := by
  convert ((((hasDerivAt_id z).neg.mul_const (u : ℂ)).cexp).const_mul
    ((u^(b-1) : ℝ) : ℂ)) using 1 <;>
      simp [profile,Pi.neg_apply,id_eq,neg_mul,mul_comm,mul_assoc]

theorem transform_hasDerivAt (b : ℝ) (hb : 0 < b) (z : ℂ) (hz : 0 < z.re) :
    HasDerivAt (transform b)
      (∫ u : ℝ in Ioi 0, -(u : ℂ)*profile b z u) z := by
  let S : Set ℂ := {w | z.re/2 < w.re}
  have hS : S ∈ 𝓝 z :=
    continuous_re.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by linarith))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ))) (F := fun w u => profile b w u)
    (F' := fun w u => -(u : ℂ)*profile b w u) hS ?_
    (profile_integrable b hb z hz) ?_
    (bound := fun u : ℝ => u^b*Real.exp (-(z.re/2)*u)) ?_ ?_ ?_).2
  · filter_upwards [hS] with w hw
    exact (profile_integrable b hb w (by change z.re/2 < w.re at hw; linarith)).aestronglyMeasurable
  · exact ((profile_integrable b hb z hz).aestronglyMeasurable.mul
      (by fun_prop : AEStronglyMeasurable (fun u : ℝ => -(u : ℂ))
        (volume.restrict (Ioi (0 : ℝ))))).congr (by filter_upwards with u; dsimp; ring)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w hw
    change 0 < u at hu
    rw [norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu,
      profile_norm b w u hu,← mul_assoc]
    rw [show u*u^(b-1)=u^b by
      calc u*u^(b-1) = u^((1 : ℝ)+(b-1)) := by
             rw [Real.rpow_add hu,Real.rpow_one]
           _ = u^b := by congr 1; ring]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hu.le _)
    apply Real.exp_le_exp.mpr
    change z.re/2 < w.re at hw
    nlinarith
  · exact (majorant_integrable (b+1) (z.re/2) (by linarith) (by linarith)).congr
      (Eventually.of_forall fun u => by dsimp; congr 2 <;> ring)
  · exact Eventually.of_forall fun u w _ => profile_hasDerivAt b u w

theorem transform_analytic (b : ℝ) (hb : 0 < b) :
    AnalyticOnNhd ℂ (transform b) {z | 0 < z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const continuous_re)
  intro z hz
  exact (transform_hasDerivAt b hb z hz).differentiableAt.differentiableWithinAt

theorem inverse_slitPlane (z : ℂ) (hz : 0 < z.re) : z⁻¹ ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  rw [Complex.inv_re]
  exact div_pos hz (Complex.normSq_pos.mpr (by intro h; simpa [h] using hz))

theorem transform_eq_gamma (b : ℝ) (hb : 0 < b) (z : ℂ) (hz : 0 < z.re) :
    transform b z = (z⁻¹)^(b : ℂ)*Complex.Gamma (b : ℂ) := by
  have hg : AnalyticOnNhd ℂ (fun w : ℂ => (w⁻¹)^(b : ℂ)*Complex.Gamma (b : ℂ))
      {w | 0 < w.re} := by
    intro w hw
    have hn : w ≠ 0 := by intro h; simpa [h] using hw
    exact (((analyticAt_id.inv hn).cpow analyticAt_const (inverse_slitPlane w hw)).mul
      analyticAt_const)
  have he (r : ℝ) (hr : 0 < r) :
      transform b (r : ℂ)=((r : ℂ)⁻¹)^(b : ℂ)*Complex.Gamma (b : ℂ) := by
    rw [transform]
    convert Complex.integral_cpow_mul_exp_neg_mul_Ioi
      (a := (b : ℂ)) (r := r) (by simpa using hb) hr using 1
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      dsimp only [profile]
      rw [Complex.ofReal_cpow hu.le]
      push_cast
      congr 2 <;> ring
    · simp only [one_div]
  have hseq : Tendsto (fun n : ℕ => ((1+1/((n : ℝ)+1) : ℝ) : ℂ)) atTop (𝓝 1) := by
    have hr : Tendsto (fun n : ℕ => (1 : ℝ)+1/((n : ℝ)+1)) atTop (𝓝 (1+0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    have h := Complex.continuous_ofReal.continuousAt.tendsto.comp hr
    simpa [Function.comp_def] using h
  have hcl : (1 : ℂ) ∈ closure
      ({w | transform b w=(w⁻¹)^(b : ℂ)*Complex.Gamma (b : ℂ)} \ {1}) := by
    apply mem_closure_of_tendsto hseq
    filter_upwards with n
    refine ⟨he _ (by positivity),?_⟩
    change ((1+1/((n : ℝ)+1) : ℝ) : ℂ) ≠ 1
    exact_mod_cast (ne_of_gt (by
      have hp : (0 : ℝ)<1/((n : ℝ)+1) := by positivity
      linarith : (1 : ℝ)<1+1/((n : ℝ)+1)))
  exact (transform_analytic b hb).eqOn_of_preconnected_of_mem_closure hg
    (convex_halfSpace_re_gt 0).isPreconnected (by simp) hcl hz

theorem cutoff_fourier_eq (b : ℝ) (hb : 0 < b) (x : ℝ) :
    (∫ u : ℝ in Ioi 0, (u^(b-1)*Real.exp (-u) : ℝ)*
      Complex.exp (Complex.I*(x : ℂ)*(u : ℂ))) =
        ((1-Complex.I*(x : ℂ))⁻¹)^(b : ℂ)*Complex.Gamma (b : ℂ) := by
  rw [← transform_eq_gamma b hb (1-Complex.I*(x : ℂ)) (by simp)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  simp only [profile,Complex.ofReal_mul,Complex.ofReal_exp,Complex.ofReal_neg]
  rw [mul_assoc,← Complex.exp_add]
  congr 2
  ring

theorem positive_scale_cpow (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : z ≠ 0) (b : ℝ) :
    ((r : ℂ)*z)^(b : ℂ) = (r^b : ℝ)*z^(b : ℂ) := by
  rw [Complex.ofReal_cpow hr.le,Complex.cpow_def_of_ne_zero
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') hz),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
    Complex.cpow_def_of_ne_zero hz,Complex.log_ofReal_mul hr hz,add_mul,Complex.exp_add,
    Complex.ofReal_log hr.le]

theorem scaled_transform_limit (b : ℝ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => (x^b : ℝ)*transform b (1-Complex.I*(x : ℂ))) atTop
      (𝓝 (Complex.I^(b : ℂ)*Complex.Gamma (b : ℂ))) := by
  have hinv : Tendsto (fun x : ℝ => ((x⁻¹ : ℝ) : ℂ)-Complex.I) atTop (𝓝 (-Complex.I)) := by
    simpa using (Complex.continuous_ofReal.continuousAt.tendsto.comp
      tendsto_inv_atTop_zero).sub_const Complex.I
  have hbase : Tendsto (fun x : ℝ => (((x⁻¹ : ℝ) : ℂ)-Complex.I)⁻¹) atTop (𝓝 Complex.I) := by
    simpa using hinv.inv₀ (by simp)
  have hp := ((continuousAt_cpow_const
    (a := Complex.I) (b := (b : ℂ)) (by simp [Complex.mem_slitPlane_iff])).tendsto.comp hbase).mul_const
      (Complex.Gamma (b : ℂ))
  apply hp.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  dsimp only [Function.comp_def]
  rw [transform_eq_gamma b hb _ (by simp),← mul_assoc,
    ← positive_scale_cpow x hx _ (inv_ne_zero (by
      intro h
      have := congrArg Complex.re h
      simp at this)) b]
  congr 1
  congr 1
  rw [Complex.ofReal_inv]
  field_simp [Complex.ofReal_ne_zero.mpr hx.ne']
  <;> ring

theorem scaled_sine_limit (b : ℝ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => x^b *
      (∫ u : ℝ in Ioi 0, u^(b-1)*Real.exp (-u)*Real.sin (x*u))) atTop
      (𝓝 (Real.Gamma b*Real.sin (Real.pi*b/2))) := by
  have h := Complex.continuous_im.continuousAt.tendsto.comp (scaled_transform_limit b hb)
  have hi (x : ℝ) : (transform b (1-Complex.I*(x : ℂ))).im =
      ∫ u : ℝ in Ioi 0, u^(b-1)*Real.exp (-u)*Real.sin (x*u) := by
    calc
      _ = ∫ u : ℝ in Ioi 0, (profile b (1-Complex.I*(x : ℂ)) u).im :=
        (integral_im (𝕜 := ℂ) (profile_integrable b hb _ (by simp))).symm
      _ = _ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u _
        simp [profile,Complex.mul_re,Complex.mul_im,Complex.exp_im]
        ring
  have hv : (Complex.I^(b : ℂ)*Complex.Gamma (b : ℂ)).im =
      Real.Gamma b*Real.sin (Real.pi*b/2) := by
    rw [Complex.Gamma_ofReal,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,zero_add,Complex.cpow_ofReal_im]
    simp [Complex.arg_I,mul_comm,mul_div_assoc]
  simpa only [Function.comp_def,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,add_zero,hi,hv] using h

theorem sine_coefficient_pos (b : ℝ) (hb : 0 < b) (hb2 : b < 2) :
    0 < Real.Gamma b*Real.sin (Real.pi*b/2) := by
  apply mul_pos (Real.Gamma_pos_of_pos hb)
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · nlinarith [Real.pi_pos]

end OperatorDerivativeRewrite.Foundation.FractionalEndpointLaplace
