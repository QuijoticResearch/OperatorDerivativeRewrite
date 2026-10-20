import Foundation.RiemannRealOrderFlow
import Mathlib.MeasureTheory.Integral.DominatedConvergence
/-! Actual order continuity, proved by a common integrable Fourier error.
Locally uniform limits do not by themselves control zeros outside compacts. -/
noncomputable section
open MeasureTheory Set Metric Filter Complex
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderLimit
open RiemannRealOrderFlow
open RiemannQuarticFlow (halfLine)

theorem weighted_order_continuousAt (a : ℝ) (ha : 0 < a) (j : ℕ) (t R u : ℝ) :
    ContinuousAt (fun b : ℝ => weighted b j t R u) a := by
  have hp : ContinuousAt (fun b : ℝ => |u|^(2*b)) a :=
    (Real.continuousAt_const_rpow' (by positivity : 2*a ≠ 0)).comp
      (continuousAt_const.mul continuousAt_id)
  have hq := (hp.const_mul t).add_const (R*u)
  have he := Real.continuous_exp.continuousAt.comp hq
  simpa only [weighted,Function.comp_def] using
    (he.const_mul (u^j)).mul_const (RiemannQuarticKernel.kernel u)

theorem weighted_difference_integral_tendsto_zero (a : ℝ) (ha : 0 < a)
    (j : ℕ) (t R : ℝ) (hR : 0 ≤ R) :
    Tendsto (fun b : ℝ => ∫ u : ℝ, |weighted b j t R u-weighted a j t R u| ∂halfLine)
      (𝓝 a) (𝓝 0) := by
  obtain ⟨N,hN⟩ := exists_nat_gt a
  let T := max t 0
  let A := Real.exp (T+1+R*Real.sqrt R)
  let B := fun u : ℝ => 2*A*RiemannEvenDomain.weighted (N+2) j (T+1) 0 u
  have hnear : ∀ᶠ b : ℝ in 𝓝 a, 0 < b ∧ b < N := Ioo_mem_nhds ha hN
  have hmeas : ∀ᶠ b : ℝ in 𝓝 a,
      AEStronglyMeasurable (fun u : ℝ => |weighted b j t R u-weighted a j t R u|) halfLine := by
    filter_upwards [hnear] with b hb
    simpa only [Real.norm_eq_abs,Pi.sub_apply] using
      ((weighted_integrable b hb.1.le j t R).sub (weighted_integrable a ha.le j t R)).norm.aestronglyMeasurable
  have hbound : ∀ᶠ b : ℝ in 𝓝 a, ∀ᵐ u : ℝ ∂halfLine,
      ‖|weighted b j t R u-weighted a j t R u|‖ ≤ B u := by
    filter_upwards [hnear] with b hb
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    have h1 := weighted_tilt_bound b N j hb.1.le hb.2.le t T R u (le_max_right _ _) (le_max_left _ _) hR hu
    have h2 := weighted_tilt_bound a N j ha.le hN.le t T R u (le_max_right _ _) (le_max_left _ _) hR hu
    have htri := norm_sub_le (weighted b j t R u) (weighted a j t R u)
    simp only [Real.norm_eq_abs] at htri
    rw [abs_of_nonneg (weighted_nonneg b j t R u hu),abs_of_nonneg (weighted_nonneg a j t R u hu)] at htri
    rw [Real.norm_eq_abs,abs_abs]
    dsimp [B,A]
    linarith
  have hB : Integrable B halfLine :=
    (RiemannEvenDomain.weighted_integrable (N+2) j (T+1) 0).const_mul _
  have hlim : ∀ᵐ u : ℝ ∂halfLine,
      Tendsto (fun b : ℝ => |weighted b j t R u-weighted a j t R u|) (𝓝 a) (𝓝 (0 : ℝ)) := by
    filter_upwards with u
    have hc := ((weighted_order_continuousAt a ha j t R u).sub_const (weighted a j t R u)).abs
    simpa only [Pi.sub_apply,sub_self,abs_zero] using hc
  simpa only [integral_zero] using
    (tendsto_integral_filter_of_dominated_convergence B hmeas hbound hB hlim)

theorem jet_difference_bound (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (j : ℕ) (t R : ℝ) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖jet a j t z-jet b j t z‖ ≤
      ∫ u : ℝ, |weighted a j t R u-weighted b j t R u| ∂halfLine := by
  have hmajor : Integrable (fun u : ℝ => |weighted a j t R u-weighted b j t R u|) halfLine := by
    simpa only [Real.norm_eq_abs,Pi.sub_apply] using
      ((weighted_integrable a ha j t R).sub (weighted_integrable b hb j t R)).norm
  have hpoint : ∀ᵐ u : ℝ ∂halfLine,
      ‖integrand a j t z u-integrand b j t z u‖ ≤ |weighted a j t R u-weighted b j t R u| := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    have hu0 : (0 : ℝ) ≤ u := hu
    have hp := ComplexRootExponentialDomain.phase_norm_bound u z
    rw [abs_of_nonneg hu] at hp
    have hpR : ‖Complex.exp (Complex.I*(u : ℂ)*z)‖ ≤ Real.exp (u*R) :=
      hp.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hz hu))
    have hid : weighted a j t R u-weighted b j t R u=
        (weighted a 0 t 0 u-weighted b 0 t 0 u)*u^j*Real.exp (u*R) := by
      simp only [weighted,pow_zero,one_mul,zero_mul,add_zero,Real.exp_add]
      ring
    have he : integrand a j t z u-integrand b j t z u=
        ((weighted a 0 t 0 u-weighted b 0 t 0 u : ℝ) : ℂ)*
          (Complex.I*(u : ℂ))^j*Complex.exp (Complex.I*(u : ℂ)*z) := by
      simp only [integrand,Complex.ofReal_sub]
      ring
    simp only [he,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      Complex.norm_I,one_mul,abs_of_nonneg hu0]
    apply (mul_le_mul_of_nonneg_left hpR (mul_nonneg (abs_nonneg _) (pow_nonneg hu j))).trans_eq
    simp only [hid,abs_mul,abs_of_nonneg (pow_nonneg hu0 j),abs_of_pos (Real.exp_pos (u*R))]
  have h := norm_integral_le_of_norm_le hmajor hpoint
  change ‖(∫ u : ℝ, integrand a j t z u ∂halfLine)-(∫ u : ℝ, integrand b j t z u ∂halfLine)‖ ≤ _
  rw [← integral_sub (integrand_integrable a ha j t z) (integrand_integrable b hb j t z)]
  exact h

theorem jet_order_tendsto_uniformly_on_ball (a : ℝ) (ha : 0 < a) (j : ℕ)
    (t R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn (fun b z => jet b j t z) (jet a j t) (𝓝 a) (closedBall (0 : ℂ) R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(weighted_difference_integral_tendsto_zero a ha j t R hR).eventually (gt_mem_nhds hε),
    Ioi_mem_nhds ha] with b he hb
  intro z hz
  rw [dist_eq_norm,norm_sub_rev]
  exact (jet_difference_bound b a hb.le ha.le j t R z (mem_closedBall_zero_iff.mp hz)).trans_lt he

theorem flow_order_tendsto_uniformly_on_ball (a : ℝ) (ha : 0 < a)
    (t R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn (fun b z => flow b t z) (flow a t) (𝓝 a) (closedBall (0 : ℂ) R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp
    (jet_order_tendsto_uniformly_on_ball a ha 0 t R hR)) ε hε] with b hb
  intro z hz
  have hp := hb z hz
  have hn := hb (-z) (by simpa only [mem_closedBall_zero_iff,norm_neg] using hz)
  rw [dist_eq_norm,norm_sub_rev] at hp hn ⊢
  have hid : flow b t z-flow a t z=
      ((jet b 0 t z-jet a 0 t z)+(jet b 0 t (-z)-jet a 0 t (-z)))/2 := by
    unfold flow
    ring
  rw [hid,norm_div,Complex.norm_ofNat]
  apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  linarith [norm_add_le (jet b 0 t z-jet a 0 t z) (jet b 0 t (-z)-jet a 0 t (-z))]

theorem flow_order_tendsto_locally_uniformly (a : ℝ) (ha : 0 < a) (t : ℝ) :
    TendstoLocallyUniformly (fun b z => flow b t z) (flow a t) (𝓝 a) := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R,hR,hsub⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  exact (flow_order_tendsto_uniformly_on_ball a ha t R hR.le).mono hsub

theorem locally_uniform_quadratic_limit (t : ℝ) :
    TendstoLocallyUniformly (fun a z => flow a t z) (RiemannEvenFlow.flow 1 t) (𝓝 (1 : ℝ)) := by
  have he : flow (1 : ℝ) t=RiemannEvenFlow.flow 1 t := by
    funext z
    simpa only [Nat.cast_one] using flow_nat 1 t z
  rw [← he]
  exact flow_order_tendsto_locally_uniformly 1 (by norm_num) t

theorem locally_uniform_quadratic_limit_from_above (t : ℝ) :
    TendstoLocallyUniformly (fun a z => flow a t z) (RiemannEvenFlow.flow 1 t)
      (𝓝[Ioi (1 : ℝ)] 1) := by
  intro V hV x
  obtain ⟨s,hs,h⟩ := locally_uniform_quadratic_limit t V hV x
  exact ⟨s,hs,h.filter_mono nhdsWithin_le_nhds⟩

/-- This is an explicit counterexample to a GENERAL inference from local
uniform convergence to bounded nonreal zeros; it is not the arithmetic flow. -/
theorem escaping_polynomial_locally_uniform_limit :
    TendstoLocallyUniformly
      (fun a : ℝ => fun z : ℂ => 1+(((a-1 : ℝ) : ℂ)^2)*z^2)
      (fun _ : ℂ => 1) (𝓝 (1 : ℝ)) := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R,hR,hsub⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℂ)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hc : ContinuousAt (fun a : ℝ => |a-1|^2*R^2) 1 := by fun_prop
  have hl : Tendsto (fun a : ℝ => |a-1|^2*R^2) (𝓝 1) (𝓝 0) := by
    simpa only [sub_self,abs_zero,zero_pow (by decide : 2 ≠ 0),zero_mul] using hc.tendsto
  filter_upwards [hl.eventually (gt_mem_nhds hε)] with a ha
  intro z hz
  rw [dist_eq_norm,norm_sub_rev,add_sub_cancel_left]
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  have hn : ‖z‖ ≤ R := mem_closedBall_zero_iff.mp (hsub hz)
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hn 2) (sq_nonneg |a-1|)).trans_lt ha

theorem escaping_polynomial_nonreal_roots :
    ∃ b : ℕ → ℝ, ∃ z : ℕ → ℂ,
      (∀ n : ℕ, 1 < b n ∧ 1+(((b n-1 : ℝ) : ℂ)^2)*(z n)^2=0 ∧ (z n).im ≠ 0) ∧
      Tendsto b atTop (𝓝 1) ∧ Tendsto (fun n => ‖z n‖) atTop atTop := by
  let b := fun n : ℕ => 1+1/((n : ℝ)+1)
  let z := fun n : ℕ => Complex.I*(((n : ℝ)+1 : ℝ) : ℂ)
  have hpos (n : ℕ) : 0 < (n : ℝ)+1 := by positivity
  refine ⟨b,z,?_,?_,?_⟩
  · intro n
    have hn : (((n : ℝ)+1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hpos n).ne'
    refine ⟨by dsimp [b]; linarith [one_div_pos.mpr (hpos n)],?_,?_⟩
    · have hb : ((b n-1 : ℝ) : ℂ)=1/(((n : ℝ)+1 : ℝ) : ℂ) := by
        simp only [b,add_sub_cancel_left,Complex.ofReal_div,Complex.ofReal_one]
      rw [hb]
      dsimp [z]
      rw [mul_pow,Complex.I_sq]
      field_simp [hn]
      ring
    · simpa only [z,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,
        Complex.ofReal_im,zero_mul,one_mul,zero_add] using (hpos n).ne'
  · have h : Tendsto (fun n : ℕ => (1 : ℝ)+1/((n : ℝ)+1)) atTop (𝓝 ((1 : ℝ)+0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [b,add_zero] using h
  · have he (n : ℕ) : ‖z n‖=(n : ℝ)+1 := by
      simp only [z,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hpos n)]
    simp_rw [he]
    exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderLimit
