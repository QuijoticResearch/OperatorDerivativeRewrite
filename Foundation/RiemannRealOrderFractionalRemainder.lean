import Foundation.RiemannRealOrderFractionalJets
import Foundation.FractionalEndpointLaplace

/-! Local integrability after subtracting the genuine fractional endpoint cutoff.
All density derivatives are actual derivatives on the positive real axis. -/
noncomputable section
open MeasureTheory Set Filter Complex Asymptotics
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderFractionalRemainder
open RiemannThetaComplexKernel RiemannRealOrderFractionalJets

theorem phaseJet_continuousOn (a t : ℝ) (n : ℕ) (hn : 0 < 2*a-(n : ℝ)) :
    ContinuousOn (fun u : ℝ => phaseJet a t n (u : ℂ)) (Ici 0) := by
  have hp : Continuous (fun u : ℝ => u^(2*a-(n : ℝ))) :=
    continuous_id.rpow_const (fun _ => Or.inr hn.le)
  have hc : Continuous (fun u : ℝ => ((t*falling (2*a) n*u^(2*a-(n : ℝ)) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_const.mul hp)
  apply hc.continuousOn.congr
  intro u hu
  exact phaseJet_real a t u n hu

theorem phaseJet_zero_of_pos (a t : ℝ) (n : ℕ) (hn : 0 < 2*a-(n : ℝ)) :
    phaseJet a t n 0=0 := by
  simpa [Real.zero_rpow hn.ne'] using phaseJet_real a t 0 n le_rfl

theorem kernel_derivative_continuous (n : ℕ) :
    Continuous (fun u : ℝ => iteratedDeriv n kernelComplex (u : ℂ)) := by
  have h := RiemannRealOrderCubicDensity.density_iteratedDeriv_continuous n 0
  have he : RiemannRealOrderCubicDensity.density 0=kernelComplex := by
    funext z
    simp [RiemannRealOrderCubicDensity.density]
  rwa [he] at h

theorem exponential_continuousOn (a t : ℝ) (ha : 0 < 2*a) :
    ContinuousOn (fun u : ℝ => exponential a t (u : ℂ)) (Ici 0) := by
  have h := Complex.continuous_exp.comp_continuousOn (phaseJet_continuousOn a t 0 (by simpa using ha))
  simpa only [phaseJet,powerJet_zero,exponential,Function.comp_def] using h

theorem phaseJet_integrable_near (a t : ℝ) (n : ℕ) (hn : -1 < 2*a-(n : ℝ))
    (δ : ℝ) (hδ : 0 < δ) :
    IntegrableOn (fun u : ℝ => phaseJet a t n (u : ℂ)) (Ioo 0 δ) := by
  have hm : IntegrableOn (fun u : ℝ => |t*falling (2*a) n| * u^(2*a-(n : ℝ))) (Ioo 0 δ) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff hδ).mpr hn).const_mul _
  have hc : ContinuousOn (fun u : ℝ => phaseJet a t n (u : ℂ)) (Ioo 0 δ) := by
    intro u hu
    exact ((phaseJet_hasDerivAt a t n (u : ℂ)
      (Complex.mem_slitPlane_iff.mpr (Or.inl hu.1))).comp_ofReal).continuousAt.continuousWithinAt
  apply hm.mono' (hc.aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  rw [phaseJet_real a t u n hu.1.le,Complex.norm_real,Real.norm_eq_abs,abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos hu.1 _)]

theorem cutoff_integrable (a t : ℝ) (ha : 1 < a) :
    IntegrableOn (cutoff a t) (Ioi 0) := by
  have h := ((FractionalEndpointLaplace.profile_integrable (2*a-2) (by linarith)
    1 (by norm_num)).const_mul ((t*falling (2*a) 3 : ℝ) : ℂ)).mul_const (kernelComplex 0)
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [cutoff,phaseJet_real a t u 3 hu.le]
  unfold FractionalEndpointLaplace.profile
  norm_num only [Nat.cast_ofNat]
  rw [show 2*a-2-1=2*a-3 by ring]
  simp only [Complex.ofReal_mul,neg_one_mul,← Complex.ofReal_neg,← Complex.ofReal_exp]
  ring

private def boundedFourth (a t : ℝ) (z : ℂ) : ℂ :=
  exponential a t z*(iteratedDeriv 4 kernelComplex z+
    4*phaseJet a t 1 z*iteratedDeriv 3 kernelComplex z+
    6*(phaseJet a t 2 z+(phaseJet a t 1 z)^2)*iteratedDeriv 2 kernelComplex z+
    4*(3*phaseJet a t 1 z*phaseJet a t 2 z+(phaseJet a t 1 z)^3)*
      iteratedDeriv 1 kernelComplex z+
    (3*(phaseJet a t 2 z)^2+6*(phaseJet a t 1 z)^2*phaseJet a t 2 z+
      (phaseJet a t 1 z)^4)*kernelComplex z)

private theorem boundedFourth_continuousOn (a t : ℝ) (ha : 1 < a) :
    ContinuousOn (fun u : ℝ => boundedFourth a t (u : ℂ)) (Ici 0) := by
  have he := exponential_continuousOn a t (by linarith)
  have h1 := phaseJet_continuousOn a t 1 (by norm_num; linarith)
  have h2 := phaseJet_continuousOn a t 2 (by norm_num; linarith)
  have hk (n : ℕ) := (kernel_derivative_continuous n).continuousOn (s := Ici (0 : ℝ))
  have hk0 : ContinuousOn (fun u : ℝ => kernelComplex (u : ℂ)) (Ici 0) := by simpa using hk 0
  change ContinuousOn (fun u : ℝ => _) (Ici 0)
  unfold boundedFourth
  fun_prop

theorem regularFourth_integrable_near (a t : ℝ) (ha : 1 < a)
    (δ : ℝ) (hδ : 0 < δ) :
    IntegrableOn (fun u : ℝ => regularFourth a t (u : ℂ)) (Ioo 0 δ) := by
  have he := exponential_continuousOn a t (by linarith)
  have h1 := phaseJet_continuousOn a t 1 (by norm_num; linarith)
  have hk (n : ℕ) := (kernel_derivative_continuous n).continuousOn (s := Ici (0 : ℝ))
  have hk0 : ContinuousOn (fun u : ℝ => kernelComplex (u : ℂ)) (Ici 0) := by simpa using hk 0
  have hc : ContinuousOn (fun u : ℝ => 4*exponential a t (u : ℂ)*
      (iteratedDeriv 1 kernelComplex (u : ℂ)+phaseJet a t 1 (u : ℂ)*kernelComplex (u : ℂ)))
      (Icc 0 δ) := by
    have : ContinuousOn (fun u : ℝ => 4*exponential a t (u : ℂ)*
      (iteratedDeriv 1 kernelComplex (u : ℂ)+phaseJet a t 1 (u : ℂ)*kernelComplex (u : ℂ)))
      (Ici 0) := by fun_prop
    exact this.mono (fun _ hu => hu.1)
  have hp := (phaseJet_integrable_near a t 3 (by norm_num; linarith) δ hδ).mul_continuousOn_of_subset hc measurableSet_Ioo isCompact_Icc
      (show Ioo (0 : ℝ) δ ⊆ Icc 0 δ from fun _ hu => ⟨hu.1.le,hu.2.le⟩)
  have hb : IntegrableOn (fun u : ℝ => boundedFourth a t (u : ℂ)) (Icc 0 δ) :=
    ((boundedFourth_continuousOn a t ha).mono
    (show Icc (0 : ℝ) δ ⊆ Ici 0 from fun _ hu => hu.1)).integrableOn_Icc
  apply (hp.add (hb.mono_set Ioo_subset_Icc_self)).congr
  filter_upwards with u
  simp only [Pi.add_apply]
  unfold regularFourth boundedFourth
  ring

theorem remainder_derivative_integrable_near (a t : ℝ) (ha : 1 < a) :
    ∃ δ : ℝ, 0 < δ ∧ IntegrableOn (deriv (remainder a t)) (Ioo 0 δ) := by
  obtain ⟨δ,hδ,hcrit⟩ := critical_endpoint_term_integrable a t ha
  have hp : IntegrableOn (fun u : ℝ => phaseJet a t 4 (u : ℂ)*endpointDifference a t u)
      (Ioo 0 δ) := by
    apply (hcrit.const_mul ((t*falling (2*a) 4 : ℝ) : ℂ)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    rw [phaseJet_real a t u 4 hu.1.le]
    push_cast
    ring
  refine ⟨δ,hδ,?_⟩
  have hc := (cutoff_integrable a t ha).mono_set
    (show Ioo (0 : ℝ) δ ⊆ Ioi 0 from fun _ hu => hu.1)
  apply ((hp.add hc).add (regularFourth_integrable_near a t ha δ hδ)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  exact (remainder_derivative_eq a t u hu.1).symm

theorem regularThird_continuousOn (a t : ℝ) (ha : 1 < a) :
    ContinuousOn (fun u : ℝ => regularThird a t (u : ℂ)) (Ici 0) := by
  have he := exponential_continuousOn a t (by linarith)
  have h1 := phaseJet_continuousOn a t 1 (by norm_num; linarith)
  have h2 := phaseJet_continuousOn a t 2 (by norm_num; linarith)
  have hk (n : ℕ) := (kernel_derivative_continuous n).continuousOn (s := Ici (0 : ℝ))
  have hk0 : ContinuousOn (fun u : ℝ => kernelComplex (u : ℂ)) (Ici 0) := by
    simpa using hk 0
  unfold regularThird
  fun_prop

theorem regularThird_zero (a t : ℝ) (ha : 1 < a) : regularThird a t 0=0 := by
  rw [regularThird,phaseJet_zero_of_pos a t 1 (by norm_num; linarith),
    phaseJet_zero_of_pos a t 2 (by norm_num; linarith),
    RiemannRealOrderCubicEndpoint.odd_kernel_derivative_zero 3 (by decide)]
  ring

theorem singular_remainder_tendsto_zero (a t : ℝ) (ha : 1 < a) :
    Tendsto (fun u : ℝ => phaseJet a t 3 (u : ℂ)*endpointDifference a t u)
      (𝓝[>] 0) (𝓝 0) := by
  have hs : Tendsto (fun u : ℝ => ((u⁻¹ : ℝ) : ℂ)*endpointDifference a t u)
      (𝓝[>] 0) (𝓝 (kernelComplex 0)) := by
    simpa only [zero_add,endpointDifference_zero a t (by linarith),sub_zero,
      Complex.real_smul] using
      (endpointDifference_hasDerivAt a t (by linarith)).tendsto_slope_zero_right
  have hp : Tendsto (fun u : ℝ => ((u^(2*a-2) : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have h : ContinuousAt (fun u : ℝ => u^(2*a-2)) 0 :=
      continuousAt_id.rpow_const (Or.inr (by linarith))
    simpa only [Function.comp_def,Real.zero_rpow (by linarith : 2*a-2 ≠ 0),Complex.ofReal_zero] using
      (Complex.continuous_ofReal.continuousAt.comp h).tendsto.mono_left nhdsWithin_le_nhds
  have hh := (tendsto_const_nhds (x := ((t*falling (2*a) 3 : ℝ) : ℂ))).mul (hp.mul hs)
  have hh' : Tendsto (fun u : ℝ => ((t*falling (2*a) 3 : ℝ) : ℂ)*
      (((u^(2*a-2) : ℝ) : ℂ)*(((u⁻¹ : ℝ) : ℂ)*endpointDifference a t u)))
      (𝓝[>] 0) (𝓝 0) := by simpa only [zero_mul,mul_zero] using hh
  apply hh'.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  rw [phaseJet_real a t u 3 hu.le]
  have hr : u^(2*a-3)=u^(2*a-2)*u⁻¹ := by
    rw [show 2*a-3=(2*a-2)-1 by ring,Real.rpow_sub_one hu.ne',div_eq_mul_inv]
  norm_num only [Nat.cast_ofNat]
  rw [hr]
  push_cast
  ring

theorem remainder_tendsto_zero (a t : ℝ) (ha : 1 < a) :
    Tendsto (remainder a t) (𝓝[>] 0) (𝓝 0) := by
  have hc := (regularThird_continuousOn a t ha) 0 (by simp)
  have ht : Tendsto (fun u : ℝ => regularThird a t (u : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Complex.ofReal_zero,regularThird_zero a t ha] using
      (hc.mono (show Ioi (0 : ℝ) ⊆ Ici 0 from fun u hu => (show 0 < u from hu).le)).tendsto
  have h := (singular_remainder_tendsto_zero a t ha).add ht
  apply (show Tendsto (fun u : ℝ => phaseJet a t 3 (u : ℂ)*endpointDifference a t u+
      regularThird a t (u : ℂ)) (𝓝[>] 0) (𝓝 0) by simpa only [zero_add] using h).congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact (remainder_eq a t u hu).symm

private theorem damped_power_integrable_away (s δ : ℝ) (hδ : 0 < δ) :
    IntegrableOn (fun u : ℝ => ((u^s : ℝ) : ℂ)*(Real.exp (-u) : ℂ)) (Ioi δ) := by
  have hc : ContinuousOn (fun u : ℝ => Real.exp (-u)*u^s) (Ici δ) :=
    continuousOn_id.neg.rexp.mul (continuousOn_id.rpow_const
      (fun u hu => Or.inl (ne_of_gt (lt_of_lt_of_le hδ hu))))
  have hi := integrable_of_isBigO_exp_neg one_half_pos hc
    (Real.Gamma_integrand_isLittleO s).isBigO
  have hC := Complex.ofRealCLM.integrable_comp hi
  apply hC.congr
  filter_upwards with u
  simp [Complex.ofReal_mul,mul_comm]

theorem cutoff_derivative_integrable_away (a t δ : ℝ) (hδ : 0 < δ) :
    IntegrableOn (deriv (cutoff a t)) (Ioi δ) := by
  have hp (n : ℕ) : IntegrableOn (fun u : ℝ =>
      phaseJet a t n (u : ℂ)*kernelComplex 0*(Real.exp (-u) : ℂ)) (Ioi δ) := by
    have h := ((damped_power_integrable_away (2*a-(n : ℝ)) δ hδ).const_mul ((t*falling (2*a) n : ℝ) : ℂ)).mul_const (kernelComplex 0)
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [phaseJet_real a t u n (le_of_lt (lt_trans hδ hu))]
    push_cast
    ring
  apply ((hp 4).sub (hp 3)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [(cutoff_hasDerivAt a t u (lt_trans hδ hu)).deriv]
  simp only [Pi.sub_apply]
  ring

theorem remainder_derivative_integrable (a t : ℝ) (ha : 1 < a) (ha2 : a ≤ 2) :
    IntegrableOn (deriv (remainder a t)) (Ioi 0) := by
  obtain ⟨δ,hδ,hnear⟩ := remainder_derivative_integrable_near a t ha
  have htail : IntegrableOn (deriv (remainder a t)) (Ioi (δ/2)) := by
    have hd := (RiemannRealOrderFractionalDensity.density_iteratedDeriv_integrable_away_zero
      4 a t (δ/2) (by linarith) ha2 (by linarith)).mono_set Ioi_subset_Ici_self
    apply (hd.sub (cutoff_derivative_integrable_away a t (δ/2) (by linarith))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change δ/2 < u at hu
    simp only [Pi.sub_apply]
    rw [(remainder_hasDerivAt a t u (by linarith : 0 < u)).deriv,
      (cutoff_hasDerivAt a t u (by linarith : 0 < u)).deriv]
  apply (hnear.union htail).mono_set
  intro u hu
  by_cases h : u < δ
  · exact Or.inl ⟨hu,h⟩
  · exact Or.inr (by have := le_of_not_gt h; change δ/2 < u; linarith)

theorem remainder_integrable (a t : ℝ) (ha : 1 < a) (ha2 : a ≤ 2) :
    IntegrableOn (remainder a t) (Ioi 0) := by
  obtain ⟨δ,hδ,hcrit⟩ := critical_endpoint_term_integrable a t ha
  have hc : ContinuousOn (fun u : ℝ => (u : ℂ)) (Icc 0 δ) := by fun_prop
  have hsing := hcrit.mul_continuousOn_of_subset hc measurableSet_Ioo isCompact_Icc
    (show Ioo (0 : ℝ) δ ⊆ Icc 0 δ from fun _ hu => ⟨hu.1.le,hu.2.le⟩)
  have hp : IntegrableOn (fun u : ℝ => phaseJet a t 3 (u : ℂ)*endpointDifference a t u)
      (Ioo 0 δ) := by
    apply (hsing.const_mul ((t*falling (2*a) 3 : ℝ) : ℂ)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    rw [phaseJet_real a t u 3 hu.1.le]
    norm_num only [Nat.cast_ofNat]
    have hr : u^(2*a-3)=u^(2*a-4)*u := by
      rw [show 2*a-3=(2*a-4)+1 by ring,Real.rpow_add hu.1,Real.rpow_one]
    rw [hr]
    simp only [Pi.mul_apply,Complex.ofReal_mul]
    ring
  have hr : IntegrableOn (fun u : ℝ => regularThird a t (u : ℂ)) (Icc 0 δ) :=
    ((regularThird_continuousOn a t ha).mono
      (show Icc (0 : ℝ) δ ⊆ Ici 0 from fun _ hu => hu.1)).integrableOn_Icc
  have hnear : IntegrableOn (remainder a t) (Ioo 0 δ) := by
    apply (hp.add (hr.mono_set Ioo_subset_Icc_self)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact (remainder_eq a t u hu.1).symm
  have htail : IntegrableOn (remainder a t) (Ioi (δ/2)) := by
    have hd := (RiemannRealOrderFractionalDensity.density_iteratedDeriv_integrable_away_zero
      3 a t (δ/2) (by linarith) ha2 (by linarith)).mono_set Ioi_subset_Ici_self
    exact hd.sub ((cutoff_integrable a t ha).mono_set
      (show Ioi (δ/2) ⊆ Ioi (0 : ℝ) from fun u hu => lt_trans (show 0 < δ/2 by linarith) hu))
  apply (hnear.union htail).mono_set
  intro u hu
  by_cases h : u < δ
  · exact Or.inl ⟨hu,h⟩
  · exact Or.inr (by have := le_of_not_gt h; change δ/2 < u; linarith)

theorem cutoff_tendsto_zero (a t : ℝ) : Tendsto (cutoff a t) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2*a-3) 1 zero_lt_one)
  have hC : Tendsto (fun u : ℝ => ((u^(2*a-3)*Real.exp (-u) : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp h
  have hh := ((tendsto_const_nhds (x := ((t*falling (2*a) 3 : ℝ) : ℂ))).mul hC).mul_const (kernelComplex 0)
  apply (show Tendsto (fun u : ℝ => ((t*falling (2*a) 3 : ℝ) : ℂ)*
      ((u^(2*a-3)*Real.exp (-u) : ℝ) : ℂ)*kernelComplex 0) atTop (𝓝 0) by
    simpa only [mul_zero,zero_mul] using hh).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
  rw [cutoff,phaseJet_real a t u 3 hu]
  norm_num only [Nat.cast_ofNat]
  push_cast
  ring

theorem remainder_tendsto_zero_atTop (a t : ℝ) (ha : 1 < a) (ha2 : a ≤ 2) :
    Tendsto (remainder a t) atTop (𝓝 0) := by
  change Tendsto (fun u : ℝ =>
    iteratedDeriv 3 (RiemannRealOrderFractionalDensity.density a t) (u : ℂ)-cutoff a t u)
    atTop (𝓝 0)
  have h := (RiemannRealOrderFractionalDensity.density_iteratedDeriv_tendsto_zero
    3 a t (by linarith) ha2).sub (cutoff_tendsto_zero a t)
  simpa only [sub_zero] using h

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderFractionalRemainder
