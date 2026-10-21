import Foundation.RiemannRealOrderFifthDerivative
import Foundation.RiemannRealOrderUniformEndpoint

/-! Actual fourth-order remainder integrability for 3/2<a<=2.
Its finite endpoint limit is the fourth kernel derivative, not zero. -/
noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderFourthRemainder
open RiemannThetaComplexKernel RiemannRealOrderFractionalJets
open RiemannRealOrderFractionalRemainder RiemannRealOrderFifthDerivative

theorem fourthCutoff_integrable (a t : ℝ) (ha : 3/2 < a) :
    IntegrableOn (fourthCutoff a t) (Ioi 0) := by
  have h := ((FractionalEndpointLaplace.profile_integrable (2*a-3) (by linarith)
    1 (by norm_num)).const_mul ((t*falling (2*a) 4 : ℝ) : ℂ)).mul_const (kernelComplex 0)
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [fourthCutoff,phaseJet_real a t u 4 hu.le]
  unfold FractionalEndpointLaplace.profile
  norm_num only [Nat.cast_ofNat]
  rw [show 2*a-3-1=2*a-4 by ring]
  simp only [Complex.ofReal_mul,neg_one_mul,← Complex.ofReal_neg,← Complex.ofReal_exp]
  ring

private def boundedFifth (a t : ℝ) (z : ℂ) : ℂ :=
  exponential a t z*(iteratedDeriv 5 kernelComplex z+
    5*phaseJet a t 1 z*iteratedDeriv 4 kernelComplex z+
    10*(phaseJet a t 2 z+(phaseJet a t 1 z)^2)*iteratedDeriv 3 kernelComplex z+
    10*(phaseJet a t 3 z+3*phaseJet a t 1 z*phaseJet a t 2 z+
      (phaseJet a t 1 z)^3)*iteratedDeriv 2 kernelComplex z+
    5*(4*phaseJet a t 1 z*phaseJet a t 3 z+3*(phaseJet a t 2 z)^2+
      6*(phaseJet a t 1 z)^2*phaseJet a t 2 z+(phaseJet a t 1 z)^4)*
        iteratedDeriv 1 kernelComplex z+
    (10*phaseJet a t 2 z*phaseJet a t 3 z+10*(phaseJet a t 1 z)^2*phaseJet a t 3 z+
      15*phaseJet a t 1 z*(phaseJet a t 2 z)^2+
      10*(phaseJet a t 1 z)^3*phaseJet a t 2 z+(phaseJet a t 1 z)^5)*kernelComplex z)

private theorem boundedFifth_continuousOn (a t : ℝ) (ha : 3/2 < a) :
    ContinuousOn (fun u : ℝ => boundedFifth a t (u : ℂ)) (Ici 0) := by
  have he := exponential_continuousOn a t (by linarith)
  have h1 := phaseJet_continuousOn a t 1 (by norm_num; linarith)
  have h2 := phaseJet_continuousOn a t 2 (by norm_num; linarith)
  have h3 := phaseJet_continuousOn a t 3 (by norm_num; linarith)
  have hk (n : ℕ) := (kernel_derivative_continuous n).continuousOn (s := Ici (0 : ℝ))
  have hk0 : ContinuousOn (fun u : ℝ => kernelComplex (u : ℂ)) (Ici 0) := by simpa using hk 0
  unfold boundedFifth
  fun_prop

theorem regularFifth_integrable_near (a t : ℝ) (ha : 3/2 < a) :
    IntegrableOn (fun u : ℝ => regularFifth a t (u : ℂ)) (Ioo 0 1) := by
  have he := exponential_continuousOn a t (by linarith)
  have h1 := phaseJet_continuousOn a t 1 (by norm_num; linarith)
  have hk (n : ℕ) := (kernel_derivative_continuous n).continuousOn (s := Ici (0 : ℝ))
  have hk0 : ContinuousOn (fun u : ℝ => kernelComplex (u : ℂ)) (Ici 0) := by simpa using hk 0
  have hc : ContinuousOn (fun u : ℝ => 5*exponential a t (u : ℂ)*
      (iteratedDeriv 1 kernelComplex (u : ℂ)+phaseJet a t 1 (u : ℂ)*kernelComplex (u : ℂ)))
      (Icc 0 1) := by
    have : ContinuousOn (fun u : ℝ => 5*exponential a t (u : ℂ)*
        (iteratedDeriv 1 kernelComplex (u : ℂ)+phaseJet a t 1 (u : ℂ)*kernelComplex (u : ℂ)))
        (Ici 0) := by fun_prop
    exact this.mono (fun _ hu => hu.1)
  have hp := (phaseJet_integrable_near a t 4 (by norm_num; linarith) 1 (by norm_num)).mul_continuousOn_of_subset
    hc measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self
  have hb : IntegrableOn (fun u : ℝ => boundedFifth a t (u : ℂ)) (Ioo 0 1) :=
    (((boundedFifth_continuousOn a t ha).mono
    (show Icc (0 : ℝ) 1 ⊆ Ici 0 from fun _ hu => hu.1)).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  apply (hp.add hb).congr
  filter_upwards with u
  simp only [Pi.add_apply]
  unfold regularFifth boundedFifth
  ring

theorem singular_fifth_integrable_near (a t : ℝ) (ha : 3/2 < a) :
    IntegrableOn (fun u : ℝ => phaseJet a t 5 (u : ℂ)*endpointDifference a t u) (Ioo 0 1) := by
  obtain ⟨C,hC,hbound⟩ := RiemannRealOrderUniformEndpoint.endpointDifference_uniform_linear t
  have hm : IntegrableOn (fun u : ℝ => |t*falling (2*a) 5| * C*u^(2*a-4)) (Ioo 0 1) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).mpr
      (by linarith : -1 < 2*a-4)).const_mul (|t*falling (2*a) 5| * C)
  have hp : ContinuousOn (fun u : ℝ => phaseJet a t 5 (u : ℂ)) (Ioo 0 1) := by
    intro u hu
    exact ((phaseJet_hasDerivAt a t 5 (u : ℂ)
      (Complex.mem_slitPlane_iff.mpr (Or.inl hu.1))).comp_ofReal).continuousAt.continuousWithinAt
  have hw := (endpointDifference_continuousOn a t).mono
    (show Ioo (0 : ℝ) 1 ⊆ Ioi 0 from fun _ hu => hu.1)
  apply hm.mono' ((hp.mul hw).aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  dsimp only [Pi.mul_apply]
  rw [norm_mul,phaseJet_real a t u 5 hu.1.le,Complex.norm_real,Real.norm_eq_abs,
    abs_mul,abs_of_pos (Real.rpow_pos_of_pos hu.1 _)]
  norm_num only [Nat.cast_ofNat]
  calc
    _ ≤ (|t*falling (2*a) 5| * u^(2*a-5))*(C*u) :=
      mul_le_mul_of_nonneg_left (hbound a (by linarith) u ⟨hu.1.le,hu.2.le⟩)
        (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hu.1.le _))
    _ = _ := by
      have hr : u^(2*a-5)*u=u^(2*a-4) := by
        calc
          _ = u^(2*a-5)*u^(1 : ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hu.1]; congr 1; ring
      calc
        _ = (|t*falling (2*a) 5| * C)*(u^(2*a-5)*u) := by ring
        _ = _ := by rw [hr]

theorem fourthRemainder_derivative_integrable_near (a t : ℝ) (ha : 3/2 < a) :
    IntegrableOn (deriv (fourthRemainder a t)) (Ioo 0 1) := by
  have hc := (fourthCutoff_integrable a t ha).mono_set
    (show Ioo (0 : ℝ) 1 ⊆ Ioi 0 from fun _ hu => hu.1)
  apply (((singular_fifth_integrable_near a t ha).add hc).add
    (regularFifth_integrable_near a t ha)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  exact (fourthRemainder_derivative_eq a t u hu.1).symm

theorem fourthCutoff_derivative_factor (a t u : ℝ) (hu : 0 < u) :
    deriv (fourthCutoff a t) u=(((2*a-4)/u-1 : ℝ) : ℂ)*fourthCutoff a t u := by
  rw [(fourthCutoff_hasDerivAt a t u hu).deriv,fourthCutoff,
    phaseJet_real a t u 5 hu.le,phaseJet_real a t u 4 hu.le,falling_succ (2*a) 4]
  norm_num only [Nat.cast_ofNat]
  rw [show 2*a-5=(2*a-4)-1 by ring,Real.rpow_sub_one hu.ne']
  push_cast
  simp only [div_eq_mul_inv]
  ring

theorem fourthCutoff_derivative_integrable_away (a t δ : ℝ) (ha : 3/2 < a) (hδ : 0 < δ) :
    IntegrableOn (deriv (fourthCutoff a t)) (Ioi δ) := by
  have hq := (fourthCutoff_integrable a t ha).mono_set
    (show Ioi δ ⊆ Ioi (0 : ℝ) from fun _ hu => lt_trans hδ hu)
  have hb : ∀ᵐ u : ℝ ∂volume.restrict (Ioi δ),
      ‖(((2*a-4)/u-1 : ℝ) : ℂ)‖ ≤ |2*a-4|/δ+1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := lt_trans hδ hu
    rw [Complex.norm_real,Real.norm_eq_abs]
    calc
      _ ≤ |(2*a-4)/u|+|1| := abs_sub _ _
      _ = |2*a-4|/u+1 := by rw [abs_div,abs_of_pos hu0,abs_one]
      _ ≤ _ := add_le_add
        (div_le_div_of_nonneg_left (abs_nonneg _) hδ hu.le) le_rfl
  apply (hq.mul_bdd (c := |2*a-4|/δ+1) (by fun_prop) hb).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [fourthCutoff_derivative_factor a t u (lt_trans hδ hu)]
  ring

theorem fourthRemainder_derivative_integrable (a t : ℝ) (ha : 3/2 < a) (ha2 : a ≤ 2) :
    IntegrableOn (deriv (fourthRemainder a t)) (Ioi 0) := by
  have hn := fourthRemainder_derivative_integrable_near a t ha
  have ht : IntegrableOn (deriv (fourthRemainder a t)) (Ioi (1/2)) := by
    have hd := (RiemannRealOrderFractionalDensity.density_iteratedDeriv_integrable_away_zero
      5 a t (1/2) (by linarith) ha2 (by norm_num)).mono_set Ioi_subset_Ici_self
    apply (hd.sub (fourthCutoff_derivative_integrable_away a t (1/2) ha (by norm_num))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := lt_trans (by norm_num : (0 : ℝ) < 1/2) hu
    simp only [Pi.sub_apply]
    rw [(fourthRemainder_hasDerivAt a t u hu0).deriv,(fourthCutoff_hasDerivAt a t u hu0).deriv]
  apply (hn.union ht).mono_set
  intro u hu
  by_cases h : u < 1
  · exact Or.inl ⟨hu,h⟩
  · exact Or.inr (by have := le_of_not_gt h; change (1/2 : ℝ) < u; linarith)

theorem regularFourth_continuousOn (a t : ℝ) (ha : 3/2 < a) :
    ContinuousOn (fun u : ℝ => regularFourth a t (u : ℂ)) (Ici 0) := by
  have he := exponential_continuousOn a t (by linarith)
  have h1 := phaseJet_continuousOn a t 1 (by norm_num; linarith)
  have h2 := phaseJet_continuousOn a t 2 (by norm_num; linarith)
  have h3 := phaseJet_continuousOn a t 3 (by norm_num; linarith)
  have hk (n : ℕ) := (kernel_derivative_continuous n).continuousOn (s := Ici (0 : ℝ))
  have hk0 : ContinuousOn (fun u : ℝ => kernelComplex (u : ℂ)) (Ici 0) := by simpa using hk 0
  unfold regularFourth
  fun_prop

theorem fourth_density_integrable (a t : ℝ) (ha : 3/2 < a) (ha2 : a ≤ 2) :
    IntegrableOn (fun u : ℝ => iteratedDeriv 4 (RiemannRealOrderFractionalDensity.density a t)
      (u : ℂ)) (Ioi 0) := by
  have he := exponential_continuousOn a t (by linarith)
  have hk := (kernel_derivative_continuous 0).continuousOn (s := Ici (0 : ℝ))
  have hc : ContinuousOn (fun u : ℝ => exponential a t (u : ℂ)*kernelComplex (u : ℂ)) (Icc 0 1) := by
    have hk0 : ContinuousOn (fun u : ℝ => kernelComplex (u : ℂ)) (Ici 0) := by simpa using hk
    exact (he.mul hk0).mono (fun _ hu => hu.1)
  have hp := (phaseJet_integrable_near a t 4 (by norm_num; linarith) 1 (by norm_num)).mul_continuousOn_of_subset
    hc measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self
  have hr : IntegrableOn (fun u : ℝ => regularFourth a t (u : ℂ)) (Ioo 0 1) :=
    (((regularFourth_continuousOn a t ha).mono
      (show Icc (0 : ℝ) 1 ⊆ Ici 0 from fun _ hu => hu.1)).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hn : IntegrableOn (fun u : ℝ => iteratedDeriv 4
      (RiemannRealOrderFractionalDensity.density a t) (u : ℂ)) (Ioo 0 1) := by
    apply (hp.add hr).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hK : 0 < (Complex.exp (4*(u : ℂ))).re := by
      simpa [Complex.exp_re,Complex.mul_re,Complex.mul_im] using Real.exp_pos (4*u)
    rw [density_fourth_derivative a t (u : ℂ)
      (Complex.mem_slitPlane_iff.mpr (Or.inl hu.1)) hK]
    dsimp only [Pi.add_apply]
    unfold regularFourth
    ring
  have ht := (RiemannRealOrderFractionalDensity.density_iteratedDeriv_integrable_away_zero
    4 a t (1/2) (by linarith) ha2 (by norm_num)).mono_set Ioi_subset_Ici_self
  apply (hn.union ht).mono_set
  intro u hu
  by_cases h : u < 1
  · exact Or.inl ⟨hu,h⟩
  · exact Or.inr (by have := le_of_not_gt h; change (1/2 : ℝ) < u; linarith)

theorem fourthRemainder_integrable (a t : ℝ) (ha : 3/2 < a) (ha2 : a ≤ 2) :
    IntegrableOn (fourthRemainder a t) (Ioi 0) :=
  (fourth_density_integrable a t ha ha2).sub (fourthCutoff_integrable a t ha)

theorem regularFourth_zero (a t : ℝ) (ha : 3/2 < a) :
    regularFourth a t 0=iteratedDeriv 4 kernelComplex 0 := by
  have he : exponential a t 0=1 := by
    unfold exponential
    rw [Complex.zero_cpow (Complex.ofReal_ne_zero.mpr (by linarith : 2*a ≠ 0))]
    simp
  rw [regularFourth,phaseJet_zero_of_pos a t 1 (by norm_num; linarith),
    phaseJet_zero_of_pos a t 2 (by norm_num; linarith),
    phaseJet_zero_of_pos a t 3 (by norm_num; linarith),he]
  ring

theorem singular_fourth_tendsto_zero (a t : ℝ) (ha : 3/2 < a) :
    Tendsto (fun u : ℝ => phaseJet a t 4 (u : ℂ)*endpointDifference a t u)
      (𝓝[>] 0) (𝓝 0) := by
  have hs : Tendsto (fun u : ℝ => ((u⁻¹ : ℝ) : ℂ)*endpointDifference a t u)
      (𝓝[>] 0) (𝓝 (kernelComplex 0)) := by
    simpa only [zero_add,endpointDifference_zero a t (by linarith),sub_zero,Complex.real_smul] using
      (endpointDifference_hasDerivAt a t (by linarith)).tendsto_slope_zero_right
  have hp : Tendsto (fun u : ℝ => ((u^(2*a-3) : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun u : ℝ => u^(2*a-3)) 0 :=
      continuousAt_id.rpow_const (Or.inr (by linarith))
    simpa only [Function.comp_def,Real.zero_rpow (by linarith : 2*a-3 ≠ 0),Complex.ofReal_zero] using
      (Complex.continuous_ofReal.continuousAt.comp hc).tendsto.mono_left nhdsWithin_le_nhds
  have h := (tendsto_const_nhds (x := ((t*falling (2*a) 4 : ℝ) : ℂ))).mul (hp.mul hs)
  have hh : Tendsto (fun u : ℝ => ((t*falling (2*a) 4 : ℝ) : ℂ)*
      (((u^(2*a-3) : ℝ) : ℂ)*(((u⁻¹ : ℝ) : ℂ)*endpointDifference a t u)))
      (𝓝[>] 0) (𝓝 0) := by simpa only [zero_mul,mul_zero] using h
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  rw [phaseJet_real a t u 4 hu.le]
  have hr : u^(2*a-4)=u^(2*a-3)*u⁻¹ := by
    rw [show 2*a-4=(2*a-3)-1 by ring,Real.rpow_sub_one hu.ne',div_eq_mul_inv]
  norm_num only [Nat.cast_ofNat]
  rw [hr]
  push_cast
  ring

theorem fourthRemainder_endpoint (a t : ℝ) (ha : 3/2 < a) :
    Tendsto (fourthRemainder a t) (𝓝[>] 0) (𝓝 (iteratedDeriv 4 kernelComplex 0)) := by
  have hc := (regularFourth_continuousOn a t ha) 0 (by simp)
  have ht : Tendsto (fun u : ℝ => regularFourth a t (u : ℂ)) (𝓝[>] 0)
      (𝓝 (iteratedDeriv 4 kernelComplex 0)) := by
    simpa only [Complex.ofReal_zero,regularFourth_zero a t ha] using
      (hc.mono (show Ioi (0 : ℝ) ⊆ Ici 0 from fun u hu => (show 0 < u from hu).le)).tendsto
  have h := (singular_fourth_tendsto_zero a t ha).add ht
  apply (show Tendsto (fun u : ℝ => phaseJet a t 4 (u : ℂ)*endpointDifference a t u+
      regularFourth a t (u : ℂ)) (𝓝[>] 0) (𝓝 (iteratedDeriv 4 kernelComplex 0)) by
      simpa only [zero_add] using h).congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact (fourthRemainder_eq a t u hu).symm

theorem fourthCutoff_tendsto_zero (a t : ℝ) : Tendsto (fourthCutoff a t) atTop (𝓝 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2*a-4) 1 zero_lt_one
  have hC : Tendsto (fun u : ℝ => ((u^(2*a-4)*Real.exp (-u) : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp h
  have hh := ((tendsto_const_nhds (x := ((t*falling (2*a) 4 : ℝ) : ℂ))).mul hC).mul_const (kernelComplex 0)
  apply (show Tendsto (fun u : ℝ => ((t*falling (2*a) 4 : ℝ) : ℂ)*
      ((u^(2*a-4)*Real.exp (-u) : ℝ) : ℂ)*kernelComplex 0) atTop (𝓝 0) by
      simpa only [mul_zero,zero_mul] using hh).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
  rw [fourthCutoff,phaseJet_real a t u 4 hu]
  norm_num only [Nat.cast_ofNat]
  push_cast
  ring

theorem fourthRemainder_tendsto_zero_atTop (a t : ℝ) (ha : 3/2 < a) (ha2 : a ≤ 2) :
    Tendsto (fourthRemainder a t) atTop (𝓝 0) := by
  change Tendsto (fun u : ℝ => iteratedDeriv 4 (RiemannRealOrderFractionalDensity.density a t)
    (u : ℂ)-fourthCutoff a t u) atTop (𝓝 0)
  have h := (RiemannRealOrderFractionalDensity.density_iteratedDeriv_tendsto_zero
    4 a t (by linarith) ha2).sub (fourthCutoff_tendsto_zero a t)
  simpa only [sub_zero] using h

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderFourthRemainder
