import Foundation.RiemannRealOrderFractionalFourier

/-! Actual low-jet endpoint limits and half-line reconstruction for real orders.
The branch-endpoint limits concern positive-axis profiles, not complex derivatives at zero. -/
noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderFractionalReconstruction
open RiemannThetaComplexKernel RiemannRealOrderFractionalJets
open RiemannRealOrderFractionalRemainder RiemannRealOrderFractionalFourier

def lowJet (n : ℕ) (a t : ℝ) (z : ℂ) : ℂ :=
  match n with
  | 0 => exponential a t z*kernelComplex z
  | 1 => exponential a t z*(iteratedDeriv 1 kernelComplex z+phaseJet a t 1 z*kernelComplex z)
  | 2 => exponential a t z*(iteratedDeriv 2 kernelComplex z+
      2*phaseJet a t 1 z*iteratedDeriv 1 kernelComplex z+
      (phaseJet a t 2 z+(phaseJet a t 1 z)^2)*kernelComplex z)
  | _ => 0

theorem lowJet_actual (n : ℕ) (hn : n ≤ 2) (a t : ℝ) (z : ℂ)
    (hz : z ∈ Complex.slitPlane) (hK : 0 < (Complex.exp (4*z)).re) :
    iteratedDeriv n (RiemannRealOrderFractionalDensity.density a t) z=lowJet n a t z := by
  interval_cases n
  · rfl
  · have h := iteratedDeriv_fun_mul (n := 1) (x := z)
      (exponential_analyticAt a t z hz).contDiffAt (kernelComplex_analyticAt z hK).contDiffAt
    change iteratedDeriv 1 (fun w => exponential a t w*kernelComplex w) z=_
    rw [h]
    norm_num [Finset.sum_range_succ,exponential_iteratedDeriv,hz,exponentialJet,bell,lowJet,Nat.choose]
    ring
  · have h := iteratedDeriv_fun_mul (n := 2) (x := z)
      (exponential_analyticAt a t z hz).contDiffAt (kernelComplex_analyticAt z hK).contDiffAt
    change iteratedDeriv 2 (fun w => exponential a t w*kernelComplex w) z=_
    rw [h]
    norm_num [Finset.sum_range_succ,exponential_iteratedDeriv,hz,exponentialJet,bell,lowJet,Nat.choose]
    ring

theorem lowJet_continuousOn (n : ℕ) (hn : n ≤ 2) (a t : ℝ) (ha : 1 < a) :
    ContinuousOn (fun u : ℝ => lowJet n a t (u : ℂ)) (Ici 0) := by
  have he := exponential_continuousOn a t (by linarith)
  have h1 := phaseJet_continuousOn a t 1 (by norm_num; linarith)
  have h2 := phaseJet_continuousOn a t 2 (by norm_num; linarith)
  have hk (j : ℕ) := (kernel_derivative_continuous j).continuousOn (s := Ici (0 : ℝ))
  have hk0 : ContinuousOn (fun u : ℝ => kernelComplex (u : ℂ)) (Ici 0) := by simpa using hk 0
  interval_cases n <;> simp only [lowJet] <;> fun_prop

theorem lowJet_zero (n : ℕ) (hn : n ≤ 2) (a t : ℝ) (ha : 1 < a) :
    lowJet n a t 0=iteratedDeriv n kernelComplex 0 := by
  have h1 := phaseJet_zero_of_pos a t 1 (by norm_num; linarith)
  have h2 := phaseJet_zero_of_pos a t 2 (by norm_num; linarith)
  have he : exponential a t 0=1 := by
    have hpow : (0 : ℂ)^((2*a : ℝ) : ℂ)=0 :=
      Complex.zero_cpow (Complex.ofReal_ne_zero.mpr (by linarith))
    change Complex.exp ((t : ℂ)*(0 : ℂ)^((2*a : ℝ) : ℂ))=1
    rw [hpow,mul_zero,Complex.exp_zero]
  interval_cases n <;> simp [lowJet,h1,h2,he]

private theorem real_kernel_domain (u : ℝ) : 0 < (Complex.exp (4*(u : ℂ))).re := by
  simpa [Complex.exp_re,Complex.mul_re,Complex.mul_im] using Real.exp_pos (4*u)

theorem profile_endpoint (n : ℕ) (hn : n ≤ 2) (a t : ℝ) (ha : 1 < a) :
    Tendsto (fun u : ℝ => iteratedDeriv n
      (RiemannRealOrderFractionalDensity.density a t) (u : ℂ))
      (𝓝[>] 0) (𝓝 (iteratedDeriv n kernelComplex 0)) := by
  have hc := (lowJet_continuousOn n hn a t ha) 0 (by simp)
  have ht : Tendsto (fun u : ℝ => lowJet n a t (u : ℂ)) (𝓝[>] 0)
      (𝓝 (iteratedDeriv n kernelComplex 0)) := by
    simpa only [Complex.ofReal_zero,lowJet_zero n hn a t ha] using
      (hc.mono (show Ioi (0 : ℝ) ⊆ Ici 0 from fun u hu => (show 0 < u from hu).le)).tendsto
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact (lowJet_actual n hn a t (u : ℂ)
    (Complex.mem_slitPlane_iff.mpr (Or.inl hu)) (real_kernel_domain u)).symm

theorem profile_integrable (n : ℕ) (hn : n ≤ 3) (a t : ℝ) (ha : 1 < a) (ha2 : a ≤ 2) :
    IntegrableOn (fun u : ℝ => iteratedDeriv n
      (RiemannRealOrderFractionalDensity.density a t) (u : ℂ)) (Ioi 0) := by
  by_cases h3 : n=3
  · subst n
    exact third_derivative_integrable a t ha ha2
  have hn2 : n ≤ 2 := by omega
  have hj : IntegrableOn (fun u : ℝ => lowJet n a t (u : ℂ)) (Icc 0 1) :=
    ((lowJet_continuousOn n hn2 a t ha).mono
      (show Icc (0 : ℝ) 1 ⊆ Ici 0 from fun _ hu => hu.1)).integrableOn_Icc
  have hnear : IntegrableOn (fun u : ℝ => iteratedDeriv n
      (RiemannRealOrderFractionalDensity.density a t) (u : ℂ)) (Ioo 0 1) := by
    apply (hj.mono_set Ioo_subset_Icc_self).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact (lowJet_actual n hn2 a t (u : ℂ)
      (Complex.mem_slitPlane_iff.mpr (Or.inl hu.1)) (real_kernel_domain u)).symm
  have htail := (RiemannRealOrderFractionalDensity.density_iteratedDeriv_integrable_away_zero
    n a t (1/2) (by linarith) ha2 (by norm_num)).mono_set Ioi_subset_Ici_self
  apply (hnear.union htail).mono_set
  intro u hu
  by_cases h : u < 1
  · exact Or.inl ⟨hu,h⟩
  · exact Or.inr (by change (1/2 : ℝ) < u; linarith)

def cosineIntegral (n : ℕ) (a t x : ℝ) : ℂ := ∫ u : ℝ in Ioi 0,
  iteratedDeriv n (RiemannRealOrderFractionalDensity.density a t) (u : ℂ)*(Real.cos (x*u) : ℂ)

def sineIntegral (n : ℕ) (a t x : ℝ) : ℂ := ∫ u : ℝ in Ioi 0,
  iteratedDeriv n (RiemannRealOrderFractionalDensity.density a t) (u : ℂ)*(Real.sin (x*u) : ℂ)

theorem cosine_integrable (n : ℕ) (hn : n ≤ 3) (a t x : ℝ) (ha : 1 < a) (ha2 : a ≤ 2) :
    IntegrableOn (fun u : ℝ => iteratedDeriv n
      (RiemannRealOrderFractionalDensity.density a t) (u : ℂ)*(Real.cos (x*u) : ℂ)) (Ioi 0) := by
  apply (profile_integrable n hn a t ha ha2).mul_bdd (c := 1) (by fun_prop)
  filter_upwards with u
  simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one (x*u)

theorem sine_integrable (n : ℕ) (hn : n ≤ 3) (a t x : ℝ) (ha : 1 < a) (ha2 : a ≤ 2) :
    IntegrableOn (fun u : ℝ => iteratedDeriv n
      (RiemannRealOrderFractionalDensity.density a t) (u : ℂ)*(Real.sin (x*u) : ℂ)) (Ioi 0) := by
  apply (profile_integrable n hn a t ha ha2).mul_bdd (c := 1) (by fun_prop)
  filter_upwards with u
  simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_sin_le_one (x*u)

private theorem bounded_profile_boundary (n : ℕ) (a t : ℝ) (ha : 1 < a) (ha2 : a ≤ 2)
    (g : ℝ → ℂ) (hg : ∀ u, ‖g u‖ ≤ 1) :
    Tendsto (fun u : ℝ => iteratedDeriv n
      (RiemannRealOrderFractionalDensity.density a t) (u : ℂ)*g u) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun u => ?_)
    (tendsto_zero_iff_norm_tendsto_zero.mp
      (RiemannRealOrderFractionalDensity.density_iteratedDeriv_tendsto_zero n a t (by linarith) ha2))
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hg u)

theorem cosine_recurrence (n : ℕ) (hn : n ≤ 2) (a t x : ℝ) (ha : 1 < a) (ha2 : a ≤ 2) :
    (x : ℂ)*cosineIntegral n a t x= -sineIntegral (n+1) a t x := by
  let f : ℝ → ℂ := fun u => iteratedDeriv n (RiemannRealOrderFractionalDensity.density a t) (u : ℂ)
  let fp : ℝ → ℂ := fun u => iteratedDeriv (n+1) (RiemannRealOrderFractionalDensity.density a t) (u : ℂ)
  let g : ℝ → ℂ := fun u => (Real.sin (x*u) : ℂ)
  let gp : ℝ → ℂ := fun u => (x : ℂ)*(Real.cos (x*u) : ℂ)
  have hf (u : ℝ) (hu : u ∈ Ioi 0) : HasDerivAt f (fp u) u :=
    RiemannRealOrderFractionalDensity.density_profile_hasDerivAt n a t u hu
  have hg (u : ℝ) : HasDerivAt g (gp u) u := by
    convert (((hasDerivAt_id u).const_mul x).sin).ofReal_comp using 1
    · rfl
    · simp [gp,Complex.ofReal_mul,mul_comm]
  have hfg : IntegrableOn (f*gp) (Ioi 0) := by
    apply ((cosine_integrable n (by omega) a t x ha ha2).const_mul (x : ℂ)).congr
    filter_upwards with u
    simp only [Pi.mul_apply,f,gp]
    ring
  have hzero : Tendsto (f*g) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous g := by dsimp [g]; fun_prop
    have h := (profile_endpoint n hn a t ha).mul
      (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    simpa only [f,Pi.mul_def,g,Complex.ofReal_zero,mul_zero,Real.sin_zero] using h
  have htop : Tendsto (f*g) atTop (𝓝 0) :=
    bounded_profile_boundary n a t ha ha2 g (fun u => by
      simpa only [g,Complex.norm_real,Real.norm_eq_abs] using Real.abs_sin_le_one (x*u))
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hf (fun u _ => hg u) hfg
    (sine_integrable (n+1) (by omega) a t x ha ha2) hzero htop
  have he : (∫ u : ℝ in Ioi 0, f u*gp u)=(x : ℂ)*cosineIntegral n a t x := by
    rw [cosineIntegral,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with u
    dsimp [f,gp]
    ring
  rw [he] at h
  simpa only [zero_sub,sub_zero,fp,g,sineIntegral] using h

theorem sine_recurrence (n : ℕ) (hn : n ≤ 2) (a t x : ℝ) (ha : 1 < a) (ha2 : a ≤ 2) :
    (x : ℂ)*sineIntegral n a t x=iteratedDeriv n kernelComplex 0+cosineIntegral (n+1) a t x := by
  let f : ℝ → ℂ := fun u => iteratedDeriv n (RiemannRealOrderFractionalDensity.density a t) (u : ℂ)
  let fp : ℝ → ℂ := fun u => iteratedDeriv (n+1) (RiemannRealOrderFractionalDensity.density a t) (u : ℂ)
  let g : ℝ → ℂ := fun u => (Real.cos (x*u) : ℂ)
  let gp : ℝ → ℂ := fun u => -(x : ℂ)*(Real.sin (x*u) : ℂ)
  have hf (u : ℝ) (hu : u ∈ Ioi 0) : HasDerivAt f (fp u) u :=
    RiemannRealOrderFractionalDensity.density_profile_hasDerivAt n a t u hu
  have hg (u : ℝ) : HasDerivAt g (gp u) u := by
    convert (((hasDerivAt_id u).const_mul x).cos).ofReal_comp using 1
    · rfl
    · simp [gp,Complex.ofReal_mul,mul_comm]
  have hfg : IntegrableOn (f*gp) (Ioi 0) := by
    apply ((sine_integrable n (by omega) a t x ha ha2).const_mul (-(x : ℂ))).congr
    filter_upwards with u
    simp only [Pi.mul_apply,f,gp]
    ring
  have hzero : Tendsto (f*g) (𝓝[>] (0 : ℝ)) (𝓝 (iteratedDeriv n kernelComplex 0)) := by
    have hc : Continuous g := by dsimp [g]; fun_prop
    have h := (profile_endpoint n hn a t ha).mul
      (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    simpa only [f,Pi.mul_def,g,Complex.ofReal_zero,mul_zero,Real.cos_zero,Complex.ofReal_one,mul_one] using h
  have htop : Tendsto (f*g) atTop (𝓝 0) :=
    bounded_profile_boundary n a t ha ha2 g (fun u => by
      simpa only [g,Complex.norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one (x*u))
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hf (fun u _ => hg u) hfg
    (cosine_integrable (n+1) (by omega) a t x ha ha2) hzero htop
  have he : (∫ u : ℝ in Ioi 0, f u*gp u)= -(x : ℂ)*sineIntegral n a t x := by
    rw [sineIntegral,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with u
    dsimp [f,gp]
    ring
  rw [he,zero_sub] at h
  change -(x : ℂ)*sineIntegral n a t x= -iteratedDeriv n kernelComplex 0-cosineIntegral (n+1) a t x at h
  linear_combination -h

theorem cosine_zero_actual (a t x : ℝ) (ha : 1 < a) :
    cosineIntegral 0 a t x=RiemannRealOrderFlow.flow a t (x : ℂ) := by
  rw [(RiemannRealOrderFractionalDensity.actual_flow_density_integral a t (by linarith) (x : ℂ)).2]
  change (∫ u : ℝ in Ioi 0, RiemannRealOrderFractionalDensity.density a t (u : ℂ)*
    (Real.cos (x*u) : ℂ)) = ∫ u : ℝ in Ici 0,
      RiemannRealOrderFractionalDensity.density a t (u : ℂ)*Complex.cos ((u : ℂ)*(x : ℂ))
  rw [integral_Ici_eq_integral_Ioi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  change RiemannRealOrderFractionalDensity.density a t (u : ℂ)*(Real.cos (x*u) : ℂ)=
    RiemannRealOrderFractionalDensity.density a t (u : ℂ)*Complex.cos ((u : ℂ)*(x : ℂ))
  rw [show (u : ℂ)*(x : ℂ)=((x*u : ℝ) : ℂ) by push_cast; ring,Complex.ofReal_cos]

theorem actual_third_identity (a t x : ℝ) (ha : 1 < a) (ha2 : a ≤ 2) :
    (x : ℂ)^3*RiemannRealOrderFlow.flow a t (x : ℂ)=thirdSine a t x := by
  have h0 := cosine_recurrence 0 (by omega) a t x ha ha2
  have h1 := sine_recurrence 1 (by omega) a t x ha ha2
  have h2 := cosine_recurrence 2 (by omega) a t x ha ha2
  rw [cosine_zero_actual a t x ha] at h0
  have hk := RiemannRealOrderCubicEndpoint.odd_kernel_derivative_zero 1 (by decide)
  rw [hk,zero_add] at h1
  change (x : ℂ)*cosineIntegral 2 a t x= -thirdSine a t x at h2
  linear_combination (x : ℂ)^2*h0-(x : ℂ)*h1-h2

theorem actual_flow_scaled_limit (a t : ℝ) (ha : 1 < a) (ha3 : a < 3/2) :
    Tendsto (fun x : ℝ => ((x^(2*a+1) : ℝ) : ℂ)*RiemannRealOrderFlow.flow a t (x : ℂ)) atTop
      (𝓝 (endpointCoefficient a t*
        ((Real.Gamma (2*a-2)*Real.sin (Real.pi*(2*a-2)/2) : ℝ) : ℂ))) := by
  apply (thirdSine_scaled_limit a t ha ha3).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [← actual_third_identity a t x ha (by linarith)]
  rw [show 2*a+1=(2*a-2)+3 by ring,Real.rpow_add hx]
  have hp : x^(3 : ℝ)=x^(3 : ℕ) := Real.rpow_natCast x 3
  rw [hp]
  push_cast
  ring

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderFractionalReconstruction
