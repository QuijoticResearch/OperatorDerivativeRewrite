import Foundation.RiemannEvenFlow
import Foundation.RiemannQuarticCurvature

/-! Actual maxima and escaping nondegenerate stationary points of the integer
even tilts. Kernel derivative and curvature estimates are reused unchanged;
the tilt derivatives and their order-dependent domains are proved here. -/
noncomputable section
open Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannEvenRealSaddle
open RiemannEvenDomain RiemannQuarticKernel RiemannQuarticCurvature

def phaseSlope (m : ℕ) (t u : ℝ) : ℝ :=
  ((2*m : ℕ) : ℝ)*t*u^(2*m-1)+deriv kernel u/kernel u

theorem weighted_tendsto_zero (m : ℕ) (t : ℝ) :
    Tendsto (weighted m 0 t 0) atTop (nhds 0) :=
  (weighted_isBigO m 0 t 0).trans_tendsto Real.tendsto_exp_neg_atTop_nhds_zero

theorem weighted_pos (m : ℕ) (t u : ℝ) (hu : 0 ≤ u) : 0 < weighted m 0 t 0 u := by
  simpa only [weighted,pow_zero,one_mul,zero_mul,add_zero] using
    mul_pos (Real.exp_pos (t*u^(2*m))) (kernel_pos u hu)

theorem exists_global_max (m : ℕ) (t : ℝ) :
    ∃ u ∈ Ici (0 : ℝ), IsMaxOn (weighted m 0 t 0) (Ici 0) u := by
  have hp := weighted_pos m t 0 le_rfl
  have he : ∀ᶠ u in atTop, weighted m 0 t 0 u < weighted m 0 t 0 0 :=
    (weighted_tendsto_zero m t).eventually (gt_mem_nhds hp)
  obtain ⟨B,hB⟩ := eventually_atTop.1 he
  obtain ⟨u,hu,hm⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) (max B 0)).Nonempty from ⟨0,le_rfl,le_max_right _ _⟩)
    ((weighted_continuousOn m 0 t 0).mono (fun x hx => hx.1))
  refine ⟨u,hu.1,?_⟩
  intro x hx
  by_cases hxu : x ≤ max B 0
  · exact hm ⟨hx,hxu⟩
  · have hBx : B ≤ x := (le_max_left B 0).trans (le_of_lt (lt_of_not_ge hxu))
    exact (hB x hBx).le.trans (hm ⟨le_rfl,le_max_right B 0⟩)

theorem weighted_hasDerivAt (m : ℕ) (t u : ℝ) :
    HasDerivAt (weighted m 0 t 0)
      (Real.exp (t*u^(2*m))*(((2*m : ℕ) : ℝ)*t*u^(2*m-1)*kernel u+deriv kernel u)) u := by
  have h := ((((hasDerivAt_id u).pow (2*m)).const_mul t).exp).mul
    (RiemannQuarticRealSaddle.kernel_hasDerivAt u)
  rw [← (RiemannQuarticRealSaddle.kernel_hasDerivAt u).deriv] at h
  convert h using 1
  · funext x
    simp [weighted]
  · simp only [id_eq,Pi.pow_apply]
    ring

theorem maxima_escape (m : ℕ) (hm : 0 < m) (R : ℝ) (hR : 0 ≤ R) :
    ∀ᶠ t in atTop, ∀ u ∈ Ici (0 : ℝ),
      IsMaxOn (weighted m 0 t 0) (Ici 0) u → R < u := by
  obtain ⟨v,hv,hvmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) R).Nonempty from ⟨0,le_rfl,hR⟩)
    (kernel_continuousOn.mono (fun x hx => hx.1))
  have hb : 0 < kernel (R+1) := kernel_pos _ (by linarith)
  have hgap : 0 < (R+1)^(2*m)-R^(2*m) := by
    apply sub_pos.mpr
    exact pow_lt_pow_left₀ (by linarith : R < R+1) hR (by omega)
  have hlim : Tendsto (fun t : ℝ => Real.exp (t*((R+1)^(2*m)-R^(2*m)))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.atTop_mul_const hgap)
  have he : ∀ᶠ t in atTop, kernel v/kernel (R+1) < Real.exp (t*((R+1)^(2*m)-R^(2*m))) :=
    hlim.eventually (eventually_gt_atTop _)
  filter_upwards [he,eventually_ge_atTop (0 : ℝ)] with t ht ht0
  intro u hu hmax
  by_contra hnot
  have huR : u ≤ R := le_of_not_gt hnot
  have hbase : weighted m 0 t 0 u ≤ Real.exp (t*R^(2*m))*kernel v := by
    have hp : u^(2*m) ≤ R^(2*m) := pow_le_pow_left₀ hu huR _
    have hk := hvmax (show u ∈ Icc (0 : ℝ) R from ⟨hu,huR⟩)
    simp only [weighted,pow_zero,one_mul,zero_mul,add_zero]
    apply mul_le_mul _ hk (kernel_pos u hu).le (Real.exp_pos _).le
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hp ht0)
  have hratio : kernel v < Real.exp (t*((R+1)^(2*m)-R^(2*m)))*kernel (R+1) :=
    (div_lt_iff₀ hb).mp ht
  have hstrict : Real.exp (t*R^(2*m))*kernel v < weighted m 0 t 0 (R+1) := by
    calc
      _ < Real.exp (t*R^(2*m))*(Real.exp (t*((R+1)^(2*m)-R^(2*m)))*kernel (R+1)) :=
        mul_lt_mul_of_pos_left hratio (Real.exp_pos _)
      _ = _ := by
        simp only [weighted,pow_zero,one_mul,zero_mul,add_zero]
        rw [← mul_assoc,← Real.exp_add]
        congr 1
        congr 1
        ring
  exact (not_lt_of_ge (hmax (show R+1 ∈ Ici (0 : ℝ) from by change 0 ≤ R+1; linarith)))
    (hbase.trans_lt hstrict)

theorem max_real_stationary (m : ℕ) (t u : ℝ) (hu : 0 < u)
    (hm : IsMaxOn (weighted m 0 t 0) (Ici 0) u) : phaseSlope m t u = 0 := by
  have hz := (hm.isLocalMax (Ici_mem_nhds hu)).hasDerivAt_eq_zero (weighted_hasDerivAt m t u)
  have hres : ((2*m : ℕ) : ℝ)*t*u^(2*m-1)*kernel u+deriv kernel u = 0 :=
    (mul_eq_zero.mp hz).resolve_left (Real.exp_ne_zero _)
  have hk := ne_of_gt (kernel_pos u hu.le)
  unfold phaseSlope
  field_simp
  simpa using hres

theorem max_complex_stationary (m : ℕ) (t u : ℝ) (hu : 0 < u)
    (hm : IsMaxOn (weighted m 0 t 0) (Ici 0) u) :
    ((2*m : ℕ) : ℂ)*(t : ℂ)*(u : ℂ)^(2*m-1)+
      RiemannThetaComplexKernel.kernelDerivative (u : ℂ)/
        RiemannThetaComplexKernel.kernelComplex (u : ℂ) = 0 := by
  have hs := max_real_stationary m t u hu hm
  unfold phaseSlope at hs
  rw [(RiemannQuarticRealSaddle.kernel_hasDerivAt u).deriv] at hs
  have him : (RiemannThetaComplexKernel.kernelDerivative (u : ℂ)).im = 0 := by
    rw [RiemannQuarticRealSaddle.kernelDerivative_real]
    rfl
  have hcast : RiemannThetaComplexKernel.kernelDerivative (u : ℂ) =
      ((RiemannThetaComplexKernel.kernelDerivative (u : ℂ)).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [hcast,RiemannThetaComplexKernel.kernelComplex_real]
  exact_mod_cast hs

theorem phaseSlope_hasDerivAt (m : ℕ) (t u : ℝ) (hu : 0 ≤ u) :
    HasDerivAt (phaseSlope m t)
      (((2*m : ℕ) : ℝ)*t*((2*m-1 : ℕ) : ℝ)*u^(2*m-2)+realLogCurvature u) u := by
  have h := (((hasDerivAt_id u).pow (2*m-1)).const_mul (((2*m : ℕ) : ℝ)*t)).add
    (realLogSlope_hasDerivAt u hu)
  convert h using 1
  · funext x; rfl
  · have he : 2*m-1-1 = 2*m-2 := by omega
    simp only [id_eq,he,mul_one]
    ring

theorem stationary_phaseSlope_deriv_upper (m : ℕ) (hm : 0 < m) (t u : ℝ)
    (ht : 0 ≤ t) (hu : ((2*m : ℕ) : ℝ) ≤ u) (hs : phaseSlope m t u = 0) :
    deriv (phaseSlope m t) u ≤ -12*Real.pi*Real.exp (4*u)-7 := by
  have hn : 2 ≤ 2*m := by omega
  have hnR : (2 : ℝ) ≤ ((2*m : ℕ) : ℝ) := by exact_mod_cast hn
  have hu1 : 1 ≤ u := by linarith
  have he : 2*m-1 = (2*m-2)+1 := by omega
  have hsub : ((2*m-1 : ℕ) : ℝ) ≤ ((2*m : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le (2*m) 1
  have hp := mul_le_mul_of_nonneg_right (hsub.trans hu) (pow_nonneg (by linarith : 0 ≤ u) (2*m-2))
  have hpow : u^(2*m-1) = u^(2*m-2)*u := by rw [he,pow_succ]
  have hp' : ((2*m-1 : ℕ) : ℝ)*u^(2*m-2) ≤ u^(2*m-1) := by
    rw [hpow]
    nlinarith
  have ha : 0 ≤ ((2*m : ℕ) : ℝ)*t := mul_nonneg (Nat.cast_nonneg _) ht
  have hmul := mul_le_mul_of_nonneg_left hp' ha
  have hl := realLogSlope_lower u hu1
  have hc := realLogCurvature_upper u hu1
  rw [(phaseSlope_hasDerivAt m t u (by linarith)).deriv]
  unfold phaseSlope at hs
  nlinarith

theorem stationary_scale_bounds (m : ℕ) (t u : ℝ) (hu : 1 ≤ u)
    (hs : phaseSlope m t u = 0) :
    4*Real.pi*Real.exp (4*u)-12 ≤ ((2*m : ℕ) : ℝ)*t*u^(2*m-1) ∧
      ((2*m : ℕ) : ℝ)*t*u^(2*m-1) ≤ 4*Real.pi*Real.exp (4*u)-8 := by
  have hv := exp_four_ge_sixteen u hu
  have hf := leading0_lower (Real.exp (4*u)) (by linarith)
  have hf0 : 0 < leading0 (Real.exp (4*u)) := by linarith
  have hr : 12/leading0 (Real.exp (4*u)) ≤ 1 := (div_le_iff₀ hf0).mpr (by linarith)
  have hh := (abs_le.mp (realLogSlope_bound u hu)).2
  have hl := realLogSlope_lower u hu
  unfold phaseSlope at hs
  constructor <;> linarith

theorem eventually_all_maxima_nondegenerate (m : ℕ) (hm : 0 < m) :
    ∀ᶠ t : ℝ in atTop, ∀ u ∈ Ici (0 : ℝ),
      IsMaxOn (weighted m 0 t 0) (Ici 0) u →
        phaseSlope m t u = 0 ∧ deriv (phaseSlope m t) u < 0 := by
  filter_upwards [maxima_escape m hm ((2*m : ℕ) : ℝ) (Nat.cast_nonneg _),
    eventually_ge_atTop (0 : ℝ)] with t hescape ht
  intro u hu hmax
  have hlarge := hescape u hu hmax
  have hn : (0 : ℝ) < ((2*m : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*m by omega)
  have hs := max_real_stationary m t u (lt_trans hn hlarge) hmax
  refine ⟨hs,?_⟩
  have h := stationary_phaseSlope_deriv_upper m hm t u ht hlarge.le hs
  nlinarith [mul_pos Real.pi_pos (Real.exp_pos (4*u))]

theorem eventually_exists_nondegenerate_saddle (m : ℕ) (hm : 0 < m) (R : ℝ) (hR : 0 ≤ R) :
    ∀ᶠ t : ℝ in atTop, ∃ u : ℝ, R < u ∧
      IsMaxOn (weighted m 0 t 0) (Ici 0) u ∧ phaseSlope m t u = 0 ∧
      deriv (phaseSlope m t) u < 0 := by
  filter_upwards [maxima_escape m hm R hR,eventually_all_maxima_nondegenerate m hm] with t he hn
  obtain ⟨u,hu,hmax⟩ := exists_global_max m t
  exact ⟨u,he u hu hmax,hmax,hn u hu hmax⟩

theorem sixth_order_eventually_exists_nondegenerate_saddle (R : ℝ) (hR : 0 ≤ R) :
    ∀ᶠ t : ℝ in atTop, ∃ u : ℝ, R < u ∧
      IsMaxOn (weighted 3 0 t 0) (Ici 0) u ∧
      6*t*u^5+deriv kernel u/kernel u = 0 ∧ deriv (phaseSlope 3 t) u < 0 := by
  simpa [phaseSlope] using eventually_exists_nondegenerate_saddle 3 (by norm_num) R hR

end OperatorDerivativeRewrite.Foundation.RiemannEvenRealSaddle
