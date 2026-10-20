import Foundation.RiemannEvenNormalizedCompact

/-! Exponentially weighted first-moment tails for the actual integer-even
kernel. These are genuine integral estimates, with constants independent of
the frequency weight and the truncation radius. -/
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannEvenWeightedTails
open RiemannEvenDomain RiemannEvenRealSaddle RiemannEvenSaddleTimes
open RiemannEvenConcentration RiemannEvenNormalizedCompact

theorem actual_right_weighted_pointwise (m : ℕ) (hm : 0 < m) (t u B s : ℝ)
    (ht : 0 < t) (hu : ((2*m : ℕ) : ℝ) ≤ u) (hs : 0 ≤ s)
    (hstat : phaseSlope m t u = 0) :
    s*Real.exp (B*s)*weighted m 0 t 0 (u+s) ≤
      (weighted m 0 t 0 u*Real.exp (B^2/(2*t)))*(s*Real.exp (-(t/2)*s^2)) := by
  have hn : (2 : ℝ) ≤ ((2*m : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ 2*m by omega)
  have hu0 : 0 ≤ u := by linarith
  have hp : 1 ≤ u^(2*m-1) := one_le_pow₀ (by linarith : 1 ≤ u)
  have hnp := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (2*m) : (0 : ℝ) ≤ ((2*m : ℕ) : ℝ))
  have hnt := mul_le_mul_of_nonneg_right (hn.trans (by simpa using hnp)) ht.le
  have hc : t ≤ (3/2 : ℝ)*((2*m : ℕ) : ℝ)*t*u^(2*m-1) := by nlinarith
  have hg := actual_right_gaussian_envelope m hm t u (u+s) hu (by linarith) hstat
  rw [show (u+s)-u = s by ring] at hg
  have hy : B*s-t*s^2 ≤ B^2/(2*t)-(t/2)*s^2 := by
    have h := sq_nonneg (t*s-B)
    have hd : B^2/(2*t)*(2*t) = B^2 := by field_simp
    nlinarith
  have hpow := mul_le_mul_of_nonneg_right hc (sq_nonneg s)
  have he : Real.exp (B*s-(3/2 : ℝ)*((2*m : ℕ) : ℝ)*t*u^(2*m-1)*s^2) ≤
      Real.exp (B^2/(2*t)-(t/2)*s^2) := Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ s*Real.exp (B*s)*(weighted m 0 t 0 u*
        Real.exp (-((3/2 : ℝ)*((2*m : ℕ) : ℝ)*t*u^(2*m-1))*s^2)) :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ = weighted m 0 t 0 u*s*Real.exp (B*s-(3/2 : ℝ)*((2*m : ℕ) : ℝ)*t*u^(2*m-1)*s^2) := by
      rw [show s*Real.exp (B*s)*(weighted m 0 t 0 u*Real.exp (-((3/2 : ℝ)*((2*m : ℕ) : ℝ)*t*u^(2*m-1))*s^2)) =
        weighted m 0 t 0 u*s*(Real.exp (B*s)*Real.exp (-((3/2 : ℝ)*((2*m : ℕ) : ℝ)*t*u^(2*m-1))*s^2)) by ring]
      rw [← Real.exp_add]
      congr 2 <;> ring
    _ ≤ weighted m 0 t 0 u*s*Real.exp (B^2/(2*t)-(t/2)*s^2) :=
      mul_le_mul_of_nonneg_left he (mul_nonneg (weighted_pos m t u hu0).le hs)
    _ = _ := by
      rw [show B^2/(2*t)-(t/2)*s^2 = B^2/(2*t)+(-(t/2)*s^2) by ring,Real.exp_add]
      ring

theorem actual_right_weighted_integrable (m : ℕ) (hm : 0 < m) (t u B r : ℝ)
    (ht : 0 < t) (hu : ((2*m : ℕ) : ℝ) ≤ u) (hr : 0 ≤ r)
    (hstat : phaseSlope m t u = 0) :
    IntegrableOn (fun s : ℝ => s*Real.exp (B*s)*weighted m 0 t 0 (u+s)) (Ioi r) := by
  have hg : Integrable (fun s : ℝ =>
      (weighted m 0 t 0 u*Real.exp (B^2/(2*t)))*(s*Real.exp (-(t/2)*s^2))) :=
    (integrable_mul_exp_neg_mul_sq (by positivity : 0 < t/2)).const_mul _
  have hcont : Continuous (fun s : ℝ => s*Real.exp (B*s)*weighted m 0 t 0 (u+s)) := by
    have hw : Continuous (fun s : ℝ => weighted m 0 t 0 (u+s)) :=
      continuous_iff_continuousAt.mpr (fun s => (weighted_hasDerivAt m t (u+s)).continuousAt.comp (by fun_prop))
    exact (by fun_prop : Continuous (fun s : ℝ => s*Real.exp (B*s))).mul hw
  apply hg.integrableOn.mono' hcont.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : 0 ≤ s := hr.trans (le_of_lt hs)
  have hu0 : 0 ≤ u := (Nat.cast_nonneg _).trans hu
  have hw := (weighted_pos m t (u+s) (by linarith)).le
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ s*Real.exp (B*s)*weighted m 0 t 0 (u+s))]
  exact actual_right_weighted_pointwise m hm t u B s ht hu hs0 hstat

theorem actual_right_weighted_integral_bound (m : ℕ) (hm : 0 < m) (t u B r : ℝ)
    (ht : 0 < t) (hu : ((2*m : ℕ) : ℝ) ≤ u) (hr : 0 ≤ r)
    (hstat : phaseSlope m t u = 0) :
    (∫ s : ℝ in Ioi r, s*Real.exp (B*s)*weighted m 0 t 0 (u+s)) ≤
      (weighted m 0 t 0 u/t)*Real.exp (B^2/(2*t)-(t/2)*r^2) := by
  have hg : Integrable (fun s : ℝ =>
      (weighted m 0 t 0 u*Real.exp (B^2/(2*t)))*(s*Real.exp (-(t/2)*s^2))) :=
    (integrable_mul_exp_neg_mul_sq (by positivity : 0 < t/2)).const_mul _
  have hb := setIntegral_mono_on
    (actual_right_weighted_integrable m hm t u B r ht hu hr hstat) hg.integrableOn
    measurableSet_Ioi (fun s hs => actual_right_weighted_pointwise m hm t u B s ht hu
      (hr.trans (le_of_lt hs)) hstat)
  rw [integral_const_mul,RiemannQuarticGaussianTail.first_moment_tail (t/2) r (by positivity)] at hb
  convert hb using 1
  rw [show B^2/(2*t)-(t/2)*r^2 = B^2/(2*t)+(-(t/2)*r^2) by ring,Real.exp_add]
  field_simp

theorem exists_normalized_right_weighted_bound (m : ℕ) (hm : 0 < m) :
    ∃ K : ℝ, 0 < K ∧ ∀ (B r t u : ℝ), 0 ≤ r → 1 ≤ t → ((2*m : ℕ) : ℝ) ≤ u →
      IsMaxOn (weighted m 0 t 0) (Ici 0) u →
      (∫ s : ℝ in Ioi r, s*Real.exp (B*s)*weighted m 0 t 0 (u+s))/
        (RiemannEvenFlow.flow m t 0).re ≤ K*Real.exp (B^2/(2*t)-(t/2)*r^2) := by
  obtain ⟨K,hK,hpeak⟩ := exists_peak_normalization_bound m hm
  refine ⟨K,hK,?_⟩
  intro B r t u hr ht hu hmax
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hn : (0 : ℝ) < ((2*m : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*m by omega)
  have hu0 := lt_of_lt_of_le hn hu
  have hstat := max_real_stationary m t u hu0 hmax
  have hM := actual_flow_zero_pos m t
  have hbound := actual_right_weighted_integral_bound m hm t u B r ht0 hu hr hstat
  have hp : weighted m 0 t 0 u/t ≤ K*(RiemannEvenFlow.flow m t 0).re :=
    (div_le_iff₀ ht0).mpr (by convert hpeak t u ht0.le hu hmax using 1 <;> ring)
  apply (div_le_iff₀ hM).mpr
  calc
    _ ≤ (weighted m 0 t 0 u/t)*Real.exp (B^2/(2*t)-(t/2)*r^2) := hbound
    _ ≤ (K*(RiemannEvenFlow.flow m t 0).re)*Real.exp (B^2/(2*t)-(t/2)*r^2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact hp
    _ = _ := by ring

theorem actual_left_weighted_integral_bound (m : ℕ) (t u B r : ℝ)
    (hB : 0 ≤ B) (hr : 0 ≤ r) (hu : r ≤ u) :
    (∫ v : ℝ in 0..(u-r), (u-v)*Real.exp (B*(u-v))*weighted m 0 t 0 v) ≤
      (u*Real.exp (B*u))*(∫ v : ℝ in 0..(u-r), weighted m 0 t 0 v) := by
  have hcont : Continuous (weighted m 0 t 0) := continuous_iff_continuousAt.mpr
    (fun v => (weighted_hasDerivAt m t v).continuousAt)
  have hi : Continuous (fun v : ℝ => (u-v)*Real.exp (B*(u-v))*weighted m 0 t 0 v) :=
    (by fun_prop : Continuous (fun v : ℝ => (u-v)*Real.exp (B*(u-v)))).mul hcont
  have hj : Continuous (fun v : ℝ => (u*Real.exp (B*u))*weighted m 0 t 0 v) :=
    continuous_const.mul hcont
  have hpoint (v : ℝ) (hv : v ∈ Icc (0 : ℝ) (u-r)) :
      (u-v)*Real.exp (B*(u-v))*weighted m 0 t 0 v ≤
        (u*Real.exp (B*u))*weighted m 0 t 0 v := by
    have huv : 0 ≤ u-v := by linarith [hv.2]
    have hu0 : 0 ≤ u := hr.trans hu
    have he : Real.exp (B*(u-v)) ≤ Real.exp (B*u) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hv.1]) hB)
    have hp := mul_le_mul (show u-v ≤ u by linarith [hv.1]) he (Real.exp_pos _).le hu0
    exact mul_le_mul_of_nonneg_right hp (weighted_pos m t v hv.1).le
  have hb := intervalIntegral.integral_mono_on (sub_nonneg.mpr hu)
    (hi.intervalIntegrable (μ := volume) 0 (u-r))
    (hj.intervalIntegrable (μ := volume) 0 (u-r)) hpoint
  simpa only [intervalIntegral.integral_const_mul] using hb

theorem exists_normalized_left_weighted_bound (m : ℕ) (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B r t u : ℝ), 0 ≤ B → 0 < r → r ≤ 1/2 →
      1 ≤ t → ((2*m : ℕ) : ℝ)+r ≤ u →
      IsMaxOn (weighted m 0 t 0) (Ici 0) u →
      (∫ v : ℝ in 0..(u-r), (u-v)*Real.exp (B*(u-v))*weighted m 0 t 0 v)/
        (RiemannEvenFlow.flow m t 0).re ≤
      C*u*Real.exp (B*u)*(t*Real.exp (-t*((((2*m : ℕ) : ℝ)+1)^(2*m)-(((2*m : ℕ) : ℝ))^(2*m)))+
        t^2*Real.exp (-t*r^2)) := by
  let n : ℝ := ((2*m : ℕ) : ℝ)
  obtain ⟨C,hC,hcompact⟩ := exists_normalized_compact_bound m hm n (Nat.cast_nonneg _)
  obtain ⟨D,hD,hsegment⟩ := exists_normalized_left_segment_bound m hm
  refine ⟨C+D,add_pos hC hD,?_⟩
  intro B r t u hB hr hrhalf ht hu hmax
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have huN : n ≤ u := by change n+r ≤ u at hu; linarith
  have hu0 : 0 ≤ u := (Nat.cast_nonneg _).trans huN
  have hur : r ≤ u := by change n+r ≤ u at hu; have hn : 0 ≤ n := Nat.cast_nonneg _; linarith
  have hc := hcompact t u ht0 huN hmax
  have hd := hsegment r hr hrhalf t u ht hu hmax
  have hcont : Continuous (weighted m 0 t 0) := continuous_iff_continuousAt.mpr
    (fun v => (weighted_hasDerivAt m t v).continuousAt)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) 0 n)
    (hcont.intervalIntegrable (μ := volume) n (u-r))
  have hM := actual_flow_zero_pos m t
  have hleft := actual_left_weighted_integral_bound m t u B r hB hr.le hur
  have hdiv := div_le_div_of_nonneg_right hleft hM.le
  rw [mul_div_assoc,← hsplit,add_div] at hdiv
  have hf : 0 ≤ u*Real.exp (B*u) := by positivity
  have he1 : 0 ≤ t*Real.exp (-t*((n+1)^(2*m)-n^(2*m))) := by positivity
  have he2 : 0 ≤ t^2*Real.exp (-t*r^2) := by positivity
  have hb : (∫ v : ℝ in 0..n, weighted m 0 t 0 v)/(RiemannEvenFlow.flow m t 0).re +
      (∫ v : ℝ in n..(u-r), weighted m 0 t 0 v)/(RiemannEvenFlow.flow m t 0).re ≤
      (C+D)*(t*Real.exp (-t*((n+1)^(2*m)-n^(2*m)))+t^2*Real.exp (-t*r^2)) := by
    have hh1 := mul_nonneg hD.le he1
    have hh2 := mul_nonneg hC.le he2
    nlinarith [hc,hd]
  exact hdiv.trans (by
    have hh := mul_le_mul_of_nonneg_left hb hf
    convert hh using 1 <;> ring)

theorem normalized_local_weighted_bound (m : ℕ) (t u B r : ℝ)
    (hB : 0 ≤ B) (hr : 0 ≤ r) (hu : r ≤ u) :
    (∫ v : ℝ in (u-r)..(u+r), |v-u| * Real.exp (B*|v-u|) * weighted m 0 t 0 v)/
      (RiemannEvenFlow.flow m t 0).re ≤ r*Real.exp (B*r) := by
  have hcont : Continuous (weighted m 0 t 0) := continuous_iff_continuousAt.mpr
    (fun v => (weighted_hasDerivAt m t v).continuousAt)
  have hi : Continuous (fun v : ℝ => |v-u| * Real.exp (B*|v-u|) * weighted m 0 t 0 v) :=
    (by fun_prop : Continuous (fun v : ℝ => |v-u| * Real.exp (B*|v-u|))).mul hcont
  have hj : Continuous (fun v : ℝ => (r*Real.exp (B*r))*weighted m 0 t 0 v) :=
    continuous_const.mul hcont
  have hends : u-r ≤ u+r := by linarith
  have hpoint (v : ℝ) (hv : v ∈ Icc (u-r) (u+r)) :
      |v-u| * Real.exp (B*|v-u|) * weighted m 0 t 0 v ≤
        (r*Real.exp (B*r))*weighted m 0 t 0 v := by
    have hd : |v-u| ≤ r := abs_le.mpr ⟨by linarith [hv.1],by linarith [hv.2]⟩
    have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hd hB)
    have hv0 : 0 ≤ v := by linarith [hv.1]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hd he (Real.exp_pos _).le hr) (weighted_pos m t v hv0).le
  have hb := intervalIntegral.integral_mono_on hends
    (hi.intervalIntegrable (μ := volume) (u-r) (u+r))
    (hj.intervalIntegrable (μ := volume) (u-r) (u+r)) hpoint
  rw [intervalIntegral.integral_const_mul] at hb
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ici (0 : ℝ))] weighted m 0 t 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with v hv
    exact (weighted_pos m t v hv).le
  have hsub : Ioc (u-r) (u+r) ≤ᵐ[volume] Ici (0 : ℝ) :=
    Eventually.of_forall (fun v hv => by change 0 ≤ v; linarith [hv.1])
  have hm := setIntegral_mono_set (weighted_integrable m 0 t 0) hnonneg hsub
  rw [← intervalIntegral.integral_of_le hends] at hm
  have hM := actual_flow_zero_pos m t
  apply (div_le_iff₀ hM).mpr
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ r*Real.exp (B*r) by positivity)
  simpa only [RiemannEvenNormalization.flow_zero_eq_mass,Complex.ofReal_re] using hh

theorem actual_centered_exponential_moment_integrable (m : ℕ) (t u B : ℝ)
    (hu : 0 ≤ u) (hB : 0 ≤ B) :
    IntegrableOn (fun v : ℝ => |v-u| * Real.exp (B*|v-u|) * weighted m 0 t 0 v) (Ici 0) := by
  have hg : IntegrableOn (fun v : ℝ => Real.exp (B*u)*
      (u*weighted m 0 t B v+weighted m 1 t B v)) (Ici 0) :=
    (((weighted_integrable m 0 t B).const_mul u).add (weighted_integrable m 1 t B)).const_mul _
  have hcont : Continuous (fun v : ℝ => |v-u| * Real.exp (B*|v-u|) * weighted m 0 t 0 v) := by
    have hw : Continuous (weighted m 0 t 0) := continuous_iff_continuousAt.mpr
      (fun v => (weighted_hasDerivAt m t v).continuousAt)
    exact (by fun_prop : Continuous (fun v : ℝ => |v-u| * Real.exp (B*|v-u|))).mul hw
  apply hg.mono' hcont.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ici] with v hv
  have hv0 : 0 ≤ v := hv
  have hd : |v-u| ≤ u+v := abs_le.mpr ⟨by linarith,by linarith⟩
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hd hB)
  have hw := (weighted_pos m t v hv).le
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity :
    0 ≤ |v-u| * Real.exp (B*|v-u|) * weighted m 0 t 0 v)]
  calc
    _ ≤ ((u+v)*Real.exp (B*(u+v)))*weighted m 0 t 0 v :=
      mul_le_mul_of_nonneg_right (mul_le_mul hd he (Real.exp_pos _).le (by positivity)) hw
    _ = _ := by
      simp only [weighted,pow_zero,pow_one,one_mul,zero_mul,add_zero]
      rw [show B*(u+v) = B*u+B*v by ring,Real.exp_add]
      rw [Real.exp_add (t*v^(2*m)) (B*v)]
      ring

end OperatorDerivativeRewrite.Foundation.RiemannEvenWeightedTails
