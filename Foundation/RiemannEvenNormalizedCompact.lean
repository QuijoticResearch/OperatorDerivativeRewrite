import Foundation.RiemannEvenCompactMass
import Foundation.RiemannEvenNormalization

/-! Actual compact mass, normalized by the actual flow value at zero, tends
to zero. The normalization budget is controlled by the exact saddle time;
no unspecified peak choice or assumed probabilistic limit is used. -/
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannEvenNormalizedCompact
open RiemannQuarticKernel RiemannEvenDomain RiemannEvenRealSaddle RiemannEvenSaddleTimes
open RiemannEvenConcentration RiemannEvenCompactMass RiemannEvenNormalization

theorem sqrt_budget_exp_bound (u : ℝ) (hu : 0 ≤ u) :
    Real.sqrt (8*Real.pi*Real.exp (4*u+2)+2) ≤ (8*Real.pi*Real.exp 2+3)*Real.exp (3*u) := by
  let A : ℝ := 8*Real.pi*Real.exp 2+3
  have hA : 3 ≤ A := by
    have hp : 0 ≤ 8*Real.pi*Real.exp 2 := by positivity
    dsimp [A]
    linarith
  have h46 : Real.exp (4*u) ≤ Real.exp (6*u) := Real.exp_le_exp.mpr (by linarith)
  have h6 : 1 ≤ Real.exp (6*u) := Real.one_le_exp (by positivity)
  have hp := mul_le_mul_of_nonneg_left h46 (show 0 ≤ 8*Real.pi*Real.exp 2 by positivity)
  have hcoef : 8*Real.pi*Real.exp 2+2 ≤ A^2 := by dsimp [A] at *; nlinarith
  have hm := mul_le_mul_of_nonneg_right hcoef (Real.exp_pos (6*u)).le
  apply Real.sqrt_le_iff.mpr ⟨by positivity,?_⟩
  have he : Real.exp (4*u+2) = Real.exp (4*u)*Real.exp 2 := Real.exp_add _ _
  have heq : (A*Real.exp (3*u))^2 = A^2*Real.exp (6*u) := by
    have hexp : (Real.exp (3*u))^2 = Real.exp (6*u) := by
      rw [pow_two,← Real.exp_add]
      congr 1
      ring
    rw [mul_pow,hexp]
  change 8*Real.pi*Real.exp (4*u+2)+2 ≤ (A*Real.exp (3*u))^2
  rw [heq,he]
  nlinarith

theorem exists_sqrt_budget_saddleTime_bound (m : ℕ) (hm : 0 < m) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : ℝ, ((2*m : ℕ) : ℝ) ≤ u →
      Real.sqrt (8*Real.pi*Real.exp (4*u+2)+2) ≤ K*saddleTime m u := by
  let n : ℝ := ((2*m : ℕ) : ℝ)
  let A : ℝ := 8*Real.pi*Real.exp 2+3
  have hn : 2 ≤ n := by dsimp [n]; exact_mod_cast (show 2 ≤ 2*m by omega)
  have hT : 0 < saddleTime m n := saddleTime_pos m hm n (by linarith)
  let K : ℝ := A*Real.exp (3*n)/saddleTime m n
  have hK : 0 < K := by dsimp [K,A]; positivity
  refine ⟨K,hK,?_⟩
  intro u hu
  have hg := saddleTime_exponential_lower m hm n u le_rfl hu
  have hp := mul_le_mul_of_nonneg_left hg hK.le
  have hid : K*(saddleTime m n*Real.exp (3*(u-n))) = A*Real.exp (3*u) := by
    dsimp [K]
    rw [show A*Real.exp (3*n)/saddleTime m n*(saddleTime m n*Real.exp (3*(u-n))) =
      A*(Real.exp (3*n)*Real.exp (3*(u-n))) by field_simp]
    rw [← Real.exp_add,show 3*n+3*(u-n) = 3*u by ring]
  exact (sqrt_budget_exp_bound u (by change n ≤ u at hu; linarith)).trans (by rw [← hid]; exact hp)

theorem actual_flow_zero_pos (m : ℕ) (t : ℝ) : 0 < (RiemannEvenFlow.flow m t 0).re := by
  rw [flow_zero_eq_mass,Complex.ofReal_re]
  change 0 < ∫ v : ℝ in Ici 0, weighted m 0 t 0 v
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (μ := volume) (s := Ici (0 : ℝ))
    (by filter_upwards [ae_restrict_mem measurableSet_Ici] with v hv; exact (weighted_pos m t v hv).le)
    (weighted_integrable m 0 t 0)).mpr
  have hsub : Icc (0 : ℝ) 1 ⊆ Function.support (weighted m 0 t 0) ∩ Ici 0 := by
    intro v hv
    exact ⟨(weighted_pos m t v hv.1).ne',hv.1⟩
  exact lt_of_lt_of_le (by simp : 0 < volume (Icc (0 : ℝ) 1)) (measure_mono hsub)

theorem exists_peak_normalization_bound (m : ℕ) (hm : 0 < m) :
    ∃ K : ℝ, 0 < K ∧ ∀ (t u : ℝ), 0 ≤ t → ((2*m : ℕ) : ℝ) ≤ u →
      IsMaxOn (weighted m 0 t 0) (Ici 0) u →
        weighted m 0 t 0 u ≤ K*t*(RiemannEvenFlow.flow m t 0).re := by
  obtain ⟨K,hK,hbudget⟩ := exists_sqrt_budget_saddleTime_bound m hm
  let B : ℝ := 2*Real.exp (-1)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨K/B,by positivity,?_⟩
  intro t u ht hu hmax
  have hn : (2 : ℝ) ≤ ((2*m : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ 2*m by omega)
  have hu2 : 2 ≤ u := hn.trans hu
  have hu0 : 0 < u := by linarith
  have hs := max_real_stationary m t u hu0 hmax
  have hM := actual_flow_zero_pos m t
  have hl := actual_halfline_mass_lower m t u ht hu2 hs
  rw [← Complex.ofReal_re (∫ v : ℝ, weighted m 0 t 0 v ∂RiemannQuarticFlow.halfLine),
    ← flow_zero_eq_mass] at hl
  have hscale := hbudget u hu
  rw [max_saddleTime m hm t u hu0 hmax] at hscale
  let q := Real.sqrt (8*Real.pi*Real.exp (4*u+2)+2)
  have hq : 0 < q := by dsimp [q]; positivity
  have ha : weighted m 0 t 0 u*B ≤ q*(RiemannEvenFlow.flow m t 0).re := by
    have hp := mul_le_mul_of_nonneg_left hl hq.le
    change q*(weighted m 0 t 0 u*(B/q)) ≤ q*(RiemannEvenFlow.flow m t 0).re at hp
    convert hp using 1
    field_simp
  have ha' : weighted m 0 t 0 u ≤ (K/B)*t*(RiemannEvenFlow.flow m t 0).re := by
    have hp := ha.trans (mul_le_mul_of_nonneg_right hscale hM.le)
    have hd := (le_div_iff₀ hB).mpr hp
    convert hd using 1 <;> ring
  exact ha'

theorem exists_normalized_compact_bound (m : ℕ) (hm : 0 < m) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t u : ℝ), 0 ≤ t → ((2*m : ℕ) : ℝ) ≤ u →
      IsMaxOn (weighted m 0 t 0) (Ici 0) u →
      (∫ v : ℝ in 0..R, weighted m 0 t 0 v)/(RiemannEvenFlow.flow m t 0).re ≤
        C*t*Real.exp (-t*((R+1)^(2*m)-R^(2*m))) := by
  obtain ⟨C,hC,hcompact⟩ := exists_compact_mass_envelope m hm R hR
  obtain ⟨K,hK,hpeak⟩ := exists_peak_normalization_bound m hm
  refine ⟨C*K,mul_pos hC hK,?_⟩
  intro t u ht hu hmax
  have hM := actual_flow_zero_pos m t
  have hu0 : 0 ≤ u := (Nat.cast_nonneg _).trans hu
  have ha := hpeak t u ht hu hmax
  apply (div_le_iff₀ hM).mpr
  have hi := hcompact t u ht hu0 hmax
  calc
    _ ≤ C*Real.exp (-t*((R+1)^(2*m)-R^(2*m)))*weighted m 0 t 0 u := hi
    _ ≤ C*Real.exp (-t*((R+1)^(2*m)-R^(2*m)))*(K*t*(RiemannEvenFlow.flow m t 0).re) :=
      mul_le_mul_of_nonneg_left ha (by positivity)
    _ = _ := by ring

theorem normalized_compact_mass_tendsto_zero (m : ℕ) (hm : 0 < m) (R : ℝ) (hR : 0 ≤ R) :
    Tendsto (fun t : ℝ => (∫ v : ℝ in 0..R, weighted m 0 t 0 v)/
      (RiemannEvenFlow.flow m t 0).re) atTop (nhds 0) := by
  obtain ⟨C,hC,hbound⟩ := exists_normalized_compact_bound m hm R hR
  have hgap := compact_exponent_gap_pos m hm R hR
  have hlim : Tendsto (fun t : ℝ => C*t*Real.exp (-t*((R+1)^(2*m)-R^(2*m)))) atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ)
      ((R+1)^(2*m)-R^(2*m)) hgap).const_mul C
    simpa only [Real.rpow_one,mul_zero,mul_assoc,mul_comm,mul_left_comm,neg_mul,mul_neg] using h
  have hc : ∀ᶠ t : ℝ in atTop,
      0 ≤ (∫ v : ℝ in 0..R, weighted m 0 t 0 v)/(RiemannEvenFlow.flow m t 0).re ∧
        (∫ v : ℝ in 0..R, weighted m 0 t 0 v)/(RiemannEvenFlow.flow m t 0).re ≤
          C*t*Real.exp (-t*((R+1)^(2*m)-R^(2*m))) := by
    filter_upwards [maxima_escape m hm ((2*m : ℕ) : ℝ) (Nat.cast_nonneg _),
      eventually_ge_atTop (0 : ℝ)] with t he ht
    obtain ⟨u,hu,hmax⟩ := exists_global_max m t
    have huN := (he u hu hmax).le
    have hM := actual_flow_zero_pos m t
    have hnum : 0 ≤ ∫ v : ℝ in 0..R, weighted m 0 t 0 v :=
      intervalIntegral.integral_nonneg hR (fun v hv => (weighted_pos m t v hv.1).le)
    exact ⟨div_nonneg hnum hM.le,hbound t u ht huN hmax⟩
  exact squeeze_zero' (hc.mono fun _ h => h.1) (hc.mono fun _ h => h.2) hlim

theorem exists_normalized_right_tail_bound (m : ℕ) (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ (t u : ℝ), 1 ≤ t → ((2*m : ℕ) : ℝ) ≤ u →
      IsMaxOn (weighted m 0 t 0) (Ici 0) u →
      (∫ s : ℝ in Ioi r, weighted m 0 t 0 (u+s))/(RiemannEvenFlow.flow m t 0).re ≤
        (C/r)*Real.exp (-t*r^2) := by
  obtain ⟨K,hK,hpeak⟩ := exists_peak_normalization_bound m hm
  refine ⟨K/2,by positivity,?_⟩
  intro r hr t u ht hu hmax
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hn : (2 : ℝ) ≤ ((2*m : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ 2*m by omega)
  have hu0 : 0 < u := by linarith
  have hs := max_real_stationary m t u hu0 hmax
  let c : ℝ := (3/2 : ℝ)*((2*m : ℕ) : ℝ)*t*u^(2*m-1)
  have hpow : 1 ≤ u^(2*m-1) := one_le_pow₀ (by linarith : 1 ≤ u)
  have hnp := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg (2*m) : (0 : ℝ) ≤ ((2*m : ℕ) : ℝ))
  have hnt := mul_le_mul_of_nonneg_right (hn.trans (by simpa using hnp)) ht0.le
  have htc : t ≤ c := by dsimp [c]; nlinarith
  have hc : 0 < c := lt_of_lt_of_le ht0 htc
  have htail := actual_right_tail_integral_bound m hm t u r hu hr hs
  change (∫ s : ℝ in Ioi r, weighted m 0 t 0 (u+s)) ≤
    weighted m 0 t 0 u*Real.exp (-c*r^2)/(2*c*r) at htail
  have he : Real.exp (-c*r^2) ≤ Real.exp (-t*r^2) := by
    apply Real.exp_le_exp.mpr
    have hp := mul_le_mul_of_nonneg_right htc (sq_nonneg r)
    linarith
  have hden : 2*t*r ≤ 2*c*r := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left htc (by norm_num : (0 : ℝ) ≤ 2)) hr.le
  have hg : Real.exp (-c*r^2)/(2*c*r) ≤ Real.exp (-t*r^2)/(2*t*r) := by
    exact (div_le_div_of_nonneg_right he (by positivity)).trans
      (div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) hden)
  have hM := actual_flow_zero_pos m t
  have hp := hpeak t u ht0.le hu hmax
  apply (div_le_iff₀ hM).mpr
  calc
    _ ≤ weighted m 0 t 0 u*(Real.exp (-c*r^2)/(2*c*r)) := by simpa only [mul_div_assoc] using htail
    _ ≤ weighted m 0 t 0 u*(Real.exp (-t*r^2)/(2*t*r)) :=
      mul_le_mul_of_nonneg_left hg (weighted_pos m t u hu0.le).le
    _ ≤ (K*t*(RiemannEvenFlow.flow m t 0).re)*(Real.exp (-t*r^2)/(2*t*r)) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by field_simp

theorem normalized_right_tail_eventually_small (m : ℕ) (hm : 0 < m) (r ε : ℝ)
    (hr : 0 < r) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ u ∈ Ici (0 : ℝ),
      IsMaxOn (weighted m 0 t 0) (Ici 0) u →
        (∫ s : ℝ in Ioi r, weighted m 0 t 0 (u+s))/(RiemannEvenFlow.flow m t 0).re < ε := by
  obtain ⟨C,hC,hbound⟩ := exists_normalized_right_tail_bound m hm
  have hlim : Tendsto (fun t : ℝ => (C/r)*Real.exp (-t*r^2)) atTop (nhds 0) := by
    have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.atTop_mul_const (sq_pos_of_pos hr))).const_mul (C/r)
    simpa only [Function.comp_def,mul_zero,neg_mul,id_eq] using h
  filter_upwards [hlim.eventually (gt_mem_nhds hε),
    maxima_escape m hm ((2*m : ℕ) : ℝ) (Nat.cast_nonneg _),
    eventually_ge_atTop (1 : ℝ)] with t hsmall he ht
  intro u hu hmax
  exact (hbound r hr t u ht (he u hu hmax).le hmax).trans_lt hsmall

theorem exists_center_linear_bound (m : ℕ) (hm : 0 < m) :
    ∃ L : ℝ, 0 < L ∧ ∀ (t u : ℝ), 1 ≤ t → ((2*m : ℕ) : ℝ) ≤ u →
      phaseSlope m t u = 0 → u ≤ L*t := by
  let n : ℝ := ((2*m : ℕ) : ℝ)
  have hn : 2 ≤ n := by dsimp [n]; exact_mod_cast (show 2 ≤ 2*m by omega)
  have hT : 0 < saddleTime m n := saddleTime_pos m hm n (by linarith)
  refine ⟨n+1/saddleTime m n,by positivity,?_⟩
  intro t u ht hu hs
  have hu0 : 0 < u := by change n ≤ u at hu; linarith
  have hg := saddleTime_linear_lower m hm n u le_rfl hu
  rw [phaseSlope_zero_saddleTime m hm t u hu0 hs] at hg
  have hd : 0 ≤ u-n := sub_nonneg.mpr hu
  have hlin : (u-n)*saddleTime m n ≤ t := by nlinarith
  have hdiv := (le_div_iff₀ hT).mpr hlin
  have hnt := mul_le_mul_of_nonneg_left ht (show 0 ≤ n by linarith)
  calc
    _ ≤ n+t/saddleTime m n := by linarith
    _ ≤ n*t+t/saddleTime m n := by linarith
    _ = _ := by ring

theorem exists_normalized_left_segment_bound (m : ℕ) (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → r ≤ 1/2 →
      ∀ (t u : ℝ), 1 ≤ t → ((2*m : ℕ) : ℝ)+r ≤ u →
      IsMaxOn (weighted m 0 t 0) (Ici 0) u →
      (∫ v : ℝ in (((2*m : ℕ) : ℝ))..(u-r), weighted m 0 t 0 v)/(RiemannEvenFlow.flow m t 0).re ≤
        C*t^2*Real.exp (-t*r^2) := by
  obtain ⟨K,hK,hpeak⟩ := exists_peak_normalization_bound m hm
  obtain ⟨L,hL,hcenter⟩ := exists_center_linear_bound m hm
  refine ⟨L*K,mul_pos hL hK,?_⟩
  intro r hr hrhalf t u ht hu hmax
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hn : (2 : ℝ) ≤ ((2*m : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ 2*m by omega)
  have huN : ((2*m : ℕ) : ℝ) ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have hur : ((2*m : ℕ) : ℝ) ≤ u-r := by linarith
  have hs := max_real_stationary m t u hu0 hmax
  have hgauss := actual_left_gaussian_envelope m hm t u (u-r) hur (by linarith)
    (by linarith) hs
  have heq : ((u-r)-u)^2 = r^2 := by ring
  rw [heq] at hgauss
  have hp : 1 ≤ (u-r)^(2*m-1) := one_le_pow₀ (by linarith : 1 ≤ u-r)
  have hnp := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (2*m) : (0 : ℝ) ≤ ((2*m : ℕ) : ℝ))
  have hnt := mul_le_mul_of_nonneg_right (hn.trans (by simpa using hnp)) ht0.le
  have hc : t ≤ (1/2 : ℝ)*((2*m : ℕ) : ℝ)*t*(u-r)^(2*m-1) := by nlinarith
  have hexp : Real.exp (-((1/2 : ℝ)*((2*m : ℕ) : ℝ)*t*(u-r)^(2*m-1))*r^2) ≤ Real.exp (-t*r^2) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hc (sq_nonneg r)
    linarith
  have hpoint (v : ℝ) (hv : v ∈ Icc (((2*m : ℕ) : ℝ)) (u-r)) :
      weighted m 0 t 0 v ≤ weighted m 0 t 0 u*Real.exp (-t*r^2) := by
    have hmono := (weighted_strictMonoOn_left_of_stationary m hm t u huN hs).monotoneOn
    have hstep := hmono (show v ∈ Icc (((2*m : ℕ) : ℝ)) u from ⟨hv.1,by linarith [hv.2]⟩)
      (show u-r ∈ Icc (((2*m : ℕ) : ℝ)) u from ⟨hur,by linarith⟩) hv.2
    exact hstep.trans (hgauss.trans (mul_le_mul_of_nonneg_left hexp (weighted_pos m t u hu0.le).le))
  let D := weighted m 0 t 0 u*Real.exp (-t*r^2)
  have hcont : Continuous (weighted m 0 t 0) := continuous_iff_continuousAt.mpr
    (fun v => (weighted_hasDerivAt m t v).continuousAt)
  have hi := hcont.intervalIntegrable (μ := volume) (((2*m : ℕ) : ℝ)) (u-r)
  have hconst := (continuous_const : Continuous (fun _ : ℝ => D)).intervalIntegrable
    (μ := volume) (((2*m : ℕ) : ℝ)) (u-r)
  have hmass := intervalIntegral.integral_mono_on hur hi hconst hpoint
  rw [intervalIntegral.integral_const] at hmass
  simp only [smul_eq_mul] at hmass
  have hD : 0 ≤ D := by dsimp [D]; exact mul_nonneg (weighted_pos m t u hu0.le).le (Real.exp_pos _).le
  have hshort : (u-r-((2*m : ℕ) : ℝ))*D ≤ u*D := by nlinarith
  have htime := hcenter t u ht huN hs
  have hpeak' := hpeak t u ht0.le huN hmax
  have hM := actual_flow_zero_pos m t
  apply (div_le_iff₀ hM).mpr
  calc
    _ ≤ u*D := hmass.trans hshort
    _ ≤ (L*t)*D := mul_le_mul_of_nonneg_right htime hD
    _ ≤ (L*t)*((K*t*(RiemannEvenFlow.flow m t 0).re)*Real.exp (-t*r^2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right hpeak' (Real.exp_pos _).le
    _ = _ := by ring

theorem normalized_left_tail_eventually_small (m : ℕ) (hm : 0 < m) (r ε : ℝ)
    (hr : 0 < r) (hrhalf : r ≤ 1/2) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ u ∈ Ici (0 : ℝ),
      IsMaxOn (weighted m 0 t 0) (Ici 0) u →
        (∫ v : ℝ in 0..(u-r), weighted m 0 t 0 v)/(RiemannEvenFlow.flow m t 0).re < ε := by
  obtain ⟨C,hC,hbound⟩ := exists_normalized_left_segment_bound m hm
  have hlim : Tendsto (fun t : ℝ => C*t^2*Real.exp (-t*r^2)) atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 : ℝ) (r^2) (sq_pos_of_pos hr)).const_mul C
    simpa only [Real.rpow_two,mul_zero,mul_assoc,mul_comm,mul_left_comm,neg_mul,mul_neg] using h
  have heps : 0 < ε/2 := half_pos hε
  filter_upwards [(normalized_compact_mass_tendsto_zero m hm (((2*m : ℕ) : ℝ)) (Nat.cast_nonneg _)).eventually
      (gt_mem_nhds heps),hlim.eventually (gt_mem_nhds heps),
    maxima_escape m hm (((2*m : ℕ) : ℝ)+r) (by positivity),
    eventually_ge_atTop (1 : ℝ)] with t hcompact hsmall he ht
  intro u hu hmax
  have huN := (he u hu hmax).le
  have hseg := hbound r hr hrhalf t u ht huN hmax
  have hcont : Continuous (weighted m 0 t 0) := continuous_iff_continuousAt.mpr
    (fun v => (weighted_hasDerivAt m t v).continuousAt)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) 0 (((2*m : ℕ) : ℝ)))
    (hcont.intervalIntegrable (μ := volume) (((2*m : ℕ) : ℝ)) (u-r))
  rw [← hsplit,add_div]
  linarith

theorem normalized_two_sided_tails_eventually_small (m : ℕ) (hm : 0 < m) (r ε : ℝ)
    (hr : 0 < r) (hrhalf : r ≤ 1/2) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ u ∈ Ici (0 : ℝ),
      IsMaxOn (weighted m 0 t 0) (Ici 0) u →
        ((∫ v : ℝ in 0..(u-r), weighted m 0 t 0 v)+
          (∫ s : ℝ in Ioi r, weighted m 0 t 0 (u+s)))/(RiemannEvenFlow.flow m t 0).re < ε := by
  filter_upwards [normalized_left_tail_eventually_small m hm r (ε/2) hr hrhalf (half_pos hε),
    normalized_right_tail_eventually_small m hm r (ε/2) hr (half_pos hε)] with t hleft hright
  intro u hu hmax
  have hl := hleft u hu hmax
  have hr' := hright u hu hmax
  rw [add_div]
  linarith

end OperatorDerivativeRewrite.Foundation.RiemannEvenNormalizedCompact
