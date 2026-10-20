import Foundation.RiemannEvenMomentDecomposition
import Foundation.RiemannEvenSaddleGrowth

/-! Decay of the actual centered exponential moment at frequency equal to
the escaping saddle center. This is an actual growing-frequency estimate. -/
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannEvenGrowingMoment
open RiemannEvenDomain RiemannEvenRealSaddle RiemannEvenWeightedTails
open RiemannEvenMomentDecomposition RiemannEvenSaddleGrowth

theorem exponential_tail_absorption (c Q Δ t u : ℝ) (hc : 0 < c) (hQ : 0 ≤ Q)
    (hu : 0 ≤ u) (ht : 1 ≤ t) (hlo : c*Real.exp (3*u) ≤ t)
    (hhi : t ≤ Q*Real.exp (4*u)) (hΔ : Real.exp (-u) ≤ Δ)
    (hdom : u^2+12*u ≤ (c/2)*Real.exp (2*u)) :
    u*Real.exp (u^2)*(t*Real.exp (-t*Δ)+t^2*Real.exp (-t*Real.exp (-u))) ≤
      (Q+Q^2)*u*Real.exp (-4*u) ∧
    Real.exp (u^2/(2*t)-(t/2)*Real.exp (-u)) ≤ Real.exp (-4*u) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have helo : c*Real.exp (2*u) ≤ t*Real.exp (-u) := by
    have h := mul_le_mul_of_nonneg_right hlo (Real.exp_pos (-u)).le
    convert h using 1
    rw [mul_assoc,← Real.exp_add]
    congr 2
    ring
  have hsquare : t^2 ≤ Q^2*Real.exp (8*u) := by
    have h := pow_le_pow_left₀ ht0.le hhi 2
    have he : (Real.exp (4*u))^2 = Real.exp (8*u) := by
      rw [pow_two,← Real.exp_add]
      congr 1
      ring
    simpa only [mul_pow,he] using h
  have hfirst : t*Real.exp (-t*Δ) ≤ Q*Real.exp (8*u)*Real.exp (-t*Real.exp (-u)) := by
    have htime : t ≤ Q*Real.exp (8*u) := hhi.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith : 4*u ≤ 8*u)) hQ)
    have he : Real.exp (-t*Δ) ≤ Real.exp (-t*Real.exp (-u)) :=
      Real.exp_le_exp.mpr (by have h := mul_le_mul_of_nonneg_left hΔ ht0.le; linarith)
    exact mul_le_mul htime he (Real.exp_pos _).le (by positivity)
  have hsecond := mul_le_mul_of_nonneg_right hsquare (Real.exp_pos (-t*Real.exp (-u))).le
  have habsorb : Real.exp (u^2+8*u-t*Real.exp (-u)) ≤ Real.exp (-4*u) :=
    Real.exp_le_exp.mpr (by linarith [sq_nonneg u])
  have hright : u^2/(2*t) ≤ u^2/2 :=
    div_le_div_of_nonneg_left (sq_nonneg u) (by norm_num) (by linarith)
  refine ⟨?_,Real.exp_le_exp.mpr (by nlinarith [sq_nonneg u])⟩
  calc
    _ ≤ u*Real.exp (u^2)*((Q*Real.exp (8*u)*Real.exp (-t*Real.exp (-u)))+
        (Q^2*Real.exp (8*u)*Real.exp (-t*Real.exp (-u)))) :=
      mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (by positivity)
    _ = (Q+Q^2)*u*Real.exp (u^2+8*u-t*Real.exp (-u)) := by
      rw [show u^2+8*u-t*Real.exp (-u) = (u^2+8*u)+(-t*Real.exp (-u)) by ring,
        Real.exp_add,Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left habsorb (by positivity)

theorem centered_growing_moment_eventually_small (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ u : ℝ in atTop, ∀ t : ℝ, 1 ≤ t →
      IsMaxOn (weighted m 0 t 0) (Ici 0) u →
      u*((∫ v : ℝ in Ici 0, |v-u| * Real.exp (u*|v-u|) * weighted m 0 t 0 v)/
        (RiemannEvenFlow.flow m t 0).re) < ε := by
  let n : ℝ := ((2*m : ℕ) : ℝ)
  let Δ : ℝ := (n+1)^(2*m)-n^(2*m)
  let Q : ℝ := 4*Real.pi
  have hΔ : 0 < Δ := RiemannEvenCompactMass.compact_exponent_gap_pos m hm n (Nat.cast_nonneg _)
  obtain ⟨c,hc,hlo⟩ := exists_stationary_time_exponential_lower m hm
  obtain ⟨C,K,hC,hK,hfull⟩ := exists_actual_full_moment_bound m hm
  have hr0 : Tendsto (fun u : ℝ => Real.exp (-u/2)) atTop (nhds 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0 : ℝ) (1/2 : ℝ) (by norm_num)
    simp only [Real.rpow_zero,one_mul] at h
    convert h using 1 <;> ext u <;> congr 1 <;> ring
  have hlocal : Tendsto (fun u : ℝ => u*Real.exp (-u/2)) atTop (nhds 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) (1/2 : ℝ) (by norm_num)
    simp only [Real.rpow_one] at h
    convert h using 1 <;> ext u <;> congr 2 <;> ring
  have hdelta : ∀ᶠ u : ℝ in atTop, Real.exp (-u) ≤ Δ :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds hΔ)).mono (fun _ h => h.le)
  have hpoly2 : Tendsto (fun u : ℝ => u^2*Real.exp (-4*u)) atTop (nhds 0) := by
    simpa only [Real.rpow_two] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 : ℝ) 4 (by norm_num)
  have hpoly1 : Tendsto (fun u : ℝ => u*Real.exp (-4*u)) atTop (nhds 0) := by
    simpa only [Real.rpow_one] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) 4 (by norm_num)
  have hlimit : Tendsto (fun u : ℝ => C*(Q+Q^2)*(u^2*Real.exp (-4*u))+
      Real.exp 1*(u*Real.exp (-u/2))+K*(u*Real.exp (-4*u))) atTop (nhds 0) := by
    simpa only [mul_zero,add_zero] using
      ((hpoly2.const_mul (C*(Q+Q^2))).add (hlocal.const_mul (Real.exp 1))).add (hpoly1.const_mul K)
  filter_upwards [eventually_ge_atTop (n+1),hr0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2)),
    hlocal.eventually (gt_mem_nhds zero_lt_one),hdelta,
    quadratic_linear_eventually_le_exp (c/2) 12 0 (by positivity),
    hlimit.eventually (gt_mem_nhds hε)] with u huN hrhalf hsmall hd hdom hfinal
  intro t ht hmax
  have hn : (2 : ℝ) ≤ n := by dsimp [n]; exact_mod_cast (show 2 ≤ 2*m by omega)
  have hu0 : 0 ≤ u := by linarith
  have huN' : ((2*m : ℕ) : ℝ) ≤ u := by change n ≤ u; linarith
  have hs := max_real_stationary m t u (by linarith) hmax
  let r : ℝ := Real.exp (-u/2)
  have hr : 0 < r := Real.exp_pos _
  have hur : ((2*m : ℕ) : ℝ)+r ≤ u := by change n+r ≤ u; dsimp [r]; linarith
  have hb := hfull u r t u hu0 hr hrhalf.le ht hur hmax
  have hrsq : r^2 = Real.exp (-u) := by
    dsimp [r]
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  rw [hrsq] at hb
  rw [show u*u = u^2 by ring] at hb
  have hab := exponential_tail_absorption c Q Δ t u hc (by dsimp [Q]; positivity) hu0 ht
    (hlo t u huN' hs) (stationary_time_upper m hm t u huN' hs) hd (by simpa using hdom)
  have he : r*Real.exp (u*r) ≤ r*Real.exp 1 :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsmall.le) hr.le
  have hleft := mul_le_mul_of_nonneg_left hab.1 hC.le
  have hright := mul_le_mul_of_nonneg_left hab.2 hK.le
  have hsum : (∫ v : ℝ in Ici 0, |v-u| * Real.exp (u*|v-u|) * weighted m 0 t 0 v)/
      (RiemannEvenFlow.flow m t 0).re ≤ C*(Q+Q^2)*u*Real.exp (-4*u)+
        r*Real.exp 1+K*Real.exp (-4*u) := by
    change _ ≤ _ at hb
    dsimp only [Δ,n] at hleft
    nlinarith [hb]
  have hmul := mul_le_mul_of_nonneg_left hsum hu0
  apply lt_of_le_of_lt _ hfinal
  convert hmul using 1 <;> dsimp only [r] <;> ring

theorem normalized_growing_moment_eventually_small (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ u ∈ Ici (0 : ℝ),
      IsMaxOn (weighted m 0 t 0) (Ici 0) u →
      u*((∫ v : ℝ in Ici 0, |v-u| * Real.exp (u*|v-u|) * weighted m 0 t 0 v)/
        (RiemannEvenFlow.flow m t 0).re) < ε := by
  obtain ⟨U,hU⟩ := eventually_atTop.1 (centered_growing_moment_eventually_small m hm ε hε)
  filter_upwards [maxima_escape m hm (max U 0) (le_max_right _ _),eventually_ge_atTop (1 : ℝ)]
    with t he ht
  intro u hu hmax
  exact hU u ((le_max_left U 0).trans (he u hu hmax).le) t ht hmax

end OperatorDerivativeRewrite.Foundation.RiemannEvenGrowingMoment
