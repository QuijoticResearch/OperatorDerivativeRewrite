import Foundation.IBMClockNoiseSpectral
import Mathlib.Analysis.Normed.Group.Tannery
/-! Critical clock-sector obstruction for the actual reflected-clock IBM endpoint.
The original number projections have divergent sqrt(n)-weighted energy, and
nonzero even sectors occur beyond every cutoff. This is not a positive
subcritical summability theorem or a fractional-operator domain equivalence.
The auxiliary Bernoulli bounds prepare that still-open positive direction. -/
noncomputable section
open Filter Set MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockNoiseThreshold
open IBMClockNoiseRegularity

theorem power_defect_bounds (n : ℕ) (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    0 ≤ 1-(1-h)^n ∧ 1-(1-h)^n ≤ min 1 ((n:ℝ)*h) := by
  have hp : 0 ≤ (1-h)^n := pow_nonneg (by linarith) _
  have hq : (1-h)^n ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hb := one_add_mul_le_pow (a := -h) (by linarith : -2 ≤ -h) n
  have he : 1 + (n:ℝ)*(-h) ≤ (1-h)^n := by simpa only [sub_eq_add_neg] using hb
  constructor
  · linarith
  · exact le_min (by linarith) (by nlinarith)

theorem power_defect_sqrt_bound (n : ℕ) (h : ℝ) (h0 : 0 < h) (h1 : h ≤ 1) :
    (1-(1-h)^n)/Real.sqrt h ≤ Real.sqrt (n:ℝ) := by
  obtain ⟨hz,hz'⟩ := power_defect_bounds n h h0.le h1
  have hz1 := hz'.trans (min_le_left _ _)
  have hzn := hz'.trans (min_le_right _ _)
  have hs : (1-(1-h)^n)^2 ≤ (n:ℝ)*h := by nlinarith
  have hr : (Real.sqrt (n:ℝ)*Real.sqrt h)^2 = (n:ℝ)*h := by
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg n),Real.sq_sqrt h0.le]
  have ht : 1-(1-h)^n ≤ Real.sqrt (n:ℝ)*Real.sqrt h := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg (n:ℝ)) (Real.sqrt_nonneg h)]
  exact (div_le_iff₀ (Real.sqrt_pos.2 h0)).2 ht

theorem rate_normalized (h : ℝ) (h0 : 0 < h) (h1 : h ≤ 1) :
    rate h / Real.sqrt h = Real.sqrt 2 - 2*Real.sqrt h/(2+Real.sqrt (4-2*h)) := by
  have hs := Real.sq_sqrt (show 0 ≤ 4-2*h by linarith)
  have hh := Real.sq_sqrt h0.le
  have hd : 2+Real.sqrt (4-2*h) ≠ 0 := by positivity
  have hn : Real.sqrt h ≠ 0 := ne_of_gt (Real.sqrt_pos.2 h0)
  unfold rate
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  field_simp
  nlinarith

theorem rate_normalized_tendsto :
    Tendsto (fun h : ℝ => rate h / Real.sqrt h) (nhdsWithin 0 (Ioi 0))
      (𝓝 (Real.sqrt 2)) := by
  have hi : Tendsto (fun h : ℝ => h) (nhdsWithin 0 (Ioi 0)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hs := Real.continuous_sqrt.tendsto 0 |>.comp hi
  have ht : Tendsto (fun h : ℝ => Real.sqrt (4-2*h)) (nhdsWithin 0 (Ioi 0))
      (𝓝 2) := by
    have hj : Tendsto (fun h : ℝ => 4-2*h) (nhdsWithin 0 (Ioi 0)) (𝓝 (4:ℝ)) := by
      convert (tendsto_const_nhds.sub (hi.const_mul 2)) using 1 <;> norm_num
    have hv : Real.sqrt (4:ℝ) = 2 := by norm_num
    simpa only [Function.comp_def,hv] using (Real.continuous_sqrt.tendsto 4).comp hj
  have hl := (tendsto_const_nhds (x := Real.sqrt 2)).sub
    ((hs.const_mul 2).div (ht.const_add 2) (by norm_num : (2:ℝ)+2 ≠ 0))
  have he : (fun h : ℝ => rate h / Real.sqrt h) =ᶠ[nhdsWithin 0 (Ioi 0)]
      (fun h => Real.sqrt 2-2*Real.sqrt h/(2+Real.sqrt (4-2*h))) := by
    filter_upwards [self_mem_nhdsWithin, hi.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with h hh hh1
    exact rate_normalized h hh hh1.le
  apply Tendsto.congr' he.symm
  simpa using hl


theorem power_defect_normalized_tendsto (n : ℕ) :
    Tendsto (fun h : ℝ => (1-(1-h)^n)/Real.sqrt h) (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  have hi : Tendsto (fun h : ℝ => h) (nhdsWithin 0 (Ioi 0)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have ht : Tendsto (fun h : ℝ => (n:ℝ)*Real.sqrt h) (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
    simpa using ((Real.continuous_sqrt.tendsto 0).comp hi).const_mul (n:ℝ)
  apply squeeze_zero' _ _ ht
  · filter_upwards [self_mem_nhdsWithin, hi.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with h hh hh1
    exact div_nonneg (power_defect_bounds n h hh.le hh1.le).1 (Real.sqrt_nonneg h)
  · filter_upwards [self_mem_nhdsWithin, hi.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with h hh hh1
    apply (div_le_iff₀ (Real.sqrt_pos.2 hh)).2
    have hb := (power_defect_bounds n h hh.le hh1.le).2.trans (min_le_right _ _)
    simpa only [mul_assoc,Real.mul_self_sqrt hh.le] using hb

theorem summable_sqrt_noise_tendsto (C : ℕ → ℝ) (hC : ∀ n, 0 ≤ C n)
    (hs : Summable (fun (n : ℕ) => Real.sqrt (n:ℝ)*C n)) :
    Tendsto (fun h : ℝ => ∑' (n : ℕ), 2*(1-(1-h)^n)/Real.sqrt h*C n)
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  have hi : Tendsto (fun h : ℝ => h) (nhdsWithin 0 (Ioi 0)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have ht := tendsto_tsum_of_dominated_convergence (𝓕 := nhdsWithin 0 (Ioi 0)) (hs.mul_left 2)
    (g := fun _ : ℕ => (0:ℝ)) (f := fun (h : ℝ) (n : ℕ) => 2*(1-(1-h)^n)/Real.sqrt h*C n) ?_ ?_
  · simpa using ht
  · intro n
    convert ((power_defect_normalized_tendsto n).const_mul 2).mul_const (C n) using 1
    · funext h; ring
    · ring
  · filter_upwards [self_mem_nhdsWithin, hi.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with h hh hh1 n
    have hn := power_defect_sqrt_bound n h hh hh1.le
    have hz := (power_defect_bounds n h hh.le hh1.le).1
    have hc := hC n
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    calc
      _ = 2*((1-(1-h)^n)/Real.sqrt h)*C n := by ring
      _ ≤ 2*Real.sqrt (n:ℝ)*C n := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by norm_num)) (hC n)
      _ = _ := by ring


theorem not_summable_sqrt_of_noise_series (C : ℕ → ℝ) (hC : ∀ n, 0 ≤ C n)
    (K : ℝ) (hK : 0 < K)
    (hseries : ∀ h : ℝ, 0 ≤ h → h ≤ 1 →
      HasSum (fun (n : ℕ) => 2*(1-(1-h)^n)*C n) (K*rate h)) :
    ¬ Summable (fun (n : ℕ) => Real.sqrt (n:ℝ)*C n) := by
  intro hs
  have ht := summable_sqrt_noise_tendsto C hC hs
  have hi : Tendsto (fun h : ℝ => h) (nhdsWithin 0 (Ioi 0)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have he : (fun h : ℝ => ∑' (n : ℕ), 2*(1-(1-h)^n)/Real.sqrt h*C n)
      =ᶠ[nhdsWithin 0 (Ioi 0)] (fun h => K*(rate h/Real.sqrt h)) := by
    filter_upwards [self_mem_nhdsWithin, hi.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with h hh hh1
    have hq := ((hseries h hh.le hh1.le).div_const (Real.sqrt h)).tsum_eq
    calc
      _ = ∑' (n : ℕ), (2*(1-(1-h)^n)*C n)/Real.sqrt h := by
        apply tsum_congr; intro n; ring
      _ = K*rate h/Real.sqrt h := hq
      _ = _ := by ring
  have hz : Tendsto (fun h : ℝ => K*(rate h/Real.sqrt h))
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := ht.congr' he
  have hk := rate_normalized_tendsto.const_mul K
  have hh := tendsto_nhds_unique hz hk
  have hp : 0 < K*Real.sqrt 2 := mul_pos hK (Real.sqrt_pos.2 (by norm_num))
  linarith

open GaussianClockValueOperators IBMClockLinearDivergence

theorem actual_not_summable_sqrt (T : ℝ≥0) (hT : 0 < T) :
    ¬ Summable (fun (n : ℕ) => Real.sqrt (n:ℝ)*
      ‖clockLift (GaussianNumberSectors.projection n) (IBMRandomTimeHilbert.randomSourceL2 T)‖^2) := by
  apply not_summable_sqrt_of_noise_series _ (fun n => sq_nonneg _)
    (‖timeDirection T‖*GaussianAbsoluteMoments.standardMoment 1)
  · exact mul_pos (IBMPointClockDomainObstruction.timeDirection_norm_pos T hT)
      IBMPhysicalL2Obstruction.first_absolute_moment_pos
  · exact IBMClockNoiseSpectral.actual_clock_noise_series T hT



theorem actual_not_summable_bessel (T : ℝ≥0) (hT : 0 < T) (a : ℝ) (ha : 1/2 ≤ a) :
    ¬ Summable (fun (n : ℕ) => ((n:ℝ)+1)^a*
      ‖clockLift (GaussianNumberSectors.projection n) (IBMRandomTimeHilbert.randomSourceL2 T)‖^2) := by
  intro hs
  apply actual_not_summable_sqrt T hT
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ hs
  intro n
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  calc
    Real.sqrt (n:ℝ) ≤ Real.sqrt ((n:ℝ)+1) := Real.sqrt_le_sqrt (by linarith)
    _ = ((n:ℝ)+1)^(1/2:ℝ) := Real.sqrt_eq_rpow _
    _ ≤ ((n:ℝ)+1)^a := Real.rpow_le_rpow_of_exponent_le (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) ha



theorem power_defect_lower (n : ℕ) (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1)
    (hn : (n:ℝ)*h ≤ 1/2) : (n:ℝ)*h/2 ≤ 1-(1-h)^n := by
  revert hn
  induction n with
  | zero => simp
  | succ n ih =>
    intro hn
    have hn' : (n:ℝ)*h ≤ 1/2 := by push_cast at hn; nlinarith
    have hl := ih hn'
    have hb := one_add_mul_le_pow (a := -h) (by linarith : -2 ≤ -h) n
    have he : 1 + (n:ℝ)*(-h) ≤ (1-h)^n := by simpa only [sub_eq_add_neg] using hb
    rw [pow_succ]
    push_cast
    nlinarith



theorem actual_unbounded_even_sectors (T : ℝ≥0) (hT : 0 < T) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ Even n ∧
      clockLift (GaussianNumberSectors.projection n) (IBMRandomTimeHilbert.randomSourceL2 T) ≠ 0 := by
  by_contra hn
  push Not at hn
  apply actual_not_summable_sqrt T hT
  apply summable_of_ne_finset_zero (s := Finset.range (N+1))
  intro n hn'
  have hgt : N < n := by simp only [Finset.mem_range,not_lt] at hn'; omega
  have hz : clockLift (GaussianNumberSectors.projection n)
      (IBMRandomTimeHilbert.randomSourceL2 T) = 0 := by
    rcases Nat.even_or_odd n with he|ho
    · exact hn n hgt he
    · exact IBMClockNoiseSpectral.actual_odd_clock_sector T hT n ho
  simp only [hz,norm_zero,zero_pow (by norm_num : 2 ≠ 0),mul_zero]

end OperatorDerivativeRewrite.Foundation.IBMClockNoiseThreshold
