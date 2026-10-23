import Mathlib.Algebra.BigOperators.Module
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Deterministic positive quadrature controlled by cumulative-mass errors.
This is the continuous-weight step required by the actual IBM quartic calculus. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace OperatorDerivativeRewrite.Foundation.IBMContinuousQuadrature

def time (T : ℝ) (N i : ℕ) : ℝ := T / N * i

theorem time_step (T : ℝ) (N i : ℕ) :
    time T N (i + 1) - time T N i = T/N := by
  simp only [time, Nat.cast_add, Nat.cast_one]
  ring

theorem time_mem {T : ℝ} (hT : 0 ≤ T) {N i : ℕ} (hN : 0 < N) (hi : i ≤ N) :
    time T N i ∈ Icc 0 T := by
  have hp : 0 < (N : ℝ) := by exact_mod_cast hN
  constructor
  · unfold time; positivity
  · calc
      time T N i ≤ T/N*N := by unfold time; gcongr
      _ = T := div_mul_cancel₀ _ hp.ne'

/-- Abel's identity controls arbitrary finite weights by their discrete
variation and the supremum of partial errors. -/
theorem weighted_prefix_bound (f e : ℕ → ℝ) (N : ℕ) (hN : 0 < N) (M B V : ℝ)
    (hM : 0 ≤ M) (hB : ∀ i < N, |f i| ≤ B)
    (he : ∀ m ≤ N, |∑ i ∈ Finset.range m, e i| ≤ M)
    (hv : (∑ i ∈ Finset.range (N - 1), |f (i + 1) - f i|) ≤ V) :
    |∑ i ∈ Finset.range N, f i * e i| ≤ M * (B+V) := by
  have hid := Finset.sum_range_by_parts f e N
  simp only [smul_eq_mul] at hid
  rw [hid]
  have hfirst : |f (N - 1) * ∑ i ∈ Finset.range N, e i| ≤ B*M := by
    rw [abs_mul]
    exact mul_le_mul (hB _ (by omega)) (he N le_rfl)
      (abs_nonneg _) ((abs_nonneg _).trans (hB _ (by omega)))
  have hrest : |∑ i ∈ Finset.range (N - 1),
      (f (i + 1) - f i) * ∑ j ∈ Finset.range (i + 1), e j| ≤ V*M := by
    calc
      _ ≤ ∑ i ∈ Finset.range (N - 1),
          |(f (i + 1) - f i) * ∑ j ∈ Finset.range (i + 1), e j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (N - 1), |f (i + 1) - f i| * M := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (he _ (by have := Finset.mem_range.mp hi; omega))
          (abs_nonneg _)
      _ ≤ V*M := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hv hM
  have h := abs_sub_le (f (N - 1) * ∑ i ∈ Finset.range N, e i) 0
    (∑ i ∈ Finset.range (N - 1), (f (i + 1) - f i) * ∑ j ∈ Finset.range (i + 1), e j)
  simp only [sub_zero, zero_sub, abs_neg] at h
  nlinarith

theorem variation_bound {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    (g : ℝ → ℝ) (N : ℕ) (hN : 0 < N)
    (hLip : ∀ x ∈ Icc 0 T, ∀ y ∈ Icc 0 T, |g y - g x| ≤ K * |y - x|) :
    (∑ i ∈ Finset.range (N - 1), |g (time T N (i + 1))-g (time T N i)|) ≤ K*T := by
  have hp : 0 < (N : ℝ) := by exact_mod_cast hN
  have hb (i : ℕ) (hi : i ∈ Finset.range (N - 1)) :
      |g (time T N (i + 1))-g (time T N i)| ≤ K*(T / N) := by
    have hiN : i + 1 ≤ N := by have := Finset.mem_range.mp hi; omega
    have h := hLip _ (time_mem hT hN (by omega : i ≤ N)) _ (time_mem hT hN hiN)
    rwa [time_step, abs_of_nonneg (div_nonneg hT hp.le)] at h
  calc
    _ ≤ ∑ i ∈ Finset.range (N - 1), K*(T / N) := Finset.sum_le_sum hb
    _ = (N - 1 : ℕ) * (K*(T / N)) := by simp
    _ ≤ (N : ℝ) * (K*(T / N)) := by gcongr; exact_mod_cast Nat.sub_le N 1
    _ = K*T := by field_simp

/-- Quantitative left Riemann-sum error on the actual uniform time grid. -/
theorem riemann_error_bound {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    (g : ℝ → ℝ) (hg : Continuous g) (N : ℕ) (hN : 0 < N)
    (hLip : ∀ x ∈ Icc 0 T, ∀ y ∈ Icc 0 T, |g y - g x| ≤ K * |y - x|) :
    |(T / N) * ∑ i ∈ Finset.range N, g (time T N i) - ∫ x in (0 : ℝ)..T, g x| ≤
      K*T^2/N := by
  have hp : 0 < (N : ℝ) := by exact_mod_cast hN
  have hh : 0 ≤ T/N := div_nonneg hT hp.le
  have hb (i : ℕ) (hi : i < N) :
      |(T / N)*g (time T N i) - ∫ x in time T N i..time T N (i + 1), g x| ≤
      (K*(T / N))*(T / N) := by
    have hstep : time T N i ≤ time T N (i + 1) := by linarith [time_step T N i]
    have hid : (T / N)*g (time T N i) -
        ∫ x in time T N i..time T N (i + 1), g x =
        ∫ x in time T N i..time T N (i + 1), (g (time T N i)-g x) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const
        (hg.intervalIntegrable _ _), intervalIntegral.integral_const, time_step]
      simp only [smul_eq_mul]
    rw [hid]
    have hfun (x : ℝ) (hx : x ∈ uIoc (time T N i) (time T N (i + 1))) :
        ‖g (time T N i)-g x‖ ≤ K*(T / N) := by
      rw [uIoc_of_le hstep] at hx
      have hxT : x ∈ Icc 0 T :=
        ⟨(time_mem hT hN (by omega : i ≤ N)).1.trans hx.1.le,
          hx.2.trans (time_mem hT hN (by omega : i + 1 ≤ N)).2⟩
      have hd : |x-time T N i| ≤ T/N := by
        rw [abs_of_nonneg (sub_nonneg.mpr hx.1.le)]
        linarith [time_step T N i, hx.2]
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact (hLip _ (time_mem hT hN (by omega : i ≤ N)) _ hxT).trans
        (mul_le_mul_of_nonneg_left hd hK)
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const hfun
    rw [time_step, abs_of_nonneg hh] at hn
    simpa only [Real.norm_eq_abs] using hn
  have ht := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i => time T N i) (f := g) (μ := volume) (n := N)
    (fun i hi => hg.intervalIntegrable _ _)
  have hz : time T N 0 = 0 := by simp [time]
  have hend : time T N N = T := by unfold time; exact div_mul_cancel₀ _ hp.ne'
  rw [hz, hend] at ht
  calc
    _ = |∑ i ∈ Finset.range N, ((T / N)*g (time T N i) -
        ∫ x in time T N i..time T N (i + 1), g x)| := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ht]
    _ ≤ ∑ i ∈ Finset.range N, |(T / N)*g (time T N i) -
        ∫ x in time T N i..time T N (i + 1), g x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range N, (K*(T / N))*(T / N) :=
      Finset.sum_le_sum fun i hi => hb i (Finset.mem_range.mp hi)
    _ = _ := by simp; field_simp

theorem lipschitz_quadrature_bound {T c K B M : ℝ} (hT : 0 ≤ T)
    (hc : 0 ≤ c) (hK : 0 ≤ K) (hM : 0 ≤ M) (g : ℝ → ℝ) (hg : Continuous g)
    (N : ℕ) (hN : 0 < N) (q : ℕ → ℝ)
    (he : ∀ m ≤ N, |(∑ i ∈ Finset.range m, q i) - c * (T / N) * m| ≤ M)
    (hB : ∀ t ∈ Icc 0 T, |g t| ≤ B)
    (hLip : ∀ x ∈ Icc 0 T, ∀ y ∈ Icc 0 T, |g y - g x| ≤ K * |y - x|) :
    |(∑ i ∈ Finset.range N, g (time T N i)*q i) - c * ∫ x in (0 : ℝ)..T, g x| ≤
      M*(B+K*T) + c*(K*T^2/N) := by
  have herr := weighted_prefix_bound (fun i => g (time T N i))
    (fun i => q i-c*(T / N)) N hN M B (K*T) hM
    (fun i hi => hB _ (time_mem hT hN (by omega))) (fun m hm => by
      simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_comm (m : ℝ)] using he m hm)
    (variation_bound hT hK g N hN hLip)
  have hr := riemann_error_bound hT hK g hg N hN hLip
  have hid : ((∑ i ∈ Finset.range N, g (time T N i)*q i) -
      c * ∫ x in (0 : ℝ)..T, g x) =
      (∑ i ∈ Finset.range N, g (time T N i)*(q i-c*(T / N))) +
      c*((T / N)*∑ i ∈ Finset.range N, g (time T N i) - ∫ x in (0 : ℝ)..T, g x) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  rw [hid]
  have ht := abs_add_le (∑ i ∈ Finset.range N, g (time T N i)*(q i-c*(T / N)))
    (c*((T / N)*∑ i ∈ Finset.range N, g (time T N i) - ∫ x in (0 : ℝ)..T, g x))
  rw [abs_mul, abs_of_nonneg hc] at ht
  exact ht.trans (add_le_add herr (mul_le_mul_of_nonneg_left hr hc))

theorem polynomial_bounds {T : ℝ} (hT : 0 ≤ T) (p : Polynomial ℝ) :
    ∃ B K : ℝ, 0 ≤ K ∧ (∀ x ∈ Icc 0 T, |p.eval x| ≤ B) ∧
      (∀ x ∈ Icc 0 T, ∀ y ∈ Icc 0 T, |p.eval y - p.eval x| ≤ K * |y - x|) := by
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).exists_bound_of_continuousOn
    p.continuous.continuousOn
  obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).exists_bound_of_continuousOn
    p.derivative.continuous.continuousOn
  refine ⟨B, K, (norm_nonneg _).trans (hK 0 ⟨le_rfl,hT⟩), ?_, ?_⟩
  · intro x hx
    simpa only [Real.norm_eq_abs] using hB x hx
  · intro x hx y hy
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := fun x => p.eval x) (fun x _ => p.differentiableAt)
      (fun x hx => by rw [p.deriv]; exact hK x hx) (convex_Icc 0 T) hx hy
    simpa only [Real.norm_eq_abs] using h

/-- Positivity bounds the effect of uniform approximation of a test weight
by its error times the total mass, with no variation assumption on the weight. -/
theorem approximation_bound {T c δ : ℝ} (hT : 0 ≤ T) (hc : 0 ≤ c)
    (g p : ℝ → ℝ) (hg : Continuous g) (hp : Continuous p)
    (N : ℕ) (hN : 0 < N) (q : ℕ → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hnear : ∀ x ∈ Icc 0 T, |p x - g x| ≤ δ) :
    |(∑ i ∈ Finset.range N, g (time T N i)*q i) - c * ∫ x in (0 : ℝ)..T, g x| ≤
      |(∑ i ∈ Finset.range N, p (time T N i)*q i) - c * ∫ x in (0 : ℝ)..T, p x| +
      δ*((∑ i ∈ Finset.range N, q i)+c*T) := by
  have hsum : |∑ i ∈ Finset.range N, (g (time T N i)-p (time T N i))*q i| ≤
      δ*∑ i ∈ Finset.range N, q i := by
    calc
      _ ≤ ∑ i ∈ Finset.range N, |(g (time T N i)-p (time T N i))*q i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range N, δ*q i := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul, abs_of_nonneg (hq i), abs_sub_comm]
        exact mul_le_mul_of_nonneg_right
          (hnear _ (time_mem hT hN (by have := Finset.mem_range.mp hi; omega))) (hq i)
      _ = _ := by rw [Finset.mul_sum]
  have hint : |(∫ x in (0 : ℝ)..T, p x) - ∫ x in (0 : ℝ)..T, g x| ≤ δ*T := by
    rw [← intervalIntegral.integral_sub (hp.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
    have hb (x : ℝ) (hx : x ∈ uIoc (0 : ℝ) T) : ‖p x - g x‖ ≤ δ := by
      rw [uIoc_of_le hT] at hx
      simpa only [Real.norm_eq_abs] using hnear x ⟨hx.1.le,hx.2⟩
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hT] using h
  have hid : ((∑ i ∈ Finset.range N, g (time T N i)*q i) -
      c * ∫ x in (0 : ℝ)..T, g x) =
      ((∑ i ∈ Finset.range N, p (time T N i)*q i) - c * ∫ x in (0 : ℝ)..T, p x) +
      (∑ i ∈ Finset.range N, (g (time T N i)-p (time T N i))*q i) +
      c*((∫ x in (0 : ℝ)..T, p x) - ∫ x in (0 : ℝ)..T, g x) := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hid]
  have h1 := abs_add_le
    (((∑ i ∈ Finset.range N, p (time T N i)*q i) - c * ∫ x in (0 : ℝ)..T, p x) +
      ∑ i ∈ Finset.range N, (g (time T N i)-p (time T N i))*q i)
    (c*((∫ x in (0 : ℝ)..T, p x) - ∫ x in (0 : ℝ)..T, g x))
  have h2 := abs_add_le
    ((∑ i ∈ Finset.range N, p (time T N i)*q i) - c * ∫ x in (0 : ℝ)..T, p x)
    (∑ i ∈ Finset.range N, (g (time T N i)-p (time T N i))*q i)
  rw [abs_mul, abs_of_nonneg hc] at h1
  have h3 := mul_le_mul_of_nonneg_left hint hc
  nlinarith

/-- Positive quadratures converge against every continuous real weight once
all cumulative mass errors vanish uniformly. Arbitrary refining grid sizes
permit later application on almost-sure stochastic subsequences. -/
theorem continuous_quadrature_tendsto {T c : ℝ} (hT : 0 ≤ T) (hc : 0 ≤ c)
    (g : ℝ → ℝ) (hg : Continuous g) (N : ℕ → ℕ) (hN : ∀ n, 0 < N n)
    (hNlim : Tendsto N atTop atTop) (q : ℕ → ℕ → ℝ) (hq : ∀ n i, 0 ≤ q n i)
    (M : ℕ → ℝ) (hM : ∀ n, 0 ≤ M n) (hMlim : Tendsto M atTop (𝓝 0))
    (he : ∀ n m, m ≤ N n →
      |(∑ i ∈ Finset.range m, q n i) - c * (T / N n) * m| ≤ M n) :
    Tendsto (fun n => ∑ i ∈ Finset.range (N n), g (time T (N n) i)*q n i)
      atTop (𝓝 (c * ∫ x in (0 : ℝ)..T, g x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hC : 0 < 2*c*T+1 := by positivity
  let δ := ε/(4*(2*c*T+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨p, hnear⟩ := exists_polynomial_near_of_continuousOn 0 T g hg.continuousOn δ hδ
  obtain ⟨B, K, hK, hB, hLip⟩ := polynomial_bounds hT p
  have hdiv : Tendsto (fun n => K*T^2/(N n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hNlim)
  have hpoly : Tendsto (fun n => M n*(B+K*T)+c*(K*T^2/(N n : ℝ))) atTop (𝓝 0) := by
    simpa only [zero_mul, mul_zero, add_zero] using
      (hMlim.mul_const (B+K*T)).add (hdiv.const_mul c)
  have heps : 0 < ε/2 := by positivity
  filter_upwards [hMlim.eventually (gt_mem_nhds zero_lt_one),
    hpoly.eventually (gt_mem_nhds heps)] with n hM1 hpε
  rw [Real.dist_eq]
  have hpN : (N n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hN n))
  have hcancel : c*(T/(N n : ℝ))*N n = c*T := by field_simp
  have hfull := he n (N n) le_rfl
  rw [hcancel] at hfull
  have hmass : (∑ i ∈ Finset.range (N n), q n i) ≤ c*T+1 := by
    linarith [le_abs_self ((∑ i ∈ Finset.range (N n), q n i)-c*T)]
  have ha := approximation_bound hT hc g (fun x => p.eval x) hg p.continuous
    (N n) (hN n) (q n) (hq n) (fun x hx => (hnear x hx).le)
  have hb := lipschitz_quadrature_bound hT hc hK (hM n) (fun x => p.eval x)
    p.continuous (N n) (hN n) (q n) (he n) hB hLip
  have hδid : δ*(2*c*T+1) = ε/4 := by dsimp [δ]; field_simp
  have hsmall : δ*((∑ i ∈ Finset.range (N n), q n i)+c*T) ≤ ε/4 := by
    rw [← hδid]
    exact mul_le_mul_of_nonneg_left (by linarith) hδ.le
  linarith

end OperatorDerivativeRewrite.Foundation.IBMContinuousQuadrature
