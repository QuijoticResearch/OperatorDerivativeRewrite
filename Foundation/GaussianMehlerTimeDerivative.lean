/-
Copyright (c) 2026 OperatorDerivativeRewrite contributors.
-/
import Foundation.GaussianMehler
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Positive-time differentiation of the existing Gaussian Mehler kernel. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter Set Real ProbabilityTheory Topology

namespace OperatorDerivativeRewrite.Foundation.GaussianMehlerTimeDerivative

abbrev γ : Measure ℝ := GaussianCore.γ

def a (t : ℝ) : ℝ := Real.exp (-t)
def b (t : ℝ) : ℝ := Real.sqrt (1 - Real.exp (-2 * t))

/-- The Mehler coefficients lie on the unit circle at nonnegative times. -/
theorem a_sq_add_b_sq (t : ℝ) (ht : 0 ≤ t) : a t ^ 2 + b t ^ 2 = 1 := by
  rw [b, Real.sq_sqrt (GaussianMehler.one_sub_exp_nonneg t ht)]
  have he : a t ^ 2 = Real.exp (-2 * t) := by
    rw [a, show -2 * t = -t + -t by ring, Real.exp_add]
    ring
  rw [he]
  ring

/-- At strictly positive time the noise coefficient is strictly positive. -/
theorem b_pos (t : ℝ) (ht : 0 < t) : 0 < b t := by
  unfold b
  apply Real.sqrt_pos.2
  have he : Real.exp (-2 * t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

/-- The deterministic Mehler coefficient has derivative minus itself. -/
theorem hasDerivAt_a (t : ℝ) : HasDerivAt a (-a t) t := by
  have h := (Real.hasDerivAt_exp (-t)).comp t ((hasDerivAt_id t).neg)
  change HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t
  simpa only [Function.comp_def, mul_neg, mul_one] using h

/-- The noise coefficient has its positive-time derivative with the exact normalization. -/
theorem hasDerivAt_b (t : ℝ) (ht : 0 < t) :
    HasDerivAt b (a t ^ 2 / b t) t := by
  have hr : HasDerivAt (fun s : ℝ => 1 - Real.exp (-2 * s))
      (2 * Real.exp (-2 * t)) t := by
    have hi : HasDerivAt (fun s : ℝ => -2 * s) (-2) t := by
      simpa using (hasDerivAt_id t).const_mul (-2)
    have he := ((Real.hasDerivAt_exp (-2 * t)).comp t hi).neg.const_add 1
    convert he using 1
    · funext s; dsimp; ring
    · ring
  have hnonzero : 1 - Real.exp (-2 * t) ≠ 0 := by
    have hp := b_pos t ht
    unfold b at hp
    exact ne_of_gt (Real.sqrt_pos.mp hp)
  have hb := hr.sqrt hnonzero
  have he : Real.exp (-2 * t) = a t ^ 2 := by
    rw [a, show -2 * t = -t + -t by ring, Real.exp_add]
    ring
  convert hb using 1
  · rfl
  · dsimp [b]
    rw [he]
    have hs : Real.sqrt (1 - a t ^ 2) ≠ 0 := by
      rw [← he]
      exact ne_of_gt (b_pos t ht)
    field_simp

/-- The noise coefficient is continuous, including at time zero. -/
theorem b_continuous : Continuous b := by
  unfold b
  fun_prop

/-- A positive-time neighborhood has a strictly positive uniform noise coefficient. -/
theorem b_local_lower_bound (t₀ : ℝ) (ht₀ : 0 < t₀) :
    (b t₀ / 2 : ℝ) > 0 ∧
    {s : ℝ | b t₀ / 2 < b s} ∩ Set.Ioi 0 ∈ 𝓝 t₀ ∧
    ∀ s ∈ {s : ℝ | b t₀ / 2 < b s} ∩ Set.Ioi 0,
      0 < s ∧ b t₀ / 2 ≤ b s := by
  have hb := b_pos t₀ ht₀
  have hc : 0 < b t₀ / 2 := by linarith
  have hnear : {s : ℝ | b t₀ / 2 < b s} ∈ 𝓝 t₀ := by
    apply (isOpen_Ioi.preimage b_continuous).mem_nhds
    change b t₀ / 2 < b t₀
    linarith
  refine ⟨hc, Filter.inter_mem hnear (isOpen_Ioi.mem_nhds ht₀), ?_⟩
  intro s hs
  exact ⟨hs.2, hs.1.le⟩

/-- The deterministic coefficient is between zero and one at nonnegative times. -/
theorem a_bounds (t : ℝ) (ht : 0 ≤ t) : 0 ≤ a t ∧ a t ≤ 1 := by
  constructor
  · exact (Real.exp_pos _).le
  · exact Real.exp_le_one_iff.mpr (by linarith)

/-- On the positive-time neighborhood, the Mehler velocity is linearly bounded
by the Gaussian coordinate. -/
theorem velocity_bound (t₀ : ℝ) (ht₀ : 0 < t₀)
    {s : ℝ} (hs : s ∈ {r : ℝ | b t₀ / 2 < b r} ∩ Set.Ioi 0) (x y : ℝ) :
    |(-a s * x + (a s ^ 2 / b s) * y)| ≤
      |x| + |y| / (b t₀ / 2) := by
  obtain ⟨hc, _, hlocal⟩ := b_local_lower_bound t₀ ht₀
  obtain ⟨hspos, hbs⟩ := hlocal s hs
  obtain ⟨ha0, ha1⟩ := a_bounds s hspos.le
  have hbpos : 0 < b s := lt_of_lt_of_le hc hbs
  have ha_sq : a s ^ 2 ≤ 1 := by nlinarith
  have hquot : a s ^ 2 / b s ≤ 1 / (b t₀ / 2) := by
    calc
      a s ^ 2 / b s ≤ 1 / b s :=
        div_le_div_of_nonneg_right ha_sq hbpos.le
      _ ≤ 1 / (b t₀ / 2) := one_div_le_one_div_of_le hc hbs
  calc
    |(-a s * x + (a s ^ 2 / b s) * y)| ≤
        |(-a s) * x| + |(a s ^ 2 / b s) * y| := abs_add_le _ _
    _ = a s * |x| + (a s ^ 2 / b s) * |y| := by
      rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg ha0]
      rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hbpos.le)]
    _ ≤ |x| + (1 / (b t₀ / 2)) * |y| := by
      exact add_le_add (by nlinarith [abs_nonneg x])
        (mul_le_mul_of_nonneg_right hquot (abs_nonneg y))
    _ = |x| + |y| / (b t₀ / 2) := by ring

/-- Genuine positive-time derivative of the existing Mehler integral, with
integrability of the differentiated kernel supplied by local domination. -/
theorem hasDerivAt_mehler_time (t : ℝ) (ht : 0 < t) (x : ℝ)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {M B : ℝ}
    (hgb : ∀ z, ‖g z‖ ≤ M) (hdgb : ∀ z, ‖deriv g z‖ ≤ B) :
    Integrable (fun y => deriv g (a t * x + b t * y) *
      (-a t * x + (a t ^ 2 / b t) * y)) γ ∧
    HasDerivAt (fun s => GaussianMehler.mehler s g x)
      (∫ y, deriv g (a t * x + b t * y) *
        (-a t * x + (a t ^ 2 / b t) * y) ∂γ) t := by
  let U : Set ℝ := {s : ℝ | b t / 2 < b s} ∩ Set.Ioi 0
  let F : ℝ → ℝ → ℝ := fun s y => g (a s * x + b s * y)
  let F' : ℝ → ℝ → ℝ := fun s y => deriv g (a s * x + b s * y) *
    (-a s * x + (a s ^ 2 / b s) * y)
  let bound : ℝ → ℝ := fun y => B * (|x| + |y| / (b t / 2))
  obtain ⟨hc, hU, hlocal⟩ := b_local_lower_bound t ht
  have hB : 0 ≤ B := by
    have h := hdgb 0
    rw [Real.norm_eq_abs] at h
    exact (abs_nonneg _).trans h
  have hFmeas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) γ := by
    apply Filter.Eventually.of_forall
    intro s
    exact (hg.continuous.measurable.comp (by fun_prop)).aestronglyMeasurable
  have hFint : Integrable (F t) γ := by
    change Integrable (fun y => g (a t * x + b t * y)) γ
    apply GaussianMehler.integrable_comp_of_bounded hg.continuous.measurable hgb
    fun_prop
  have hF'meas : AEStronglyMeasurable (F' t) γ := by
    exact (((hg.continuous_deriv le_rfl).measurable.comp (by fun_prop)).mul
      (by fun_prop : Measurable (fun y : ℝ =>
        -a t * x + (a t ^ 2 / b t) * y))).aestronglyMeasurable
  have hmoment : Integrable (fun y : ℝ => |y|) γ :=
    ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)).abs
  have hbound_int : Integrable bound γ := by
    convert ((integrable_const (|x|)).add (hmoment.const_mul (1 / (b t / 2)))).const_mul B using 1
    funext y
    dsimp [bound]
    ring
  have hbound : ∀ᵐ y ∂γ, ∀ s ∈ U, ‖F' s y‖ ≤ bound y := by
    filter_upwards with y s hs
    change ‖deriv g (a s * x + b s * y) *
      (-a s * x + (a s ^ 2 / b s) * y)‖ ≤
      B * (|x| + |y| / (b t / 2))
    rw [Real.norm_eq_abs, abs_mul]
    have hv := velocity_bound t ht hs x y
    have hg' : |deriv g (a s * x + b s * y)| ≤ B := by
      simpa only [Real.norm_eq_abs] using hdgb _
    exact (mul_le_mul_of_nonneg_right hg' (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hv hB)
  have hdiff : ∀ᵐ y ∂γ, ∀ s ∈ U, HasDerivAt (F · y) (F' s y) s := by
    filter_upwards with y s hs
    obtain ⟨hspos, _⟩ := hlocal s hs
    have hinner : HasDerivAt (fun r : ℝ => a r * x + b r * y)
        (-a s * x + (a s ^ 2 / b s) * y) s := by
      exact ((hasDerivAt_a s).mul_const x).add ((hasDerivAt_b s hspos).mul_const y)
    have hf : HasDerivAt g (deriv g (a s * x + b s * y)) (a s * x + b s * y) :=
      (hg.differentiable (by simp)).differentiableAt.hasDerivAt
    exact hf.comp s hinner
  obtain ⟨hint, hderiv⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le hU hFmeas hFint
      hF'meas hbound hbound_int hdiff
  have hF : (fun s => ∫ y, F s y ∂γ) = fun s => GaussianMehler.mehler s g x := rfl
  rw [hF] at hderiv
  exact ⟨hint, hderiv⟩

/-- The actual Mathlib time derivative of the existing Mehler semigroup at positive time. -/
theorem deriv_mehler_time (t : ℝ) (ht : 0 < t) (x : ℝ)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {M B : ℝ}
    (hgb : ∀ z, ‖g z‖ ≤ M) (hdgb : ∀ z, ‖deriv g z‖ ≤ B) :
    deriv (fun s => GaussianMehler.mehler s g x) t =
      ∫ y, deriv g (a t * x + b t * y) *
        (-a t * x + (a t ^ 2 / b t) * y) ∂γ :=
  (hasDerivAt_mehler_time t ht x hg hgb hdgb).2.deriv

end OperatorDerivativeRewrite.Foundation.GaussianMehlerTimeDerivative
