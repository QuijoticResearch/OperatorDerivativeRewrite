import Foundation.SU2SignBottleneck

/-! Persistence of the actual stationary loop slow mode under iteration.
The finite-loop operator is used throughout; no four-dimensional transfer
operator or relation between coupling and physical spacing is assumed. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology
open OperatorDerivativeRewrite.Foundation.SU2VariationalGap
open OperatorDerivativeRewrite.Foundation.SU2SignBottleneck

namespace OperatorDerivativeRewrite.Foundation.SU2SlowModeIteration

def steps (r : ℝ) : ℕ → StateL2 r → StateL2 r
  | 0, f => f
  | n + 1, f => operator r (steps r n f)

def dissipation (r : ℝ) (f : StateL2 r) : ℝ :=
  inner ℝ f f - inner ℝ (operator r f) f

private theorem inner_lower (r : ℝ) (f : StateL2 r) :
    -inner ℝ f f ≤ inner ℝ (operator r f) f := by
  have h := abs_real_inner_le_norm (operator r f) f
  have hc := operator_contraction r f
  rw [real_inner_self_eq_norm_sq]
  nlinarith [norm_nonneg f, norm_nonneg (operator r f), neg_le_abs (inner ℝ (operator r f) f)]

theorem dissipation_nonneg (r : ℝ) (f : StateL2 r) : 0 ≤ dissipation r f := by
  have h := real_inner_le_norm (operator r f) f
  have hc := operator_contraction r f
  rw [dissipation, real_inner_self_eq_norm_sq]
  nlinarith [norm_nonneg f]

/-- Reversibility and contraction make the one-step Dirichlet form decrease. -/
theorem dissipation_contracts (r : ℝ) (f : StateL2 r) :
    dissipation r (operator r f) ≤ dissipation r f := by
  have h := inner_lower r (f - operator r f)
  simp only [map_sub, inner_sub_left, inner_sub_right] at h
  rw [operator_symmetric r (operator r f) f] at h
  simp only [real_inner_comm f (operator r f)] at h
  have hcomm := real_inner_comm f (operator r f)
  dsimp [dissipation]
  linarith

theorem steps_dissipation (r : ℝ) (n : ℕ) (f : StateL2 r) :
    dissipation r (steps r n f) ≤ dissipation r f := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (dissipation_contracts r (steps r n f)).trans ih

private theorem square_loss (r : ℝ) (f : StateL2 r) :
    inner ℝ f f - inner ℝ (operator r f) (operator r f) ≤ 2 * dissipation r f := by
  have h : 0 ≤ inner ℝ (f - operator r f) (f - operator r f) := real_inner_self_nonneg
  simp only [inner_sub_left, inner_sub_right, real_inner_comm f (operator r f)] at h
  have hcomm := real_inner_comm f (operator r f)
  dsimp [dissipation]
  linarith

theorem steps_square_lower (r : ℝ) (n : ℕ) (f : StateL2 r) :
    inner ℝ f f - 2 * (n : ℝ) * dissipation r f ≤
      inner ℝ (steps r n f) (steps r n f) := by
  induction n with
  | zero => simp [steps]
  | succ n ih =>
    have h := square_loss r (steps r n f)
    have hd := steps_dissipation r n f
    simp only [steps, Nat.cast_add, Nat.cast_one]
    nlinarith

private theorem steps_add (r : ℝ) (n m : ℕ) (f : StateL2 r) :
    steps r (n + m) f = steps r n (steps r m f) := by
  induction n with
  | zero => simp [steps]
  | succ n ih => simp only [Nat.succ_add, steps, ih]

private theorem steps_symmetric (r : ℝ) (n : ℕ) (f g : StateL2 r) :
    inner ℝ (steps r n f) g = inner ℝ f (steps r n g) := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    change inner ℝ (operator r (steps r n f)) g = _
    rw [operator_symmetric, ih]
    have hc : steps r n (operator r g) = operator r (steps r n g) := by
      clear ih
      induction n with
      | zero => rfl
      | succ n hn => simp only [steps, hn]
    rw [hc]
    rfl

/-- All iteration counts, including odd ones; no positive-spectrum assumption. -/
theorem lag_lower (r : ℝ) (n : ℕ) (f : StateL2 r) :
    inner ℝ f f - (n : ℝ) * dissipation r f ≤ inner ℝ (steps r n f) f := by
  have heven (k : ℕ) :
      inner ℝ f f - ((k + k:ℕ):ℝ) * dissipation r f ≤ inner ℝ (steps r (k + k) f) f := by
    rw [steps_add, steps_symmetric]
    simpa only [Nat.cast_add, two_mul] using steps_square_lower r k f
  have hodd (k : ℕ) :
      inner ℝ f f - ((k + k + 1:ℕ):ℝ) * dissipation r f ≤ inner ℝ (steps r (k + k + 1) f) f := by
    have hb := steps_square_lower r k f
    have hd := steps_dissipation r k f
    rw [show k + k + 1 = k + (k + 1) by omega, steps_add r k (k + 1), steps_symmetric, steps]
    dsimp [dissipation] at hd hb ⊢
    push_cast
    nlinarith
  rcases Nat.even_or_odd n with h | h
  · obtain ⟨k, rfl⟩ := h
    exact heven k
  · obtain ⟨k, hk⟩ := h
    rw [hk]
    simpa only [two_mul] using hodd k

/-- The previously verified exponential bottleneck persists for many actual
stationary transfer steps, rather than only in a one-step Rayleigh quotient. -/
theorem exponential_lag_persistence :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ r : ℝ in atTop,
      (∫ C, vector r C ∂SU2LoopEquilibrium.equilibriumLaw r) = 0 ∧
      0 < inner ℝ (vector r) (vector r) ∧
      ∀ n : ℕ, (1-(n : ℝ) * c * Real.exp (-r / 2)) * inner ℝ (vector r) (vector r) ≤
        inner ℝ (steps r n (vector r)) (vector r) := by
  obtain ⟨c, hc, h⟩ := exponential_variational_obstruction
  refine ⟨c,hc,?_⟩
  filter_upwards [h] with r hr
  refine ⟨hr.1, hr.2.1, ?_⟩
  intro n
  have hl := lag_lower r n (vector r)
  have he : dissipation r (vector r) ≤
      c * Real.exp (-r / 2) * inner ℝ (vector r) (vector r) := hr.2.2
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

theorem steps_norm (r : ℝ) (n : ℕ) (f : StateL2 r) : ‖steps r n f‖ ≤ ‖f‖ := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (operator_contraction r (steps r n f)).trans ih

theorem lag_upper (r : ℝ) (n : ℕ) (f : StateL2 r) :
    inner ℝ (steps r n f) f ≤ inner ℝ f f := by
  have h := real_inner_le_norm (steps r n f) f
  have hc := steps_norm r n f
  rw [real_inner_self_eq_norm_sq]
  nlinarith [norm_nonneg f]

/-- Normalized stationary sign covariance; claims about this ratio below use
strictly positive variance, eventually supplied by the actual sign theorem. -/
def normalizedLag (r : ℝ) (n : ℕ) : ℝ :=
  inner ℝ (steps r n (vector r)) (vector r) / inner ℝ (vector r) (vector r)

theorem necessary_step_budget (r c q : ℝ) (n : ℕ)
    (hv : 0 < inner ℝ (vector r) (vector r))
    (he : dissipation r (vector r) ≤ c * Real.exp (-r / 2) * inner ℝ (vector r) (vector r))
    (hq : normalizedLag r n ≤ q) : (1 - q) * Real.exp (r / 2) ≤ (n : ℝ) * c := by
  have hl := lag_lower r n (vector r)
  have hu := (div_le_iff₀ hv).mp hq
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hh : 1 - q ≤ (n : ℝ) * c * Real.exp (-r / 2) := by
    have hm := mul_le_mul_of_nonneg_left he hn
    nlinarith
  have hx := mul_le_mul_of_nonneg_right hh (Real.exp_pos (r / 2)).le
  have heq : Real.exp (-r / 2) * Real.exp (r / 2) = 1 := by
    rw [← Real.exp_add, show -r / 2 + r / 2 = 0 by ring, Real.exp_zero]
  calc
    (1 - q) * Real.exp (r / 2) ≤ ((n : ℝ) * c * Real.exp (-r / 2)) * Real.exp (r / 2) := hx
    _ = (n : ℝ) * c := by rw [mul_assoc, heq, mul_one]

/-- A norm-contraction claim for the actual centered sign vector must pay the
same exponential iteration budget. The covariance estimate is necessary even
when an argument targets the stronger L2 operator norm. -/
theorem norm_contraction_requires_steps (r c q : ℝ) (n : ℕ)
    (hv : 0 < inner ℝ (vector r) (vector r))
    (he : dissipation r (vector r) ≤ c * Real.exp (-r / 2) * inner ℝ (vector r) (vector r))
    (hq : ‖steps r n (vector r)‖ ≤ q * ‖vector r‖) :
    (1 - q) * Real.exp (r / 2) ≤ (n : ℝ) * c := by
  apply necessary_step_budget r c q n hv he
  apply (div_le_iff₀ hv).mpr
  have hi := real_inner_le_norm (steps r n (vector r)) (vector r)
  have hm := mul_le_mul_of_nonneg_right hq (norm_nonneg (vector r))
  rw [real_inner_self_eq_norm_sq]
  nlinarith

/-- Any iteration clock small relative to exp(r / 2) retains normalized covariance
one in the limit. This is an actual finite-loop operator statement. -/
theorem slow_clock_persistence (n : ℝ → ℕ)
    (hn : Tendsto (fun r => (n r : ℝ) * Real.exp (-r / 2)) atTop (𝓝 0)) :
    Tendsto (fun r => normalizedLag r (n r)) atTop (𝓝 1) := by
  obtain ⟨c, hc, h⟩ := exponential_lag_persistence
  have hl : Tendsto (fun r => 1 - c * ((n r : ℝ) * Real.exp (-r / 2))) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (hn.const_mul c)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [h] with r hr
    apply (le_div_iff₀ hr.2.1).mpr
    have hh := hr.2.2 (n r)
    convert hh using 1; ring
  · filter_upwards [h] with r hr
    exact (div_le_iff₀ hr.2.1).mpr (by simpa using lag_upper r (n r) (vector r))

/-- Conditional physical scale test: a(r)=exp(-κr), bounded distance n(r)a(r).
The strict κ<1 / 2 hypothesis is essential to this estimate; no actual Yang--Mills
coupling/spacing identification is claimed. -/
theorem exponential_spacing_clock (κ L : ℝ) (hκ : κ < 1 / 2) (n : ℝ → ℕ)
    (hn : ∀ᶠ r : ℝ in atTop, (n r : ℝ) * Real.exp (-κ * r) ≤ L) :
    Tendsto (fun r => (n r : ℝ) * Real.exp (-r / 2)) atTop (𝓝 0) := by
  have hx : Tendsto (fun r : ℝ => Real.exp ((κ - 1 / 2) * r)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
  have hu : Tendsto (fun r : ℝ => L * Real.exp ((κ - 1 / 2) * r)) atTop (𝓝 0) := by
    simpa using hx.const_mul L
  apply squeeze_zero' (Eventually.of_forall (fun r => by positivity)) ?_ hu
  filter_upwards [hn] with r hr
  calc
    (n r : ℝ) * Real.exp (-r / 2) =
        ((n r : ℝ) * Real.exp (-κ * r)) * Real.exp ((κ - 1 / 2) * r) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring
    _ ≤ L * Real.exp ((κ - 1 / 2) * r) :=
      mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le

theorem bounded_physical_distance_persistence (κ L : ℝ) (hκ : κ < 1 / 2) (n : ℝ → ℕ)
    (hn : ∀ᶠ r : ℝ in atTop, (n r : ℝ) * Real.exp (-κ * r) ≤ L) :
    Tendsto (fun r => normalizedLag r (n r)) atTop (𝓝 1) :=
  slow_clock_persistence n (exponential_spacing_clock κ L hκ n hn)

/-- Strict fixed contraction cannot hold along such a bounded-distance clock. -/
theorem no_bounded_distance_contraction (κ L q : ℝ) (hκ : κ < 1 / 2) (hq : q < 1)
    (n : ℝ → ℕ) (hn : ∀ᶠ r : ℝ in atTop, (n r : ℝ) * Real.exp (-κ * r) ≤ L) :
    ¬∀ᶠ r : ℝ in atTop, normalizedLag r (n r) ≤ q := by
  intro h
  have ht := (tendsto_order.mp (bounded_physical_distance_persistence κ L hκ n hn)).1 q hq
  obtain ⟨r, hr, hr'⟩ := (h.and ht).exists
  exact (not_lt_of_ge hr) hr'

end OperatorDerivativeRewrite.Foundation.SU2SlowModeIteration
