import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Generalization of the verified SU2SlowModeIteration Hilbert argument.
It is used for the actual seven-link stationary transfer, and assumes no
nonnegative-spectrum hypothesis. Existing loop declarations are unchanged. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.SelfAdjointContractionIteration
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def steps (T : E →L[ℝ] E) : ℕ → E → E
  | 0,f => f
  | n+1,f => T (steps T n f)

def dissipation (T : E →L[ℝ] E) (f : E) : ℝ := inner ℝ f f-inner ℝ (T f) f

variable (T : E →L[ℝ] E) (hc : ∀ f,‖T f‖ ≤ ‖f‖)
variable (hs : ∀ f g,inner ℝ (T f) g=inner ℝ f (T g))
include hc hs

private theorem inner_lower (f : E) :
    -inner ℝ f f ≤ inner ℝ (T f) f := by
  have h := abs_real_inner_le_norm (T f) f
  have hc := hc f
  rw [real_inner_self_eq_norm_sq]
  nlinarith [norm_nonneg f, norm_nonneg (T f), neg_le_abs (inner ℝ (T f) f)]

theorem dissipation_nonneg (f : E) : 0 ≤ dissipation T f := by
  have h := real_inner_le_norm (T f) f
  have hc := hc f
  rw [dissipation, real_inner_self_eq_norm_sq]
  nlinarith [norm_nonneg f]

/-- Reversibility and contraction make the one-step Dirichlet form decrease. -/
theorem dissipation_contracts (f : E) :
    dissipation T (T f) ≤ dissipation T f := by
  have h := inner_lower T hc hs (f - T f)
  simp only [map_sub, inner_sub_left, inner_sub_right] at h
  rw [hs (T f) f] at h
  simp only [real_inner_comm f (T f)] at h
  have hcomm := real_inner_comm f (T f)
  dsimp [dissipation]
  linarith

theorem steps_dissipation (n : ℕ) (f : E) :
    dissipation T (steps T n f) ≤ dissipation T f := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (dissipation_contracts T hc hs (steps T n f)).trans ih

private theorem square_loss (f : E) :
    inner ℝ f f - inner ℝ (T f) (T f) ≤ 2 * dissipation T f := by
  have h : 0 ≤ inner ℝ (f - T f) (f - T f) := real_inner_self_nonneg
  simp only [inner_sub_left, inner_sub_right, real_inner_comm f (T f)] at h
  have hcomm := real_inner_comm f (T f)
  dsimp [dissipation]
  linarith

theorem steps_square_lower (n : ℕ) (f : E) :
    inner ℝ f f - 2 * (n : ℝ) * dissipation T f ≤
      inner ℝ (steps T n f) (steps T n f) := by
  induction n with
  | zero => simp [steps]
  | succ n ih =>
    have h := square_loss T hc hs (steps T n f)
    have hd := steps_dissipation T hc hs n f
    simp only [steps, Nat.cast_add, Nat.cast_one]
    nlinarith

private theorem steps_add (n m : ℕ) (f : E) :
    steps T (n + m) f = steps T n (steps T m f) := by
  induction n with
  | zero => simp [steps]
  | succ n ih => simp only [Nat.succ_add, steps, ih]

private theorem steps_symmetric (n : ℕ) (f g : E) :
    inner ℝ (steps T n f) g = inner ℝ f (steps T n g) := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    change inner ℝ (T (steps T n f)) g = _
    rw [hs, ih]
    have hc : steps T n (T g) = T (steps T n g) := by
      clear ih
      induction n with
      | zero => rfl
      | succ n hn => simp only [steps, hn]
    rw [hc]
    rfl

/-- All iteration counts, including odd ones; no positive-spectrum assumption. -/
theorem lag_lower (n : ℕ) (f : E) :
    inner ℝ f f - (n : ℝ) * dissipation T f ≤ inner ℝ (steps T n f) f := by
  have heven (k : ℕ) :
      inner ℝ f f - ((k + k:ℕ):ℝ) * dissipation T f ≤ inner ℝ (steps T (k + k) f) f := by
    rw [steps_add T hc hs, steps_symmetric T hc hs]
    simpa only [Nat.cast_add, two_mul] using steps_square_lower T hc hs k f
  have hodd (k : ℕ) :
      inner ℝ f f - ((k + k + 1:ℕ):ℝ) * dissipation T f ≤ inner ℝ (steps T (k + k + 1) f) f := by
    have hb := steps_square_lower T hc hs k f
    have hd := steps_dissipation T hc hs k f
    rw [show k + k + 1 = k + (k + 1) by omega, steps_add T hc hs k (k + 1), steps_symmetric T hc hs, steps]
    dsimp [dissipation] at hd hb ⊢
    push_cast
    nlinarith
  rcases Nat.even_or_odd n with h | h
  · obtain ⟨k, rfl⟩ := h
    exact heven k
  · obtain ⟨k, hk⟩ := h
    rw [hk]
    simpa only [two_mul] using hodd k


theorem steps_contraction (n : ℕ) (f : E) : ‖steps T n f‖ ≤ ‖f‖ := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (hc (steps T n f)).trans ih

theorem lag_upper (n : ℕ) (f : E) : inner ℝ (steps T n f) f ≤ inner ℝ f f := by
  have he := real_inner_le_norm (steps T n f) f
  have hn := steps_contraction T hc hs n f
  rw [real_inner_self_eq_norm_sq]
  nlinarith [norm_nonneg f]

end OperatorDerivativeRewrite.Foundation.SelfAdjointContractionIteration
