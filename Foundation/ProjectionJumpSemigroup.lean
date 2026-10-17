import Foundation.AcceleratedDecayBoundary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.TangentCone.Real

/-! The exact differentiability domain of the instantaneous projection semigroup.
The algebraic semigroup law alone supplies no strong continuity at zero. -/
noncomputable section
open Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.ProjectionJumpSemigroup
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def jump (P : E →L[ℝ] E) (t : ℝ) : E →L[ℝ] E :=
  if t = 0 then ContinuousLinearMap.id ℝ E else P

theorem jump_zero (P : E →L[ℝ] E) : jump P 0 = ContinuousLinearMap.id ℝ E := by
  simp [jump]

theorem jump_positive (P : E →L[ℝ] E) {t : ℝ} (ht : 0 < t) : jump P t = P := by
  simp [jump, ne_of_gt ht]

theorem compose (P : E →L[ℝ] E) (hP : P.comp P = P)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    jump P (s+t) = (jump P t).comp (jump P s) := by
  by_cases hsz : s = 0
  · subst s; simp [jump]
  by_cases htz : t = 0
  · subst t; simp [jump]
  have hst : s+t ≠ 0 := ne_of_gt (add_pos (lt_of_le_of_ne hs (Ne.symm hsz))
    (lt_of_le_of_ne ht (Ne.symm htz)))
  simp [jump, hsz, htz, hst, hP]

theorem contractive (P : E →L[ℝ] E) (hP : ∀ x, ‖P x‖ ≤ ‖x‖) (t : ℝ) (x : E) :
    ‖jump P t x‖ ≤ ‖x‖ := by
  by_cases ht : t = 0 <;> simp [jump, ht, hP x]

theorem continuous_iff_fixed (P : E →L[ℝ] E) (x : E) :
    ContinuousWithinAt (fun t => jump P t x) (Ici 0) 0 ↔ P x = x := by
  constructor
  · intro hc
    have ht := hc.tendsto.mono_left (nhdsWithin_mono (0 : ℝ) Ioi_subset_Ici_self)
    have he : (fun t => jump P t x) =ᶠ[𝓝[>] (0 : ℝ)] fun _ => P x := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact congrArg (fun A : E →L[ℝ] E => A x) (jump_positive P ht)
    have hh := tendsto_nhds_unique (ht.congr' he)
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => P x) (𝓝[>] 0) (𝓝 (P x)))
    simpa [jump] using hh.symm
  · intro hx
    have he : (fun t => jump P t x) = fun _ => x := by
      funext t; by_cases ht : t = 0 <;> simp [jump, ht, hx]
    rw [he]
    exact continuousWithinAt_const

theorem derivative_iff (P : E →L[ℝ] E) (x v : E) :
    HasDerivWithinAt (fun t => jump P t x) v (Ici 0) 0 ↔ P x = x ∧ v = 0 := by
  constructor
  · intro hd
    have hx := (continuous_iff_fixed P x).mp hd.continuousWithinAt
    refine ⟨hx, ?_⟩
    have he : (fun t => jump P t x) = fun _ => x := by
      funext t; by_cases ht : t = 0 <;> simp [jump, ht, hx]
    rw [he] at hd
    have hzero := (hasDerivAt_const (0 : ℝ) x).hasDerivWithinAt (s := Ici 0)
    exact (hd.derivWithin (uniqueDiffWithinAt_Ici 0)).symm.trans
      (hzero.derivWithin (uniqueDiffWithinAt_Ici 0))
  · rintro ⟨hx, rfl⟩
    have he : (fun t => jump P t x) = fun _ => x := by
      funext t; by_cases ht : t = 0 <;> simp [jump, ht, hx]
    rw [he]
    exact (hasDerivAt_const (0 : ℝ) x).hasDerivWithinAt

theorem differentiable_iff_fixed (P : E →L[ℝ] E) (x : E) :
    DifferentiableWithinAt ℝ (fun t => jump P t x) (Ici 0) 0 ↔ P x = x := by
  constructor
  · intro h
    exact (continuous_iff_fixed P x).mp h.continuousWithinAt
  · intro h
    exact ((derivative_iff P x 0).mpr ⟨h, rfl⟩).differentiableWithinAt

theorem fixed_set_closed (P : E →L[ℝ] E) : IsClosed {x : E | P x = x} :=
  isClosed_eq P.continuous continuous_id

theorem domain_not_dense (P : E →L[ℝ] E) (hx : ∃ x, P x ≠ x) :
    ¬ Dense {x : E | DifferentiableWithinAt ℝ (fun t => jump P t x) (Ici 0) 0} := by
  simp only [differentiable_iff_fixed]
  intro hd
  have he : {x : E | P x = x} = univ := by
    rw [← (fixed_set_closed P).closure_eq]
    exact hd.closure_eq
  obtain ⟨x, hx⟩ := hx
  exact hx (by have hm : x ∈ ({x : E | P x = x} : Set E) := by rw [he]; trivial
               exact hm)

end OperatorDerivativeRewrite.Foundation.ProjectionJumpSemigroup
