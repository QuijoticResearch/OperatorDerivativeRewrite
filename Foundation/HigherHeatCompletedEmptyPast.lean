import Foundation.HigherHeatEmptyPastBound
import Foundation.HigherHeatCompletedCausalProjection

/-! Completed empty-past observable projection and actual signed expectation extension. -/
noncomputable section
open scoped NNReal

namespace OperatorDerivativeRewrite.Foundation.HigherHeatCompletedEmptyPast
open HigherHeatPolynomialCylinders HigherHeatPolynomialCoordinates HigherHeatAnalyticCylinderDomain
open HigherHeatCylindricalConditioning HigherHeatEmptyPastBound HigherHeatCompletedCausalProjection

theorem empty_base (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (b : ℕ) (F : Cylinder) :
    dyadicProjection m hm T hT 0 0 F = dyadicProjection m hm T hT b 0 F := by
  apply tail_induction b (fun F =>
    dyadicProjection m hm T hT 0 0 F = dyadicProjection m hm T hT b 0 F) _ F
  intro n hn P
  rw [dyadicProjection_apply m hm T hT 0 0 n (Nat.zero_le n),
    dyadicProjection_apply m hm T hT b 0 n hn]
  simp only [zero_mul]

theorem core_empty_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (F : Cylinder) :
    ‖core (dyadicProjection m hm T hT 0 0 F)‖ ≤ Real.exp (T:ℝ) * ‖core F‖ := by
  apply tail_induction 0 (fun F =>
    ‖core (dyadicProjection m hm T hT 0 0 F)‖ ≤ Real.exp (T:ℝ) * ‖core F‖) _ F
  intro n hn P
  rw [dyadicProjection_apply m hm T hT 0 0 n hn]
  have he : HigherHeatDyadicConditioning.initialPast n 0 = ∅ := by
    ext i
    simp [HigherHeatDyadicConditioning.initialPast]
  simp only [zero_mul, he, core_norm, cylinderSeminorm_grid]
  exact local_empty_bound n m hm T hT P

def emptyProjection (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) : Domain →L[ℝ] Domain :=
  (core.comp (dyadicProjection m hm T hT 0 0)).extendOfNorm core

theorem emptyProjection_core (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (F : Cylinder) :
    emptyProjection m hm T hT (core F) = core (dyadicProjection m hm T hT 0 0 F) :=
  LinearMap.extendOfNorm_eq core_dense ⟨Real.exp (T:ℝ), core_empty_bound m hm T hT⟩ F

theorem emptyProjection_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (u : Domain) :
    ‖emptyProjection m hm T hT u‖ ≤ Real.exp (T:ℝ) * ‖u‖ :=
  LinearMap.norm_extendOfNorm_apply_le core_dense (Real.exp (T:ℝ)) (core_empty_bound m hm T hT) u

theorem emptyProjection_norm (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    ‖emptyProjection m hm T hT‖ ≤ Real.exp (T:ℝ) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le (emptyProjection_bound m hm T hT)

theorem emptyProjection_unique (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (L : Domain →L[ℝ] Domain)
    (hL : ∀ F, L (core F) = core (dyadicProjection m hm T hT 0 0 F)) :
    L = emptyProjection m hm T hT := by
  apply ContinuousLinearMap.coeFn_injective
  apply core_dense.equalizer L.continuous (emptyProjection m hm T hT).continuous
  funext F
  exact (hL F).trans (emptyProjection_core m hm T hT F).symm

theorem emptyProjection_idempotent (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    (emptyProjection m hm T hT).comp (emptyProjection m hm T hT) = emptyProjection m hm T hT := by
  apply emptyProjection_unique m hm T hT
  intro F
  rw [ContinuousLinearMap.comp_apply, emptyProjection_core, emptyProjection_core,
    dyadicProjection_tower]
  rfl

theorem emptyProjection_left (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (r : Fin (size b)) :
    (emptyProjection m hm T hT).comp (completed m hm T hT b r) = emptyProjection m hm T hT := by
  apply emptyProjection_unique m hm T hT
  intro F
  rw [ContinuousLinearMap.comp_apply, completed_core, emptyProjection_core,
    empty_base m hm T hT b, dyadicProjection_tower]
  simp only [zero_min]
  exact congrArg core (empty_base m hm T hT b F).symm

theorem emptyProjection_right (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (r : Fin (size b)) :
    (completed m hm T hT b r).comp (emptyProjection m hm T hT) = emptyProjection m hm T hT := by
  apply emptyProjection_unique m hm T hT
  intro F
  rw [ContinuousLinearMap.comp_apply, emptyProjection_core, completed_core,
    empty_base m hm T hT b, dyadicProjection_tower]
  simp only [min_zero]

end OperatorDerivativeRewrite.Foundation.HigherHeatCompletedEmptyPast
