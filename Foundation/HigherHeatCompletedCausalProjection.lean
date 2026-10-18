import Foundation.HigherHeatFiniteCausalBound
import Foundation.HigherHeatAnalyticCylinderDomain
import Foundation.HigherHeatCylindricalConditioning
import Mathlib.Analysis.Normed.Operator.Extend

/-! Unique bounded extensions of actual positive-time dyadic signed observable projections.
These operators act on the complete common analytic test space, not a probability L2 space
or a chronological tensor-integrand domain. The empty past requires a separate estimate. -/
noncomputable section
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.HigherHeatCompletedCausalProjection
open HigherHeatPolynomialCylinders HigherHeatPolynomialCoordinates HigherHeatAnalyticCylinderDomain
open HigherHeatCylindricalConditioning HigherHeatFiniteCausalBound

def cutCount (b : ℕ) (r : Fin (size b)) (n : ℕ) : ℕ := (r.val+1)*2^(n-b)

theorem cutCount_pos (b : ℕ) (r : Fin (size b)) (n : ℕ) : 0 < cutCount b r n :=
  Nat.mul_pos (Nat.succ_pos _) (pow_pos (by decide) _)

theorem cutCount_le (b : ℕ) (r : Fin (size b)) (n : ℕ) (hn : b ≤ n) :
    cutCount b r n ≤ size n := by
  have he : size b * 2^(n-b) = size n := by
    simp only [size, HigherHeatDyadicLaws.gridSize_pow, ← pow_add, Nat.add_sub_of_le hn]
  exact (Nat.mul_le_mul_right (2^(n-b)) (Nat.succ_le_iff.mpr r.isLt)).trans he.le

def endpoint (b : ℕ) (r : Fin (size b)) (n : ℕ) (hn : b ≤ n) : Fin (size n) :=
  ⟨cutCount b r n - 1, by
    have hp := cutCount_pos b r n
    have hl := cutCount_le b r n hn
    omega⟩

theorem endpoint_count (b : ℕ) (r : Fin (size b)) (n : ℕ) (hn : b ≤ n) :
    (endpoint b r n hn).val+1 = cutCount b r n := by
  have hp := cutCount_pos b r n
  change cutCount b r n - 1 + 1 = cutCount b r n
  omega

theorem core_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (r : Fin (size b)) (F : Cylinder) :
    ‖core (dyadicProjection m hm T hT b (r.val+1) F)‖ ≤ Real.exp (T:ℝ) * ‖core F‖ := by
  apply tail_induction b (fun F =>
    ‖core (dyadicProjection m hm T hT b (r.val+1) F)‖ ≤ Real.exp (T:ℝ) * ‖core F‖) _ F
  intro n hn P
  rw [dyadicProjection_apply m hm T hT b (r.val+1) n hn P]
  simp only [core_norm, cylinderSeminorm_grid]
  have hc := localProjection_encode_bound n m hm T hT (endpoint b r n hn) P
  simpa only [endpoint_count, cutCount] using hc

def completed (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (r : Fin (size b)) : Domain →L[ℝ] Domain :=
  (core.comp (dyadicProjection m hm T hT b (r.val+1))).extendOfNorm core

theorem completed_core (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (r : Fin (size b)) (F : Cylinder) :
    completed m hm T hT b r (core F) = core (dyadicProjection m hm T hT b (r.val+1) F) :=
  LinearMap.extendOfNorm_eq core_dense ⟨Real.exp (T:ℝ), core_bound m hm T hT b r⟩ F

theorem completed_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (r : Fin (size b)) (u : Domain) :
    ‖completed m hm T hT b r u‖ ≤ Real.exp (T:ℝ) * ‖u‖ :=
  LinearMap.norm_extendOfNorm_apply_le core_dense (Real.exp (T:ℝ)) (core_bound m hm T hT b r) u

theorem completed_norm (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (r : Fin (size b)) : ‖completed m hm T hT b r‖ ≤ Real.exp (T:ℝ) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le (completed_bound m hm T hT b r)

theorem completed_unique (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (r : Fin (size b)) (L : Domain →L[ℝ] Domain)
    (hL : ∀ F, L (core F) = core (dyadicProjection m hm T hT b (r.val+1) F)) :
    L = completed m hm T hT b r := by
  apply ContinuousLinearMap.coeFn_injective
  apply core_dense.equalizer L.continuous (completed m hm T hT b r).continuous
  funext F
  exact (hL F).trans (completed_core m hm T hT b r F).symm

theorem completed_tower (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (r s : Fin (size b)) :
    (completed m hm T hT b r).comp (completed m hm T hT b s) =
      completed m hm T hT b (min r s) := by
  apply completed_unique m hm T hT b (min r s)
  intro F
  rw [ContinuousLinearMap.comp_apply, completed_core m hm T hT b s F,
    completed_core m hm T hT b r, dyadicProjection_tower]
  have he : min (r.val+1) (s.val+1) = (min r s).val+1 := by
    rcases le_total r s with h | h
    · rw [min_eq_left (Nat.add_le_add_right (show r.val ≤ s.val from h) 1), min_eq_left h]
    · rw [min_eq_right (Nat.add_le_add_right (show s.val ≤ r.val from h) 1), min_eq_right h]
  rw [he]

theorem completed_idempotent (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (r : Fin (size b)) :
    (completed m hm T hT b r).comp (completed m hm T hT b r) = completed m hm T hT b r := by
  simpa only [min_self] using completed_tower m hm T hT b r r

theorem completed_refinement (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (r : Fin (size b)) :
    completed m hm T hT b r = completed m hm T hT (b+1) (oldEmbedding b r) := by
  apply completed_unique m hm T hT (b+1) (oldEmbedding b r)
  intro F
  rw [completed_core m hm T hT b r]
  have he : (oldEmbedding b r).val+1 = 2*(r.val+1) := by
    change (2*r.val+1)+1 = 2*(r.val+1)
    omega
  rw [he]
  exact congrArg core (dyadicProjection_refinement m hm T hT b (r.val+1) F)

def pastSpace (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (r : Fin (size b)) : Submodule ℝ Domain :=
  (completed m hm T hT b r - ContinuousLinearMap.id ℝ Domain).ker

theorem mem_pastSpace (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (r : Fin (size b)) (u : Domain) :
    u ∈ pastSpace m hm T hT b r ↔ completed m hm T hT b r u = u := by
  change (completed m hm T hT b r - ContinuousLinearMap.id ℝ Domain) u = 0 ↔ _
  simp only [sub_apply, ContinuousLinearMap.id_apply, sub_eq_zero]

theorem pastSpace_closed (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (r : Fin (size b)) : IsClosed (pastSpace m hm T hT b r : Set Domain) :=
  (completed m hm T hT b r - ContinuousLinearMap.id ℝ Domain).isClosed_ker

theorem completed_fixed (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (r : Fin (size b)) (u : Domain) :
    completed m hm T hT b r (completed m hm T hT b r u) = completed m hm T hT b r u :=
  DFunLike.congr_fun (completed_idempotent m hm T hT b r) u

theorem range_eq_pastSpace (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (r : Fin (size b)) :
    Set.range (completed m hm T hT b r) = (pastSpace m hm T hT b r : Set Domain) := by
  ext u
  constructor
  · rintro ⟨v, rfl⟩
    exact (mem_pastSpace m hm T hT b r _).mpr (completed_fixed m hm T hT b r v)
  · intro hu
    exact ⟨u, (mem_pastSpace m hm T hT b r u).mp hu⟩

theorem range_closed (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (r : Fin (size b)) : IsClosed (Set.range (completed m hm T hT b r)) := by
  rw [range_eq_pastSpace]
  exact pastSpace_closed m hm T hT b r

theorem closure_projected_core (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (r : Fin (size b)) :
    closure (Set.range (fun F => completed m hm T hT b r (core F))) =
      Set.range (completed m hm T hT b r) := by
  have he : Set.range (fun F => completed m hm T hT b r (core F)) =
      (completed m hm T hT b r) '' Set.range core := by
    ext u
    constructor
    · rintro ⟨F, rfl⟩
      exact ⟨core F, ⟨F, rfl⟩, rfl⟩
    · rintro ⟨v, ⟨F, rfl⟩, rfl⟩
      exact ⟨F, rfl⟩
  rw [he]
  apply Set.Subset.antisymm
  · apply closure_minimal _ (range_closed m hm T hT b r)
    rintro u ⟨v, hv, rfl⟩
    exact ⟨v, rfl⟩
  · rintro u ⟨v, rfl⟩
    exact mem_closure_image (completed m hm T hT b r).continuous.continuousAt (core_dense v)

end OperatorDerivativeRewrite.Foundation.HigherHeatCompletedCausalProjection
