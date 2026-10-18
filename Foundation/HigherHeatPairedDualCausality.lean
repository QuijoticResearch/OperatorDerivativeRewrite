import Foundation.HigherHeatCompletedCausalPairing

/-! Actual signed causal projections intertwine the completed pairing with dual pullback.
The induced continuous seminorm is not assumed nondegenerate or continuous in cut time. -/
noncomputable section
open scoped NNReal

namespace OperatorDerivativeRewrite.Foundation.HigherHeatPairedDualCausality
open HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain
open HigherHeatCompletedCausalProjection HigherHeatCompletedEmptyPast
open HigherHeatCompletedPairing HigherHeatCompletedCausalPairing

abbrev Dual := Domain →L[ℝ] ℝ

def pullback (P : Domain →L[ℝ] Domain) : Dual →L[ℝ] Dual :=
  (ContinuousLinearMap.compL ℝ Domain Domain ℝ).flip P

theorem pullback_apply (P : Domain →L[ℝ] Domain) (φ : Dual) : pullback P φ = φ.comp P := rfl

theorem pullback_bound (P : Domain →L[ℝ] Domain) (φ : Dual) :
    ‖pullback P φ‖ ≤ ‖P‖*‖φ‖ := by
  simpa only [pullback_apply, mul_comm] using ContinuousLinearMap.opNorm_comp_le φ P

theorem completed_intertwining (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (r : Fin (size b)) :
    (pairing m hm T hT).comp (completed m hm T hT b r) =
      (pullback (completed m hm T hT b r)).comp (pairing m hm T hT) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  exact completed_symmetric m hm T hT b r u v

theorem empty_intertwining (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    (pairing m hm T hT).comp (emptyProjection m hm T hT) =
      (pullback (emptyProjection m hm T hT)).comp (pairing m hm T hT) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  exact empty_symmetric m hm T hT u v

def dualSeminorm (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) : Seminorm ℝ Domain :=
  (normSeminorm ℝ Dual).comp (pairing m hm T hT).toLinearMap

theorem dualSeminorm_apply (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (u : Domain) :
    dualSeminorm m hm T hT u = ‖pairing m hm T hT u‖ := rfl

theorem dualSeminorm_zero_iff (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (u : Domain) :
    dualSeminorm m hm T hT u = 0 ↔ ∀ v : Domain, pairing m hm T hT u v = 0 := by
  rw [dualSeminorm_apply, ContinuousLinearMap.opNorm_zero_iff (pairing m hm T hT u)]
  exact ContinuousLinearMap.ext_iff

theorem dualSeminorm_continuous (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    Continuous (dualSeminorm m hm T hT) := by
  change Continuous (fun u => ‖pairing m hm T hT u‖)
  exact Continuous.norm (E := Dual) (pairing m hm T hT).continuous

theorem completed_dualSeminorm_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (r : Fin (size b)) (u : Domain) :
    dualSeminorm m hm T hT (completed m hm T hT b r u) ≤
      Real.exp (T:ℝ)*dualSeminorm m hm T hT u := by
  simp only [dualSeminorm_apply]
  have he := DFunLike.congr_fun (completed_intertwining m hm T hT b r) u
  change pairing m hm T hT (completed m hm T hT b r u) =
    pullback (completed m hm T hT b r) (pairing m hm T hT u) at he
  rw [he]
  exact (pullback_bound _ _).trans
    (mul_le_mul_of_nonneg_right (completed_norm m hm T hT b r) (ContinuousLinearMap.opNorm_nonneg _))

theorem empty_dualSeminorm_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (u : Domain) :
    dualSeminorm m hm T hT (emptyProjection m hm T hT u) ≤
      Real.exp (T:ℝ)*dualSeminorm m hm T hT u := by
  simp only [dualSeminorm_apply]
  have he := DFunLike.congr_fun (empty_intertwining m hm T hT) u
  change pairing m hm T hT (emptyProjection m hm T hT u) =
    pullback (emptyProjection m hm T hT) (pairing m hm T hT u) at he
  rw [he]
  exact (pullback_bound _ _).trans
    (mul_le_mul_of_nonneg_right (emptyProjection_norm m hm T hT) (ContinuousLinearMap.opNorm_nonneg _))

end OperatorDerivativeRewrite.Foundation.HigherHeatPairedDualCausality
