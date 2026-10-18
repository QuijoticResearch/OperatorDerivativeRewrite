import Foundation.HigherHeatCausalPairing
import Foundation.HigherHeatCompletedPairing

/-! Signed symmetry and innovation annihilation for actual completed dyadic observable projections. -/
noncomputable section
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.HigherHeatCompletedCausalPairing
open HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain
open HigherHeatCylindricalConditioning HigherHeatCompletedCausalProjection
open HigherHeatCompletedEmptyPast HigherHeatCompletedSignedMean HigherHeatCompletedPairing
open HigherHeatCausalPairing

theorem completed_symmetric (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (r : Fin (size b)) (u v : Domain) :
    pairing m hm T hT (completed m hm T hT b r u) v =
      pairing m hm T hT u (completed m hm T hT b r v) := by
  refine core_dense.induction_on u ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro F
    refine core_dense.induction_on v ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro G
      rw [completed_core, completed_core, pairing_core_real, pairing_core_real]
      exact congrArg Complex.re
        (cylinder_projection_symmetric m hm T hT b
          (HigherHeatDyadicConditioning.initialPast b (r.val+1)) F G)

theorem pairing_projected (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (r : Fin (size b)) (u v : Domain) :
    pairing m hm T hT (completed m hm T hT b r u) (completed m hm T hT b r v) =
      pairing m hm T hT u (completed m hm T hT b r v) := by
  rw [completed_symmetric, completed_fixed]

theorem innovation_past (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (r : Fin (size b)) (u v : Domain)
    (hv : completed m hm T hT b r v = v) :
    pairing m hm T hT (u-completed m hm T hT b r u) v = 0 := by
  rw [map_sub, sub_apply, completed_symmetric, hv, sub_self]

theorem empty_pairing (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (u v : Domain) :
    pairing m hm T hT (emptyProjection m hm T hT u) v =
      mean m hm T hT u * mean m hm T hT v := by
  rw [emptyProjection_apply, map_smul, smul_apply,
    pairing_comm m hm T hT (core 1) v, pairing_one]
  rfl

theorem empty_symmetric (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (u v : Domain) :
    pairing m hm T hT (emptyProjection m hm T hT u) v =
      pairing m hm T hT u (emptyProjection m hm T hT v) := by
  rw [empty_pairing, pairing_comm m hm T hT u, empty_pairing, mul_comm]

end OperatorDerivativeRewrite.Foundation.HigherHeatCompletedCausalPairing
