import Foundation.PeriodicCoarseHodgeRanks
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! The actual coarse curl Gram matrix and its complete Walsh action. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicCoarseGramAction
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicCoarseGaugeDiagnostics PeriodicCoarseWalshBasis
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def incidenceCoefficient (p : CoarseFace) (e : CoarseEdge) : ℤ :=
  (if e = (p.val.1,p.val.2.1) then 1 else 0) +
  (if e = (coarseShift p.val.1 p.val.2.1,p.val.2.2) then 1 else 0) -
  (if e = (coarseShift p.val.1 p.val.2.2,p.val.2.1) then 1 else 0) -
  (if e = (p.val.1,p.val.2.2) then 1 else 0)

def incidenceMatrix : Matrix CoarseFace CoarseEdge ℝ := LinearMap.toMatrix' coarseIncidence
def gramMatrix : Matrix CoarseEdge CoarseEdge ℝ := incidenceMatrix.transpose * incidenceMatrix
def H : Field →ₗ[ℝ] Field := Matrix.toLin' gramMatrix

theorem matrix_entry (p : CoarseFace) (e : CoarseEdge) :
    incidenceMatrix p e = (incidenceCoefficient p e : ℝ) := by
  rw [incidenceMatrix, LinearMap.toMatrix'_apply]
  simp [coarseIncidence, coarseCurl, incidenceCoefficient, Pi.single_apply, eq_comm]

theorem incidenceMatrix_mulVec (f : Field) : incidenceMatrix.mulVec f = coarseIncidence f :=
  LinearMap.toMatrix'_mulVec _ _

theorem H_apply (f : Field) : H f = gramMatrix.mulVec f := rfl

theorem H_entry (f : Field) (e : CoarseEdge) :
    H f e = ∑ p : CoarseFace, (incidenceCoefficient p e : ℝ) * coarseIncidence f p := by
  rw [H_apply, gramMatrix, ← Matrix.mulVec_mulVec, incidenceMatrix_mulVec]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, matrix_entry]

set_option maxHeartbeats 768000000 in
-- Finite integer incidence rows check the complete action on all64 Walsh modes.
theorem int_gram_mode : ∀ (a : Label) (e : CoarseEdge),
    (∑ p : CoarseFace, incidenceCoefficient p e *
      coarseIntCurl (modeZ a) p.val.1 p.val.2.1 p.val.2.2) =
      (4 * (a.1.card : ℤ)) * modeZ a e -
        (if a.2 ∈ a.1 then 4 * ∑ j ∈ a.1, modeZ (a.1,j) e else 0) := by decide

theorem H_mode (a : Label) :
    H (mode a) = (4 * (a.1.card : ℝ)) • mode a -
      (if a.2 ∈ a.1 then (4 : ℝ) • ∑ j ∈ a.1, mode (a.1,j) else 0) := by
  funext e
  rw [H_entry]
  have hc (p : CoarseFace) : coarseIncidence (mode a) p =
      (coarseIntCurl (modeZ a) p.val.1 p.val.2.1 p.val.2.2 : ℝ) :=
    coarseCurl_cast (modeZ a) _ _ _
  simp_rw [hc]
  by_cases h : a.2 ∈ a.1
  · simp only [h, ite_true, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, mode]
    have hi := int_gram_mode a e
    rw [if_pos h] at hi
    exact_mod_cast hi
  · simp only [h, ite_false, sub_zero, Pi.smul_apply, smul_eq_mul, mode]
    have hi := int_gram_mode a e
    rw [if_neg h, sub_zero] at hi
    exact_mod_cast hi

theorem H_sector_sum (T : Finset Direction) : H (∑ i ∈ T, mode (T,i)) = 0 := by
  rw [map_sum]
  have hs : (∑ i ∈ T, H (mode (T,i))) =
      ∑ i ∈ T, ((4 * (T.card : ℝ)) • mode (T,i) - (4 : ℝ) • ∑ j ∈ T, mode (T,j)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [H_mode, if_pos hi]
  rw [hs]
  funext e
  simp only [Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  ring

end OperatorDerivativeRewrite.Foundation.PeriodicCoarseGramAction
