import Foundation.HigherHeatConditionalLinearObservables
import Foundation.HigherHeatPolynomialPathDomain
import Foundation.HigherHeatDyadicConditioning

/-! Native terminal-cylinder and conditional-position identities on every dyadic grid. -/
noncomputable section
open scoped NNReal BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatTerminalPositions
open HigherHeatPolynomialCylinders HigherHeatPolynomialPathDomain HigherHeatGridDoubling
open HigherHeatMultivariateMoments PureOrderPolynomialConditioning

def lastIndex (n : ℕ) : Fin (size n) :=
  ⟨size n-1, by have hp : 0 < size n := HigherHeatDyadicLaws.gridSize_pos n; omega⟩

theorem lastIndex_count (n : ℕ) : (lastIndex n).val+1 = size n := by
  have hp : 0 < size n := HigherHeatDyadicLaws.gridSize_pos n
  change size n-1+1 = size n
  omega

theorem lastIndex_step (n : ℕ) : oddIndex (lastIndex n) = lastIndex (n+1) := by
  apply Fin.ext
  change 2*(size n-1)+1 = size (n+1)-1
  change 2*(size n-1)+1 = 2*size n-1
  have hp : 0 < size n := HigherHeatDyadicLaws.gridSize_pos n
  omega

theorem positionPolynomial_last (n : ℕ) :
    positionPolynomial n (lastIndex n) = (terminal : Test n) := by
  have he : (Finset.univ.filter (fun j : Fin (size n) => j ≤ lastIndex n)) = Finset.univ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    change j.val ≤ size n-1
    have hj := j.isLt
    omega
  rw [positionPolynomial, he]
  rfl

theorem positionCylinder_last (n : ℕ) : positionCylinder n (lastIndex n) = terminalCylinder := by
  induction n with
  | zero => rw [positionCylinder, positionPolynomial_last]; rfl
  | succ n ih => rw [← lastIndex_step, position_refinement, ih]

theorem terminal_on_grid (n : ℕ) : terminalCylinder = cylinderOf n (terminal : Test n) := by
  rw [← positionCylinder_last n, positionCylinder, positionPolynomial_last]

theorem localProjection_terminal (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (r : Fin (size n)) :
    HigherHeatDyadicConditioning.localProjection m T n
      (HigherHeatDyadicConditioning.initialPast n (r.val+1)) (terminal : Test n) =
        positionPolynomial n r := by
  change conditioning (2*m) (parameters m (fun _ => HigherHeatDyadicLaws.duration T n))
    (HigherHeatDyadicConditioning.initialPast n (r.val+1)) (terminal : Test n) = _
  simp only [terminal, map_sum]
  simp_rw [HigherHeatConditionalLinearObservables.conditioning_X m hm
    (fun _ => HigherHeatDyadicLaws.duration T n)
    (fun _ => HigherHeatDyadicLaws.duration_pos T hT n)]
  rw [positionPolynomial, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  have he : j ∈ HigherHeatDyadicConditioning.initialPast n (r.val+1) ↔ j ≤ r := by
    simp only [HigherHeatDyadicConditioning.initialPast, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Nat.lt_succ_iff
  simp only [he]

end OperatorDerivativeRewrite.Foundation.HigherHeatTerminalPositions
