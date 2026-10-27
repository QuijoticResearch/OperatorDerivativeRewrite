import Foundation.PhysicalHeatCompoundPoisson

/-!
# The no-jump atom obstructs absolute-continuity smoothing

The `n=0` term in the genuine Poisson mixture is exactly a Dirac mass at
the torus origin with coefficient `exp(-rate)`. Consequently every finite
Poisson rate gives positive origin mass, and the compound law cannot be
absolutely continuous with respect to a reference measure whose origin
singleton is null. The conclusion is stated with that exact hypothesis;
no unproved Haar null-singleton instance or pathwise Poisson process is used.
-/

open OperatorDerivativeRewrite.Foundation
open PhysicalHeatCompoundPoisson PhysicalHeatConvolution
open FiniteFourierDifferentialTrace FourierCovarianceCriterion
open MeasureTheory ProbabilityTheory AddCircle
open scoped NNReal ENNReal

noncomputable section

namespace OperatorDerivativeRewrite.Foundation.PhysicalHeatCompoundPoissonAtom

theorem noJump_dirac_le (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (hr0 : r 0 = 0)
    (δ rate : ℝ≥0) :
    ENNReal.ofReal (Real.exp (-(rate : ℝ))) •
      Measure.dirac (0 : UnitAddTorus (Fin 3)) ≤
      compoundHeatLaw r hr hr0 δ rate := by
  have hle := Measure.le_sum (fun n : ℕ =>
    ENNReal.ofReal (poissonWeight rate n) •
      (heatLaw r hr hr0 ((n : ℝ≥0) * δ) : Measure (UnitAddTorus (Fin 3)))) 0
  rw [← compoundHeatLaw_sum] at hle
  simpa [poissonWeight, heatLaw_zero r hr hr0] using hle

theorem compoundHeatLaw_origin_atom (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (hr0 : r 0 = 0)
    (δ rate : ℝ≥0) :
    ENNReal.ofReal (Real.exp (-(rate : ℝ))) ≤
      compoundHeatLaw r hr hr0 δ rate (Set.singleton (0 : UnitAddTorus (Fin 3))) := by
  have he := (noJump_dirac_le r hr hr0 δ rate)
    (Set.singleton (0 : UnitAddTorus (Fin 3)))
  have h' : ENNReal.ofReal (Real.exp (-(rate : ℝ))) *
      (Set.singleton (0 : UnitAddTorus (Fin 3))).indicator 1 0 ≤
      compoundHeatLaw r hr hr0 δ rate (Set.singleton (0 : UnitAddTorus (Fin 3))) := by
    simpa using he
  have hval : (Set.singleton (0 : UnitAddTorus (Fin 3))).indicator
      (1 : UnitAddTorus (Fin 3) → ℝ≥0∞) 0 = 1 := by
    exact Set.indicator_of_mem (Set.mem_singleton _) 1
  rw [hval] at h'
  simpa using h'

theorem compoundHeatLaw_origin_atom_pos (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (hr0 : r 0 = 0)
    (δ rate : ℝ≥0) :
    0 < compoundHeatLaw r hr hr0 δ rate (Set.singleton (0 : UnitAddTorus (Fin 3))) := by
  have h := compoundHeatLaw_origin_atom r hr hr0 δ rate
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (Real.exp_pos _)) h

theorem compoundHeatLaw_not_ac_of_null_origin (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (hr0 : r 0 = 0)
    (δ rate : ℝ≥0) (ν : Measure (UnitAddTorus (Fin 3)))
    (hν : ν (Set.singleton (0 : UnitAddTorus (Fin 3))) = 0) :
    ¬ compoundHeatLaw r hr hr0 δ rate ≪ ν := by
  intro h
  have hz := h hν
  exact (ne_of_gt (compoundHeatLaw_origin_atom_pos r hr hr0 δ rate)) hz

end OperatorDerivativeRewrite.Foundation.PhysicalHeatCompoundPoissonAtom
