import Foundation.PhysicalHeatChainGamma
import Foundation.PhysicalHeatCompoundPoissonAtom

/-!
# A discrete compound-heat chain and its exact jump covariance

The transformed compound-Poisson symbol already has a genuine heat law. We
reuse the physical heat-chain path construction to obtain a countable-time
Markov chain whose one-step law is the actual Poisson mixture. Its short-time
character-increment covariance derivative equals the covariance of one
original heat jump. This is a discrete chain indexed by whole steps; the
derivative varies the Poisson rate of its one-step law. It does not construct
a cadlag continuous-time compound-Poisson process or a closed Gamma domain.
-/

open OperatorDerivativeRewrite.Foundation
open FiniteFourierDifferentialTrace FourierCovarianceCriterion
open PhysicalHeatChain PhysicalHeatCompoundPoisson PhysicalHeatCompoundPoissonAtom
open PhysicalHeatKernel FiniteStableGamma.Core
open MeasureTheory AddCircle ProbabilityTheory Function Preorder
open scoped NNReal ProbabilityTheory

noncomputable section

namespace OperatorDerivativeRewrite.Foundation.PhysicalHeatCompoundPoissonChainGamma

def compoundChainLaw (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (hr0 : r 0 = 0)
    (δ rate : ℝ≥0) (x₀ : UnitAddTorus (Fin 3)) :
    Measure (ℕ → UnitAddTorus (Fin 3)) :=
  chainLaw (jumpRate r δ) (jumpRate_covariance r hr hr0 δ)
    (jumpRate_zero r hr0 δ) rate x₀

instance compoundChainLaw_isProbability (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (hr0 : r 0 = 0)
    (δ rate : ℝ≥0) (x₀ : UnitAddTorus (Fin 3)) :
    IsProbabilityMeasure (compoundChainLaw r hr hr0 δ rate x₀) := by
  unfold compoundChainLaw
  infer_instance

theorem compoundChainLaw_condDistrib (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (hr0 : r 0 = 0)
    (δ rate : ℝ≥0) (x₀ : UnitAddTorus (Fin 3)) (n : ℕ) :
    condDistrib (fun path : ℕ → UnitAddTorus (Fin 3) => path (n+1))
      (frestrictLe n) (compoundChainLaw r hr hr0 δ rate x₀) =ᵐ[
        (compoundChainLaw r hr hr0 δ rate x₀).map (frestrictLe n)]
      stepKernel (jumpRate r δ) (jumpRate_covariance r hr hr0 δ)
        (jumpRate_zero r hr0 δ) rate n := by
  exact chainLaw_condDistrib (jumpRate r δ)
    (jumpRate_covariance r hr hr0 δ) (jumpRate_zero r hr0 δ) rate x₀ n

theorem compoundChainLaw_one_origin (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (hr0 : r 0 = 0)
    (δ rate : ℝ≥0) :
    (compoundChainLaw r hr hr0 δ rate 0).map (fun path => path 1) =
      compoundHeatLaw r hr hr0 δ rate := by
  unfold compoundChainLaw
  rw [chainLaw_one, heatKernel_apply]
  simp only [zero_add, Measure.map_id']
  exact (compoundHeatLaw_eq_heatLaw r hr hr0 δ rate).symm

theorem compoundChainLaw_one_origin_atom (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (hr0 : r 0 = 0)
    (δ rate : ℝ≥0) :
    0 < ((compoundChainLaw r hr hr0 δ rate 0).map (fun path => path 1))
      (Set.singleton (0 : UnitAddTorus (Fin 3))) := by
  rw [compoundChainLaw_one_origin]
  exact compoundHeatLaw_origin_atom_pos r hr hr0 δ rate

theorem jumpRate_gamma_is_heatJump_covariance (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (hr0 : r 0 = 0)
    (δ : ℝ≥0) (k l : Wave) :
    2 * kernel (fun q => (jumpRate r δ q : ℝ)) k l =
      (∫ z, (UnitAddTorus.mFourier (-l) z - 1) *
        (UnitAddTorus.mFourier k z - 1)
        ∂heatKernel r hr hr0 δ (0 : UnitAddTorus (Fin 3))).re := by
  rw [heatKernel_increment_pair]
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.one_re]
  simp only [kernel, jumpRate_coe, heatIncrementSymbol]
  ring

theorem compoundChainLaw_incrementPair_hasDerivWithinAt_zero
    (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (hr0 : r 0 = 0)
    (δ : ℝ≥0) (k l : Wave) :
    HasDerivWithinAt (fun t : ℝ =>
      (∫ path, (UnitAddTorus.mFourier (-k) (path 1) - 1) *
        (UnitAddTorus.mFourier l (path 1) - 1)
        ∂compoundChainLaw r hr hr0 δ (Real.toNNReal t) 0).re)
      (∫ z, (UnitAddTorus.mFourier (-l) z - 1) *
        (UnitAddTorus.mFourier k z - 1)
        ∂heatKernel r hr hr0 δ (0 : UnitAddTorus (Fin 3))).re
      (Set.Ici 0) 0 := by
  rw [← jumpRate_gamma_is_heatJump_covariance r hr hr0 δ k l]
  exact chainLaw_incrementPair_hasDerivWithinAt_zero
    (jumpRate r δ) (jumpRate_covariance r hr hr0 δ)
    (jumpRate_zero r hr0 δ) k l

end OperatorDerivativeRewrite.Foundation.PhysicalHeatCompoundPoissonChainGamma
