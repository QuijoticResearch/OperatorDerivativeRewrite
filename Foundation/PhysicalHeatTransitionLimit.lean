import Foundation.PhysicalHeatMarkovOrder
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Compactness reduction for physical heat transition laws

The theorem below isolates the remaining harmonic input for a torus transition
law: a sequence of normalized finite Fourier squares whose autocorrelation
coefficients tend to one at every fixed frequency. Compactness of probability
measures and weak continuity of bounded character integrals then produce a
genuine probability measure with exactly the prescribed heat Fourier moments.
The existence of that approximate-square sequence, uniqueness of the law,
convolution composition, and stochastic paths are separate obligations.
-/

open OperatorDerivativeRewrite.Foundation
open FiniteFourierDifferentialTrace FourierCovarianceCriterion
open PhysicalHeatMarkovOrder
open MeasureTheory AddCircle Filter
open scoped NNReal ComplexConjugate Topology BoundedContinuousFunction

noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace OperatorDerivativeRewrite.Foundation.PhysicalHeatTransitionLimit

theorem exists_transition_of_approximate_squares
    (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (t : ℝ≥0)
    (f : ℕ → Fourier)
    (hf : ∀ n, (∑ k ∈ (f n).coeff.support,
      conj ((f n).coeff k) * (f n).coeff k) = 1)
    (hcoeff : ∀ k : Wave,
      Tendsto (fun n => (FiniteFourierReality.reflection (f n) * f n).coeff k)
        atTop (𝓝 1)) :
    ∃ μ : ProbabilityMeasure (UnitAddTorus (Fin 3)),
      ∀ k : Wave,
        (∫ x : UnitAddTorus (Fin 3), UnitAddTorus.mFourier (-k) x
          ∂(μ : Measure (UnitAddTorus (Fin 3)))) =
            (Real.exp (-((t : ℝ) * (r k : ℝ))) : ℂ) := by
  let μn : ℕ → ProbabilityMeasure (UnitAddTorus (Fin 3)) :=
    fun n => heatSquareProbability r hr hr0 t (f n) (hf n)
  obtain ⟨μ, φ, hmono, hlim⟩ := CompactSpace.tendsto_subseq μn
  refine ⟨μ, ?_⟩
  intro k
  let g : UnitAddTorus (Fin 3) →ᵇ ℂ :=
    (ContinuousMap.equivBoundedOfCompact (UnitAddTorus (Fin 3)) ℂ)
      (UnitAddTorus.mFourier (-k))
  have hμ : Tendsto (fun n => ∫ x, g x ∂(μn (φ n) : Measure (UnitAddTorus (Fin 3))))
      atTop (𝓝 (∫ x, g x ∂(μ : Measure (UnitAddTorus (Fin 3))))) :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hlim g
  have hc : Tendsto (fun n =>
      (FiniteFourierReality.reflection (f (φ n)) * f (φ n)).coeff k)
      atTop (𝓝 1) := (hcoeff k).comp hmono.tendsto_atTop
  have hprod : Tendsto (fun n =>
      (Real.exp (-((t : ℝ) * (r k : ℝ))) : ℂ) *
        (FiniteFourierReality.reflection (f (φ n)) * f (φ n)).coeff k)
      atTop (𝓝 ((Real.exp (-((t : ℝ) * (r k : ℝ))) : ℂ) * 1)) :=
    tendsto_const_nhds.mul hc
  have heq (n : ℕ) :
      (∫ x, g x ∂(μn (φ n) : Measure (UnitAddTorus (Fin 3)))) =
        (Real.exp (-((t : ℝ) * (r k : ℝ))) : ℂ) *
          (FiniteFourierReality.reflection (f (φ n)) * f (φ n)).coeff k := by
    simpa [μn, g, heatSquareProbability] using
      heatSquareMeasure_fourierCoeff r hr t (f (φ n)) k
  have hsame : (∫ x, g x ∂(μ : Measure (UnitAddTorus (Fin 3)))) =
      (Real.exp (-((t : ℝ) * (r k : ℝ))) : ℂ) := by
    have hprod' : Tendsto
        (fun n => ∫ x, g x ∂(μn (φ n) : Measure (UnitAddTorus (Fin 3))))
        atTop (𝓝 ((Real.exp (-((t : ℝ) * (r k : ℝ))) : ℂ))) := by
      simpa only [mul_one] using
        (hprod.congr' (Filter.Eventually.of_forall (fun n => (heq n).symm)))
    exact tendsto_nhds_unique hμ hprod'
  simpa [g] using hsame

end OperatorDerivativeRewrite.Foundation.PhysicalHeatTransitionLimit
