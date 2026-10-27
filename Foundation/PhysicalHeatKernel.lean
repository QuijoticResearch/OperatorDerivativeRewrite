import Foundation.PhysicalHeatWeakContinuity
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Physical heat Markov transition kernel

For each time and starting point, translate the verified torus heat law.
The kernel is Markov, its character integrals have the expected translated
heat multiplier, its compositions obey Chapman--Kolmogorov, and zero time is
the identity kernel. This constructs genuine transition kernels, not a
path-space process or a sample-path regularity theorem.
-/

open OperatorDerivativeRewrite.Foundation
open FiniteFourierDifferentialTrace FourierCovarianceCriterion
open PhysicalHeatConvolution PhysicalHeatLawUnique
open MeasureTheory AddCircle ProbabilityTheory
open scoped NNReal ProbabilityTheory

noncomputable section

namespace OperatorDerivativeRewrite.Foundation.PhysicalHeatKernel

def heatKernel (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (t : ℝ≥0) :
    Kernel (UnitAddTorus (Fin 3)) (UnitAddTorus (Fin 3)) :=
  Kernel.map
    ((Kernel.id : Kernel (UnitAddTorus (Fin 3)) (UnitAddTorus (Fin 3))) ×ₖ
      Kernel.const (UnitAddTorus (Fin 3))
        (heatLaw r hr hr0 t : Measure (UnitAddTorus (Fin 3))))
    (fun p => p.1 + p.2)

instance heatKernel_isMarkov (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (t : ℝ≥0) :
    IsMarkovKernel (heatKernel r hr hr0 t) := by
  unfold heatKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

theorem heatKernel_apply (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (t : ℝ≥0) (x : UnitAddTorus (Fin 3)) :
    heatKernel r hr hr0 t x =
      (heatLaw r hr hr0 t : Measure (UnitAddTorus (Fin 3))).map (fun y => x + y) := by
  unfold heatKernel
  rw [Kernel.map_apply _ (by fun_prop), Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

private theorem character_add (k : Wave) (x y : UnitAddTorus (Fin 3)) :
    UnitAddTorus.mFourier k (x + y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier k y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply,
    fourier_apply, zsmul_add, toCircle_add, Circle.coe_mul,
    Finset.prod_mul_distrib]

theorem heatKernel_character (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (t : ℝ≥0) (x : UnitAddTorus (Fin 3)) (k : Wave) :
    (∫ z, UnitAddTorus.mFourier (-k) z ∂heatKernel r hr hr0 t x) =
      UnitAddTorus.mFourier (-k) x *
        (Real.exp (-((t : ℝ) * (r k : ℝ))) : ℂ) := by
  rw [heatKernel_apply]
  rw [integral_map (by fun_prop)]
  · simp_rw [character_add]
    rw [integral_const_mul, heatLaw_character]
  · exact (UnitAddTorus.mFourier (-k)).continuous.measurable.aestronglyMeasurable

theorem heatKernel_comp (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (s t : ℝ≥0) :
    (heatKernel r hr hr0 t ∘ₖ heatKernel r hr hr0 s) =
      heatKernel r hr hr0 (s+t) := by
  apply Kernel.ext
  intro x
  let μ : ProbabilityMeasure (UnitAddTorus (Fin 3)) :=
    ((heatKernel r hr hr0 t ∘ₖ heatKernel r hr hr0 s) x).toProbabilityMeasure
  let ν : ProbabilityMeasure (UnitAddTorus (Fin 3)) :=
    (heatKernel r hr hr0 (s+t) x).toProbabilityMeasure
  have hμν : μ = ν := by
    apply measure_eq_of_fourier_moments
    intro k
    have hchar (l : Wave) :
        (∫ z, UnitAddTorus.mFourier (-l) z
          ∂(heatKernel r hr hr0 t ∘ₖ heatKernel r hr hr0 s) x) =
        (∫ z, UnitAddTorus.mFourier (-l) z
          ∂heatKernel r hr hr0 (s+t) x) := by
      calc
      _ = ∫ y, ∫ z, UnitAddTorus.mFourier (-l) z
            ∂heatKernel r hr hr0 t y ∂heatKernel r hr hr0 s x := by
          apply Kernel.integral_comp
          exact (UnitAddTorus.mFourier (-l)).continuous.integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
      _ = ∫ y, UnitAddTorus.mFourier (-l) y *
            (Real.exp (-((t : ℝ) * (r l : ℝ))) : ℂ)
            ∂heatKernel r hr hr0 s x := by simp_rw [heatKernel_character]
      _ = (∫ y, UnitAddTorus.mFourier (-l) y ∂heatKernel r hr hr0 s x) *
            (Real.exp (-((t : ℝ) * (r l : ℝ))) : ℂ) := by
          rw [integral_mul_const]
      _ = UnitAddTorus.mFourier (-l) x *
            (Real.exp (-((s : ℝ) * (r l : ℝ))) : ℂ) *
            (Real.exp (-((t : ℝ) * (r l : ℝ))) : ℂ) := by
          rw [heatKernel_character]
      _ = UnitAddTorus.mFourier (-l) x *
            (Real.exp (-(((s+t) : ℝ) * (r l : ℝ))) : ℂ) := by
          push_cast
          rw [mul_assoc, ← Complex.exp_add]
          congr 1
          ring_nf
      _ = ∫ z, UnitAddTorus.mFourier (-l) z
            ∂heatKernel r hr hr0 (s+t) x := by
          simp only [heatKernel_character, NNReal.coe_add]
    simpa only [μ, ν, Measure.coe_toProbabilityMeasure, neg_neg] using hchar (-k)
  exact congrArg (fun q : ProbabilityMeasure (UnitAddTorus (Fin 3)) =>
    (q : Measure (UnitAddTorus (Fin 3)))) hμν

theorem heatKernel_zero (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) :
    heatKernel r hr hr0 0 = Kernel.id := by
  ext x
  rw [heatKernel_apply, heatLaw_zero, Kernel.id_apply]
  simp

end OperatorDerivativeRewrite.Foundation.PhysicalHeatKernel
