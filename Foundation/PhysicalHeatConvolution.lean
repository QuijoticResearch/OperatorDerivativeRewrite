import Foundation.PhysicalHeatLawUnique
import Mathlib.MeasureTheory.Group.IntegralConvolution

/-!
# Convolution semigroup of physical heat probability laws

Fourier characters multiply under torus addition. The actual probability
laws from `PhysicalHeatLawUnique` therefore have multiplicative character
moments under measure convolution. Fourier uniqueness identifies this
convolution with the law at summed time. The time-zero law is `dirac 0`.
This is a measure semigroup; no stochastic process or path regularity is
inferred here.
-/

open OperatorDerivativeRewrite.Foundation
open FiniteFourierDifferentialTrace FourierCovarianceCriterion
open PhysicalHeatLawUnique
open MeasureTheory AddCircle
open scoped NNReal MeasureTheory

noncomputable section

namespace OperatorDerivativeRewrite.Foundation.PhysicalHeatConvolution

private theorem character_add (k : Wave) (x y : UnitAddTorus (Fin 3)) :
    UnitAddTorus.mFourier k (x + y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier k y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply,
    fourier_apply, zsmul_add, toCircle_add, Circle.coe_mul,
    Finset.prod_mul_distrib]

private theorem character_integrable (k : Wave)
    (μ : Measure (UnitAddTorus (Fin 3))) [IsFiniteMeasure μ] :
    Integrable (fun x => UnitAddTorus.mFourier k x) μ :=
  (UnitAddTorus.mFourier k).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem character_convolution (k : Wave)
    (μ ν : ProbabilityMeasure (UnitAddTorus (Fin 3))) :
    (∫ z, UnitAddTorus.mFourier k z
      ∂((μ : Measure (UnitAddTorus (Fin 3))) ∗ (ν : Measure (UnitAddTorus (Fin 3))))) =
    (∫ x, UnitAddTorus.mFourier k x ∂(μ : Measure (UnitAddTorus (Fin 3)))) *
    (∫ y, UnitAddTorus.mFourier k y ∂(ν : Measure (UnitAddTorus (Fin 3)))) := by
  rw [integral_conv (character_integrable k _)]
  simp_rw [character_add]
  simp only [integral_mul_const, integral_const_mul]

def heatLaw (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (t : ℝ≥0) :
    ProbabilityMeasure (UnitAddTorus (Fin 3)) :=
  Classical.choose (exists_unique_physical_heat_law r hr hr0 t)

theorem heatLaw_character (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (t : ℝ≥0) (k : Wave) :
    (∫ x, UnitAddTorus.mFourier (-k) x
      ∂(heatLaw r hr hr0 t : Measure (UnitAddTorus (Fin 3)))) =
        (Real.exp (-((t : ℝ) * (r k : ℝ))) : ℂ) :=
  (Classical.choose_spec (exists_unique_physical_heat_law r hr hr0 t)).1 k

theorem heatLaw_conv (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (s t : ℝ≥0) :
    ((heatLaw r hr hr0 s : Measure (UnitAddTorus (Fin 3))) ∗
      (heatLaw r hr hr0 t : Measure (UnitAddTorus (Fin 3)))) =
    (heatLaw r hr hr0 (s+t) : Measure (UnitAddTorus (Fin 3))) := by
  let μ : ProbabilityMeasure (UnitAddTorus (Fin 3)) :=
    (((heatLaw r hr hr0 s : Measure (UnitAddTorus (Fin 3))) ∗
      (heatLaw r hr hr0 t : Measure (UnitAddTorus (Fin 3)))).toProbabilityMeasure)
  have hμ : ∀ k : Wave,
      (∫ x, UnitAddTorus.mFourier (-k) x ∂(μ : Measure (UnitAddTorus (Fin 3)))) =
        (Real.exp (-(((s+t) : ℝ) * (r k : ℝ))) : ℂ) := by
    intro k
    change (∫ x, UnitAddTorus.mFourier (-k) x
      ∂((heatLaw r hr hr0 s : Measure (UnitAddTorus (Fin 3))) ∗
        (heatLaw r hr hr0 t : Measure (UnitAddTorus (Fin 3))))) = _
    rw [character_convolution, heatLaw_character, heatLaw_character]
    push_cast
    rw [← Complex.exp_add]
    congr 1
    ring
  have h := physical_heat_law_unique r (s+t) μ (heatLaw r hr hr0 (s+t)) hμ
    (heatLaw_character r hr hr0 (s+t))
  exact congrArg (fun q : ProbabilityMeasure (UnitAddTorus (Fin 3)) =>
    (q : Measure (UnitAddTorus (Fin 3)))) h

theorem heatLaw_zero (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) :
    (heatLaw r hr hr0 0 : Measure (UnitAddTorus (Fin 3))) = Measure.dirac 0 := by
  let δ : ProbabilityMeasure (UnitAddTorus (Fin 3)) :=
    (Measure.dirac (0 : UnitAddTorus (Fin 3))).toProbabilityMeasure
  have hδ : ∀ k : Wave,
      (∫ x, UnitAddTorus.mFourier (-k) x ∂(δ : Measure (UnitAddTorus (Fin 3)))) =
        (Real.exp (-((0 : ℝ) * (r k : ℝ))) : ℂ) := by
    intro k
    simp [δ, UnitAddTorus.mFourier]
  have h := physical_heat_law_unique r 0 (heatLaw r hr hr0 0) δ
    (heatLaw_character r hr hr0 0) hδ
  exact congrArg (fun q : ProbabilityMeasure (UnitAddTorus (Fin 3)) =>
    (q : Measure (UnitAddTorus (Fin 3)))) h

end OperatorDerivativeRewrite.Foundation.PhysicalHeatConvolution
