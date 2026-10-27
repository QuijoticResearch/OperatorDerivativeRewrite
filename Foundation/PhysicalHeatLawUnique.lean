import Foundation.PhysicalHeatFiniteBox
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt

/-!
# Fourier uniqueness for physical torus heat laws

Complex Fourier characters separate probability measures on the compact torus.
Their span is uniformly dense by Stone--Weierstrass. Integration against a
probability measure is a bounded complex linear functional, so equality of
character moments extends to every continuous function and then to measures.
This selects a unique measure for each covariance-symbol heat multiplier.
It does not construct a convolution law or stochastic process.
-/

open OperatorDerivativeRewrite.Foundation
open FourierCovarianceCriterion
open FiniteFourierDifferentialTrace
open MeasureTheory
open AddCircle
open scoped NNReal

noncomputable section

namespace OperatorDerivativeRewrite.Foundation.PhysicalHeatLawUnique

private def torusIntegral (μ : ProbabilityMeasure (UnitAddTorus (Fin 3))) :
    C(UnitAddTorus (Fin 3), ℂ) →L[ℂ] ℂ := by
  let L : C(UnitAddTorus (Fin 3), ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun f => ∫ x, f x ∂(μ : Measure (UnitAddTorus (Fin 3)))
        map_add' := by
          intro f g
          exact integral_add' (f.continuous.integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _))
            (g.continuous.integrable_of_hasCompactSupport
              (HasCompactSupport.of_compactSpace _))
        map_smul' := by
          intro c f
          exact integral_smul c _ }
  exact L.mkContinuous 1 (by
    intro f
    change ‖∫ x, f x ∂(μ : Measure (UnitAddTorus (Fin 3)))‖ ≤ 1 * ‖f‖
    have h := norm_integral_le_of_norm_le_const
      (μ := (μ : Measure (UnitAddTorus (Fin 3))))
      (C := ‖f‖) (Filter.Eventually.of_forall (fun x => ContinuousMap.norm_coe_le_norm f x))
    simpa using h)

theorem measure_eq_of_fourier_moments
    (μ ν : ProbabilityMeasure (UnitAddTorus (Fin 3)))
    (h : ∀ k : Fin 3 → ℤ,
      (∫ x, UnitAddTorus.mFourier k x ∂(μ : Measure (UnitAddTorus (Fin 3)))) =
      (∫ x, UnitAddTorus.mFourier k x ∂(ν : Measure (UnitAddTorus (Fin 3))))) :
    μ = ν := by
  let S : Submodule ℂ C(UnitAddTorus (Fin 3), ℂ) :=
    Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := Fin 3)))
  let F := torusIntegral μ
  let G := torusIntegral ν
  have hS : ∀ f ∈ S, F f = G f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        exact h k
    | zero => simp
    | add x y hx hy ihx ihy => simpa only [map_add] using congrArg₂ (· + ·) ihx ihy
    | smul c x hx ih => simpa only [map_smul] using congrArg (c • ·) ih
  have hdense : Dense (S : Set C(UnitAddTorus (Fin 3), ℂ)) := by
    apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
    exact UnitAddTorus.span_mFourier_closure_eq_top
  have hfg : F = G := by
    apply ContinuousLinearMap.ext
    intro f
    have hclosed : IsClosed {x | F x = G x} := isClosed_eq F.continuous G.continuous
    have hall := closure_minimal (fun x hx => hS x hx) hclosed
    exact hall (hdense.closure_eq.symm ▸ Set.mem_univ f)
  apply ProbabilityMeasure.toMeasure_injective
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let fc : C(UnitAddTorus (Fin 3), ℂ) :=
    ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hf := congrArg (fun H : C(UnitAddTorus (Fin 3), ℂ) →L[ℂ] ℂ => H fc) hfg
  change (∫ x, (f x : ℂ) ∂(μ : Measure (UnitAddTorus (Fin 3)))) =
    (∫ x, (f x : ℂ) ∂(ν : Measure (UnitAddTorus (Fin 3)))) at hf
  let zμ : ℝ := ∫ x, f x ∂(μ : Measure (UnitAddTorus (Fin 3)))
  let zν : ℝ := ∫ x, f x ∂(ν : Measure (UnitAddTorus (Fin 3)))
  have hμ : (∫ x, (f x : ℂ) ∂(μ : Measure (UnitAddTorus (Fin 3)))) =
      (zμ : ℂ) := integral_ofReal
  have hν : (∫ x, (f x : ℂ) ∂(ν : Measure (UnitAddTorus (Fin 3)))) =
      (zν : ℂ) := integral_ofReal
  rw [hμ, hν] at hf
  exact Complex.ofReal_injective hf

theorem physical_heat_law_unique (r : Wave → ℝ≥0)
    (t : ℝ≥0)
    (μ ν : ProbabilityMeasure (UnitAddTorus (Fin 3)))
    (hμ : ∀ k : Wave,
      (∫ x, UnitAddTorus.mFourier (-k) x ∂(μ : Measure (UnitAddTorus (Fin 3)))) =
        (Real.exp (-((t : ℝ) * (r k : ℝ))) : ℂ))
    (hν : ∀ k : Wave,
      (∫ x, UnitAddTorus.mFourier (-k) x ∂(ν : Measure (UnitAddTorus (Fin 3)))) =
        (Real.exp (-((t : ℝ) * (r k : ℝ))) : ℂ)) :
    μ = ν := by
  apply measure_eq_of_fourier_moments
  intro k
  simpa only [neg_neg] using (hμ (-k)).trans (hν (-k)).symm

theorem exists_unique_physical_heat_law (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (t : ℝ≥0) :
    ∃! μ : ProbabilityMeasure (UnitAddTorus (Fin 3)),
      ∀ k : Wave,
        (∫ x, UnitAddTorus.mFourier (-k) x ∂(μ : Measure (UnitAddTorus (Fin 3)))) =
          (Real.exp (-((t : ℝ) * (r k : ℝ))) : ℂ) := by
  obtain ⟨μ, hμ⟩ := PhysicalHeatFiniteBox.exists_physical_heat_law r hr hr0 t
  exact ⟨μ, hμ, fun ν hν => physical_heat_law_unique r t ν μ hν hμ⟩

end OperatorDerivativeRewrite.Foundation.PhysicalHeatLawUnique
