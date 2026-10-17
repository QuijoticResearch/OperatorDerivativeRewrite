import Foundation.SchwartzBoundedCylinders
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-! A genuine bounded continuous occupation functional on continuous paths, formed pointwise. -/
noncomputable section
open MeasureTheory Filter
open scoped BoundedContinuousFunction SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.BoundedPathOccupation

variable (μ : Measure ℝ) [IsFiniteMeasure μ]

theorem integrable_evaluation (f : ℝ →ᵇ ℝ) (ω : C(ℝ,ℝ)) :
    Integrable (fun t => f (ω t)) μ := by
  apply Integrable.of_bound (f.continuous.comp ω.continuous).aestronglyMeasurable ‖f‖
  exact Eventually.of_forall (fun t => f.norm_coe_le_norm _)

theorem occupation_continuous (f : ℝ →ᵇ ℝ) :
    Continuous (fun ω : C(ℝ,ℝ) => ∫ t, f (ω t) ∂μ) := by
  apply continuous_of_dominated
    (bound := fun _ => ‖f‖)
  · intro ω
    exact (integrable_evaluation μ f ω).aestronglyMeasurable
  · intro ω
    exact Eventually.of_forall (fun t => f.norm_coe_le_norm _)
  · exact integrable_const _
  · exact Eventually.of_forall (fun t => f.continuous.comp (continuous_eval_const t))

def boundedOccupation (f : ℝ →ᵇ ℝ) : C(ℝ,ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun ω => ∫ t, f (ω t) ∂μ)
    (occupation_continuous μ f) (‖f‖*μ.real Set.univ)
    (fun ω => norm_integral_le_of_norm_le_const
      (Eventually.of_forall (fun t => f.norm_coe_le_norm (ω t))))

theorem boundedOccupation_apply (f : ℝ →ᵇ ℝ) (ω : C(ℝ,ℝ)) :
    boundedOccupation μ f ω = ∫ t, f (ω t) ∂μ := rfl

theorem boundedOccupation_bound (f : ℝ →ᵇ ℝ) :
    ‖boundedOccupation μ f‖ ≤ ‖f‖*μ.real Set.univ :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by positivity) _

def occupation : (ℝ →ᵇ ℝ) →L[ℝ] (C(ℝ,ℝ) →ᵇ ℝ) :=
  LinearMap.mkContinuous
    { toFun := boundedOccupation μ
      map_add' := by
        intro f g
        ext ω
        exact integral_add (integrable_evaluation μ f ω) (integrable_evaluation μ g ω)
      map_smul' := by
        intro c f
        ext ω
        exact integral_smul c (fun t => f (ω t)) }
    (μ.real Set.univ) (fun f => by
      change ‖boundedOccupation μ f‖ ≤ μ.real Set.univ * ‖f‖
      simpa only [mul_comm] using boundedOccupation_bound μ f)

theorem occupation_apply (f : ℝ →ᵇ ℝ) (ω : C(ℝ,ℝ)) :
    occupation μ f ω = ∫ t, f (ω t) ∂μ := rfl

theorem occupation_norm : ‖occupation μ‖ ≤ μ.real Set.univ := by
  apply (occupation μ).opNorm_le_bound ENNReal.toReal_nonneg
  intro f
  change ‖boundedOccupation μ f‖ ≤ μ.real Set.univ * ‖f‖
  simpa only [mul_comm] using boundedOccupation_bound μ f

def schwartzOccupation : 𝓢(ℝ,ℝ) →L[ℝ] (C(ℝ,ℝ) →ᵇ ℝ) :=
  (occupation μ).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℝ ℝ ℝ)

theorem schwartzOccupation_apply (g : 𝓢(ℝ,ℝ)) (ω : C(ℝ,ℝ)) :
    schwartzOccupation μ g ω = ∫ t, g (ω t) ∂μ := rfl

theorem schwartzOccupation_bound (g : 𝓢(ℝ,ℝ)) :
    ‖schwartzOccupation μ g‖ ≤ μ.real Set.univ * SchwartzMap.seminorm ℝ 0 0 g := by
  apply (boundedOccupation_bound μ g.toBoundedContinuousFunction).trans
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left g.norm_toBoundedContinuousFunction_le ENNReal.toReal_nonneg

theorem occupation_integrable (ν : Measure C(ℝ,ℝ)) [IsFiniteMeasure ν] (f : ℝ →ᵇ ℝ) :
    Integrable (fun ω => ∫ t, f (ω t) ∂μ) ν :=
  (boundedOccupation μ f).integrable (μ := ν)

theorem occupation_fubini (ν : Measure C(ℝ,ℝ)) [IsFiniteMeasure ν] (f : ℝ →ᵇ ℝ) :
    (∫ ω, (∫ t, f (ω t) ∂μ) ∂ν) = ∫ t, (∫ ω, f (ω t) ∂ν) ∂μ := by
  apply integral_integral_swap
  apply Integrable.of_bound (f.continuous.comp continuous_eval).aestronglyMeasurable ‖f‖
  exact Eventually.of_forall (fun p => f.norm_coe_le_norm _)

end OperatorDerivativeRewrite.Foundation.BoundedPathOccupation
