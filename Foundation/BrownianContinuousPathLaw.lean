import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-! Uniqueness of the actual continuous Brownian path law from the already
verified finite-dimensional Brownian laws. No path-space law is postulated. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianContinuousPathLaw
set_option backward.isDefEq.respectTransparency false

theorem function_projective {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (X t)) (hB : IsPreBrownianReal X μ) :
    IsProjectiveLimit (μ.map (fun ω t => X t ω)) BrownianReal.projectiveFamily := by
  intro I
  have hr : Measurable (I.restrict : (ℝ≥0 → ℝ) → (I → ℝ)) :=
    Measurable.of_eval (fun i : I => measurable_pi_apply (i : ℝ≥0))
  rw [Measure.map_map hr (Measurable.of_eval hm)]
  exact (hB.hasLaw I).map_eq

theorem function_law_unique {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') (X : ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Ω' → ℝ)
    (hX : ∀ t, Measurable (X t)) (hY : ∀ t, Measurable (Y t))
    (hBX : IsPreBrownianReal X μ) (hBY : IsPreBrownianReal Y ν) :
    μ.map (fun ω t => X t ω) = ν.map (fun ω t => Y t ω) :=
  (function_projective μ X hX hBX).unique (function_projective ν Y hY hBY)

theorem path_observation_eq {Ω : Type*} (p : Ω → C(ℝ≥0, ℝ)) :
    MeasurableSpace.comap p inferInstance =
      MeasurableSpace.comap (fun ω t => p ω t) inferInstance := by
  rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval]
  simp only [MeasurableSpace.comap_iSup,MeasurableSpace.comap_comp,
    MeasurableSpace.comap_process_pi,Function.comp_def]

theorem path_space_eq : (inferInstance : MeasurableSpace C(ℝ≥0, ℝ)) =
    MeasurableSpace.comap (fun p : C(ℝ≥0, ℝ) => (p : ℝ≥0 → ℝ)) inferInstance := by
  simpa only [MeasurableSpace.comap_id,id_eq] using path_observation_eq (id : C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ))

theorem evaluation_measurable :
    Measurable (fun p : C(ℝ≥0, ℝ) => (p : ℝ≥0 → ℝ)) :=
  Measurable.of_eval (fun t => ContinuousMap.measurable_eval t)

theorem continuous_measure_ext (μ ν : Measure C(ℝ≥0, ℝ))
    (h : μ.map (fun p : C(ℝ≥0, ℝ) => (p : ℝ≥0 → ℝ)) =
      ν.map (fun p : C(ℝ≥0, ℝ) => (p : ℝ≥0 → ℝ))) : μ = ν := by
  ext A hA
  have hA' := path_space_eq.le A hA
  obtain ⟨B,hB,rfl⟩ := hA'
  have he := congrArg (fun ξ : Measure (ℝ≥0 → ℝ) => ξ B) h
  simpa only [Measure.map_apply evaluation_measurable hB] using he

theorem path_law_unique {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') (p : Ω → C(ℝ≥0, ℝ)) (q : Ω' → C(ℝ≥0, ℝ))
    (hp : Measurable p) (hq : Measurable q)
    (hBp : IsPreBrownianReal (fun t ω => p ω t) μ)
    (hBq : IsPreBrownianReal (fun t ω => q ω t) ν) : μ.map p = ν.map q := by
  apply continuous_measure_ext
  rw [Measure.map_map evaluation_measurable hp,Measure.map_map evaluation_measurable hq]
  exact function_law_unique μ ν _ _
    (fun t => (ContinuousMap.measurable_eval t).comp hp)
    (fun t => (ContinuousMap.measurable_eval t).comp hq) hBp hBq

end OperatorDerivativeRewrite.Foundation.BrownianContinuousPathLaw
