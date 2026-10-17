import Foundation.CorridorBoundarySharpness
import Mathlib.Tactic.FinCases

/-! Monotone shifts make the null-boundary criterion sharp for occupation totals too. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.CorridorOccupationSharpness
open CorridorClassification CorridorBoundarySharpness
set_option backward.isDefEq.respectTransparency false

theorem label_mono_coordinates {r l r' l' a b : ℝ} (hr : r≤r') (hl : l≤l') :
    label r l a b≤label r' l' a b := by
  by_cases hρ : r<a
  · simp [label, hρ]
  · have hρ' : ¬r'<a := by linarith
    by_cases hω : l<b
    · by_cases hω' : l'<b <;> norm_num [label, hρ, hρ', hω, hω']
    · have hω' : ¬l'<b := by linarith
      simp [label, hρ, hρ', hω, hω']

theorem down_label_le (r l a b : ℝ) (n : ℕ) :
    label (r-step n) (l-step n) a b≤label r l a b :=
  label_mono_coordinates (sub_le_self _ (step_pos n).le) (sub_le_self _ (step_pos n).le)

theorem endpoint_indicator_bound (old new : Fin 3) (hm : new≤old) :
    (if new≠old then (1:ℝ) else 0)≤
      ((if new=0 then 1 else 0)-(if old=0 then 1 else 0))+
        ((if old=2 then 1 else 0)-(if new=2 then 1 else 0)) := by
  fin_cases old <;> fin_cases new <;> norm_num at *

def endpointChange {α : Type*} (ρ ω ρ' ω' : α → ℝ) (a b : ℝ) (x : α) : ℝ :=
  (caseIndicator ρ' ω' a b 0 x-caseIndicator ρ ω a b 0 x)+
    (caseIndicator ρ ω a b 2 x-caseIndicator ρ' ω' a b 2 x)

theorem monotone_indicator_bound {α : Type*} (ρ ω ρ' ω' : α → ℝ) (a b : ℝ)
    (hm : ∀ x, label (ρ' x) (ω' x) a b≤label (ρ x) (ω x) a b) (x : α) :
    disagreementIndicator ρ ω ρ' ω' a b x≤endpointChange ρ ω ρ' ω' a b x := by
  classical
  simpa only [disagreementIndicator, disagreement, endpointChange, caseIndicator, region,
    Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply] using
    endpoint_indicator_bound (label (ρ x) (ω x) a b) (label (ρ' x) (ω' x) a b) (hm x)

theorem endpointChange_integrable {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {ρ ω ρ' ω' : α → ℝ} (hr : Measurable ρ) (hl : Measurable ω)
    (hr' : Measurable ρ') (hl' : Measurable ω') (a b : ℝ) :
    Integrable (endpointChange ρ ω ρ' ω' a b) μ :=
  ((caseIndicator_integrable μ hr' hl' a b 0).sub (caseIndicator_integrable μ hr hl a b 0)).add
    ((caseIndicator_integrable μ hr hl a b 2).sub (caseIndicator_integrable μ hr' hl' a b 2))

theorem integral_endpointChange {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {ρ ω ρ' ω' : α → ℝ} (hr : Measurable ρ) (hl : Measurable ω)
    (hr' : Measurable ρ') (hl' : Measurable ω') (a b : ℝ) :
    (∫ x, endpointChange ρ ω ρ' ω' a b x ∂μ)=
      (caseOccupation μ ρ' ω' a b 0-caseOccupation μ ρ ω a b 0)+
        (caseOccupation μ ρ ω a b 2-caseOccupation μ ρ' ω' a b 2) := by
  have hz : Integrable (fun x => caseIndicator ρ' ω' a b 0 x-caseIndicator ρ ω a b 0 x) μ :=
    (caseIndicator_integrable μ hr' hl' a b 0).sub (caseIndicator_integrable μ hr hl a b 0)
  have ht : Integrable (fun x => caseIndicator ρ ω a b 2 x-caseIndicator ρ' ω' a b 2 x) μ :=
    (caseIndicator_integrable μ hr hl a b 2).sub (caseIndicator_integrable μ hr' hl' a b 2)
  change (∫ x, (caseIndicator ρ' ω' a b 0 x-caseIndicator ρ ω a b 0 x)+
    (caseIndicator ρ ω a b 2 x-caseIndicator ρ' ω' a b 2 x) ∂μ)=_
  rw [integral_add hz ht,
    integral_sub (caseIndicator_integrable μ hr' hl' a b 0) (caseIndicator_integrable μ hr hl a b 0),
    integral_sub (caseIndicator_integrable μ hr hl a b 2) (caseIndicator_integrable μ hr' hl' a b 2),
    integral_caseIndicator μ hr' hl' a b 0, integral_caseIndicator μ hr hl a b 0,
    integral_caseIndicator μ hr hl a b 2, integral_caseIndicator μ hr' hl' a b 2]

theorem monotone_disagreement_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (ρ ω ρ' ω' : α → ℝ) (hr : Measurable ρ) (hl : Measurable ω)
    (hr' : Measurable ρ') (hl' : Measurable ω') (a b : ℝ)
    (hm : ∀ x, label (ρ' x) (ω' x) a b≤label (ρ x) (ω x) a b) :
    disagreementMass μ ρ ω ρ' ω' a b≤
      (caseOccupation μ ρ' ω' a b 0-caseOccupation μ ρ ω a b 0)+
        (caseOccupation μ ρ ω a b 2-caseOccupation μ ρ' ω' a b 2) := by
  have hh := integral_mono (disagreementIndicator_integrable μ hr hl hr' hl' a b)
    (endpointChange_integrable μ hr hl hr' hl' a b) (monotone_indicator_bound ρ ω ρ' ω' a b hm)
  rw [integral_disagreementIndicator μ hr hl hr' hl' a b,
    integral_endpointChange μ hr hl hr' hl' a b] at hh
  exact hh

theorem boundary_null_of_down_endpoints {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (ρ ω : α → ℝ) (hr : Measurable ρ) (hl : Measurable ω) (a b : ℝ)
    (hz : Tendsto (fun n => caseOccupation μ (down ρ n) (down ω n) a b 0) atTop
      (𝓝 (caseOccupation μ ρ ω a b 0)))
    (ht : Tendsto (fun n => caseOccupation μ (down ρ n) (down ω n) a b 2) atTop
      (𝓝 (caseOccupation μ ρ ω a b 2))) : μ (relevantBoundary ρ ω a b)=0 := by
  have hcost : Tendsto (fun n =>
      (caseOccupation μ (down ρ n) (down ω n) a b 0-caseOccupation μ ρ ω a b 0)+
        (caseOccupation μ ρ ω a b 2-caseOccupation μ (down ρ n) (down ω n) a b 2))
      atTop (𝓝 (0:ℝ)) := by
    have hzconst : Tendsto (fun _ : ℕ => caseOccupation μ ρ ω a b 0) atTop
        (𝓝 (caseOccupation μ ρ ω a b 0)) := tendsto_const_nhds
    have htconst : Tendsto (fun _ : ℕ => caseOccupation μ ρ ω a b 2) atTop
        (𝓝 (caseOccupation μ ρ ω a b 2)) := tendsto_const_nhds
    simpa only [sub_self, zero_add] using
      (hz.sub hzconst).add (htconst.sub ht)
  have hzero : Tendsto (fun n => disagreementMass μ ρ ω (down ρ n) (down ω n) a b)
      atTop (𝓝 (0:ℝ)) := by
    apply squeeze_zero (fun n => measureReal_nonneg)
      (fun n => monotone_disagreement_bound μ ρ ω (down ρ n) (down ω n) hr hl
        (down_measurable hr n) (down_measurable hl n) a b (fun x => down_label_le _ _ a b n)) hcost
  have hh : μ.real (relevantBoundary ρ ω a b)=0 :=
    tendsto_nhds_unique (down_disagreement_limit μ ρ ω hr hl a b) hzero
  exact (measureReal_eq_zero_iff (measure_ne_top μ _)).mp hh

def UniformOccupationStable {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (ρ ω : α → ℝ) (a b : ℝ) : Prop :=
  ∀ (ρₙ ωₙ : ℕ → α → ℝ), (∀ n, Measurable (ρₙ n)) → (∀ n, Measurable (ωₙ n)) →
    TendstoUniformly ρₙ ρ atTop → TendstoUniformly ωₙ ω atTop →
      ∀ j : Fin 3, Tendsto (fun n => caseOccupation μ (ρₙ n) (ωₙ n) a b j) atTop
        (𝓝 (caseOccupation μ ρ ω a b j))

theorem uniformOccupationStable_iff_boundary_null {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (ρ ω : α → ℝ) (hr : Measurable ρ) (hl : Measurable ω) (a b : ℝ) :
    UniformOccupationStable μ ρ ω a b ↔ μ (relevantBoundary ρ ω a b)=0 := by
  constructor
  · intro hs
    have hh := hs (down ρ) (down ω) (down_measurable hr) (down_measurable hl)
      (down_uniform ρ) (down_uniform ω)
    exact boundary_null_of_down_endpoints μ ρ ω hr hl a b (hh 0) (hh 2)
  · intro hb ρₙ ωₙ hrn hln hρlim hωlim j
    exact caseOccupation_converges_global μ ρ ω ρₙ ωₙ a b j hr hl hrn hln
      (Filter.Eventually.of_forall hρlim.tendsto_at)
      (Filter.Eventually.of_forall hωlim.tendsto_at) hb

theorem occupation_stability_iff_classification_stability {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (ρ ω : α → ℝ) (hr : Measurable ρ) (hl : Measurable ω)
    (a b : ℝ) : UniformOccupationStable μ ρ ω a b ↔ UniformlyStable μ ρ ω a b :=
  (uniformOccupationStable_iff_boundary_null μ ρ ω hr hl a b).trans
    (uniformlyStable_iff_boundary_null μ ρ ω hr hl a b).symm

theorem down_endpoint_test_iff_boundary_null {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (ρ ω : α → ℝ) (hr : Measurable ρ) (hl : Measurable ω) (a b : ℝ) :
    ((Tendsto (fun n => caseOccupation μ (down ρ n) (down ω n) a b 0) atTop
      (𝓝 (caseOccupation μ ρ ω a b 0))) ∧
      (Tendsto (fun n => caseOccupation μ (down ρ n) (down ω n) a b 2) atTop
        (𝓝 (caseOccupation μ ρ ω a b 2)))) ↔ μ (relevantBoundary ρ ω a b)=0 := by
  constructor
  · rintro ⟨hz, ht⟩
    exact boundary_null_of_down_endpoints μ ρ ω hr hl a b hz ht
  · intro hb
    have hs := (uniformOccupationStable_iff_boundary_null μ ρ ω hr hl a b).mpr hb
    have hh := hs (down ρ) (down ω) (down_measurable hr) (down_measurable hl)
      (down_uniform ρ) (down_uniform ω)
    exact ⟨hh 0, hh 2⟩

end OperatorDerivativeRewrite.Foundation.CorridorOccupationSharpness
