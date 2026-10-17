import Foundation.CorridorClassification
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.UniformConvergence

/-! A vanishing uniform shift detects exactly the relevant classifier boundary. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.CorridorBoundarySharpness
open CorridorClassification
set_option backward.isDefEq.respectTransparency false

def step (n : ℕ) : ℝ := 1/((n:ℝ)+1)
theorem step_pos (n : ℕ) : 0<step n := by unfold step; positivity
theorem step_tendsto_zero : Tendsto step atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

def down {α : Type*} (f : α → ℝ) (n : ℕ) (x : α) : ℝ := f x-step n

theorem down_measurable {α : Type*} [MeasurableSpace α] {f : α → ℝ}
    (hf : Measurable f) (n : ℕ) : Measurable (down f n) := hf.sub measurable_const

theorem down_tendsto {α : Type*} (f : α → ℝ) (x : α) :
    Tendsto (fun n => down f n x) atTop (𝓝 (f x)) := by
  simpa only [down, sub_zero] using (tendsto_const_nhds.sub step_tendsto_zero :
    Tendsto (fun n => f x-step n) atTop (𝓝 (f x-0)))

theorem down_uniform {α : Type*} (f : α → ℝ) : TendstoUniformly (down f) f atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [step_tendsto_zero.eventually (eventually_lt_nhds hε)] with n hn x
  have he : |f x-(f x-step n)|=step n := by
    rw [show f x-(f x-step n)=step n by ring, abs_of_pos (step_pos n)]
  simpa only [Real.dist_eq, down, he] using hn

def disagreement {α : Type*} (ρ ω ρ' ω' : α → ℝ) (a b : ℝ) : Set α :=
  {x | label (ρ' x) (ω' x) a b≠label (ρ x) (ω x) a b}

def disagreementMass {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (ρ ω ρ' ω' : α → ℝ) (a b : ℝ) : ℝ := μ.real (disagreement ρ ω ρ' ω' a b)

def disagreementIndicator {α : Type*} (ρ ω ρ' ω' : α → ℝ) (a b : ℝ) : α → ℝ :=
  (disagreement ρ ω ρ' ω' a b).indicator (1 : α → ℝ)

def boundaryIndicator {α : Type*} (ρ ω : α → ℝ) (a b : ℝ) : α → ℝ :=
  (relevantBoundary ρ ω a b).indicator (1 : α → ℝ)

theorem disagreement_measurable {α : Type*} [MeasurableSpace α] {ρ ω ρ' ω' : α → ℝ}
    (hr : Measurable ρ) (hl : Measurable ω) (hr' : Measurable ρ') (hl' : Measurable ω')
    (a b : ℝ) : MeasurableSet (disagreement ρ ω ρ' ω' a b) :=
  (measurableSet_eq_fun (label_measurable hr' hl' a b) (label_measurable hr hl a b)).compl

theorem boundary_measurable {α : Type*} [MeasurableSpace α] {ρ ω : α → ℝ}
    (hr : Measurable ρ) (hl : Measurable ω) (a b : ℝ) :
    MeasurableSet (relevantBoundary ρ ω a b) :=
  (measurableSet_eq_fun hr measurable_const).union
    ((measurableSet_le measurable_const hr).inter (measurableSet_eq_fun hl measurable_const))

theorem disagreementIndicator_integrable {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {ρ ω ρ' ω' : α → ℝ}
    (hr : Measurable ρ) (hl : Measurable ω) (hr' : Measurable ρ') (hl' : Measurable ω')
    (a b : ℝ) : Integrable (disagreementIndicator ρ ω ρ' ω' a b) μ :=
  (integrable_const 1).indicator (disagreement_measurable hr hl hr' hl' a b)

theorem disagreementIndicator_norm_le {α : Type*} (ρ ω ρ' ω' : α → ℝ) (a b : ℝ) (x : α) :
    ‖disagreementIndicator ρ ω ρ' ω' a b x‖≤1 := by
  classical
  by_cases hx : x∈disagreement ρ ω ρ' ω' a b <;> simp [disagreementIndicator, hx]

theorem integral_disagreementIndicator {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {ρ ω ρ' ω' : α → ℝ} (hr : Measurable ρ) (hl : Measurable ω)
    (hr' : Measurable ρ') (hl' : Measurable ω') (a b : ℝ) :
    (∫ x, disagreementIndicator ρ ω ρ' ω' a b x ∂μ)=disagreementMass μ ρ ω ρ' ω' a b :=
  integral_indicator_one (disagreement_measurable hr hl hr' hl' a b)

theorem integral_boundaryIndicator {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {ρ ω : α → ℝ} (hr : Measurable ρ) (hl : Measurable ω) (a b : ℝ) :
    (∫ x, boundaryIndicator ρ ω a b x ∂μ)=μ.real (relevantBoundary ρ ω a b) :=
  integral_indicator_one (boundary_measurable hr hl a b)

theorem down_label_ne_on_boundary (r l a b : ℝ)
    (hb : r=a ∨ (a≤r ∧ l=b)) :
    ∀ᶠ n in atTop, label (r-step n) (l-step n) a b≠label r l a b := by
  rcases hb with hr | ⟨hr, hl⟩
  · subst r
    apply Filter.Eventually.of_forall
    intro n
    have hnew : a-step n<a := by linarith [step_pos n]
    by_cases hw : l<b <;> simp [label, hnew, hw]
  · subst l
    by_cases he : r=a
    · subst r
      apply Filter.Eventually.of_forall
      intro n
      have hnew : a-step n<a := by linarith [step_pos n]
      simp [label, hnew]
    · have hgap : 0<r-a := sub_pos.mpr (lt_of_le_of_ne hr (Ne.symm he))
      filter_upwards [step_tendsto_zero.eventually (eventually_lt_nhds hgap)] with n hn
      have hnew : ¬r-step n<a := by linarith
      have hfreq : b-step n<b := by linarith [step_pos n]
      simp [label, hnew, hfreq, not_lt.mpr hr]

theorem down_indicator_tendsto {α : Type*} (ρ ω : α → ℝ) (a b : ℝ) (x : α) :
    Tendsto (fun n => disagreementIndicator ρ ω (down ρ n) (down ω n) a b x) atTop
      (𝓝 (boundaryIndicator ρ ω a b x)) := by
  classical
  by_cases hb : x∈relevantBoundary ρ ω a b
  · have he := down_label_ne_on_boundary (ρ x) (ω x) a b hb
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hn
    simp [disagreementIndicator, disagreement, boundaryIndicator, down, hn, hb]
  · have hr : ρ x≠a := fun h => hb (Or.inl h)
    have hrel : ρ x<a ∨ ω x≠b := by
      by_cases hρ : ρ x<a
      · exact Or.inl hρ
      · exact Or.inr (fun hw => hb (Or.inr ⟨le_of_not_gt hρ, hw⟩))
    have he := label_eventually_eq a b (down_tendsto ρ x) (fun _ => down_tendsto ω x) hr hrel
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hn
    simp [disagreementIndicator, disagreement, boundaryIndicator, hn, hb]

theorem down_disagreement_limit {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (ρ ω : α → ℝ) (hr : Measurable ρ) (hl : Measurable ω) (a b : ℝ) :
    Tendsto (fun n => disagreementMass μ ρ ω (down ρ n) (down ω n) a b) atTop
      (𝓝 (μ.real (relevantBoundary ρ ω a b))) := by
  have hi := tendsto_integral_of_dominated_convergence (fun _ : α => (1:ℝ))
    (fun n => (disagreementIndicator_integrable μ hr hl (down_measurable hr n)
      (down_measurable hl n) a b).aestronglyMeasurable) (integrable_const 1)
    (fun n => Filter.Eventually.of_forall
      (disagreementIndicator_norm_le ρ ω (down ρ n) (down ω n) a b))
    (Filter.Eventually.of_forall (down_indicator_tendsto ρ ω a b))
  simp only [integral_disagreementIndicator μ hr hl (down_measurable hr _) (down_measurable hl _) a b,
    integral_boundaryIndicator μ hr hl a b] at hi
  exact hi

theorem disagreement_tendsto_zero {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (ρ ω : α → ℝ) (ρₙ ωₙ : ℕ → α → ℝ) (a b : ℝ)
    (hr : Measurable ρ) (hl : Measurable ω)
    (hrn : ∀ n, Measurable (ρₙ n)) (hln : ∀ n, Measurable (ωₙ n))
    (hρlim : ∀ᵐ x ∂μ, Tendsto (fun n => ρₙ n x) atTop (𝓝 (ρ x)))
    (hωlim : ∀ᵐ x ∂μ, Tendsto (fun n => ωₙ n x) atTop (𝓝 (ω x)))
    (hb : μ (relevantBoundary ρ ω a b)=0) :
    Tendsto (fun n => disagreementMass μ ρ ω (ρₙ n) (ωₙ n) a b) atTop (𝓝 0) := by
  classical
  have hne : ∀ᵐ x ∂μ, x∉relevantBoundary ρ ω a b := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using hb
  have hc : ∀ᵐ x ∂μ, Tendsto
      (fun n => disagreementIndicator ρ ω (ρₙ n) (ωₙ n) a b x) atTop (𝓝 (0:ℝ)) := by
    filter_upwards [hρlim, hωlim, hne] with x hx hy hn
    have hrel : ρ x<a ∨ ω x≠b := by
      by_cases hh : ρ x<a
      · exact Or.inl hh
      · exact Or.inr (fun hw => hn (Or.inr ⟨le_of_not_gt hh, hw⟩))
    have he := label_eventually_eq a b hx (fun _ => hy) (fun h => hn (Or.inl h)) hrel
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n he
    simp [disagreementIndicator, disagreement, he]
  have hi := tendsto_integral_of_dominated_convergence (fun _ : α => (1:ℝ))
    (fun n => (disagreementIndicator_integrable μ hr hl (hrn n) (hln n) a b).aestronglyMeasurable)
    (integrable_const 1)
    (fun n => Filter.Eventually.of_forall (disagreementIndicator_norm_le ρ ω (ρₙ n) (ωₙ n) a b)) hc
  simp only [integral_disagreementIndicator μ hr hl (hrn _) (hln _) a b, integral_zero] at hi
  exact hi

def UniformlyStable {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (ρ ω : α → ℝ) (a b : ℝ) : Prop :=
  ∀ (ρₙ ωₙ : ℕ → α → ℝ), (∀ n, Measurable (ρₙ n)) → (∀ n, Measurable (ωₙ n)) →
    TendstoUniformly ρₙ ρ atTop → TendstoUniformly ωₙ ω atTop →
      Tendsto (fun n => disagreementMass μ ρ ω (ρₙ n) (ωₙ n) a b) atTop (𝓝 0)

theorem uniformlyStable_iff_boundary_null {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (ρ ω : α → ℝ) (hr : Measurable ρ) (hl : Measurable ω) (a b : ℝ) :
    UniformlyStable μ ρ ω a b ↔ μ (relevantBoundary ρ ω a b)=0 := by
  constructor
  · intro hs
    have hzero := hs (down ρ) (down ω) (down_measurable hr) (down_measurable hl)
      (down_uniform ρ) (down_uniform ω)
    have hh : μ.real (relevantBoundary ρ ω a b)=0 :=
      tendsto_nhds_unique (down_disagreement_limit μ ρ ω hr hl a b) hzero
    exact (measureReal_eq_zero_iff (measure_ne_top μ _)).mp hh
  · intro hb ρₙ ωₙ hrn hln hρlim hωlim
    exact disagreement_tendsto_zero μ ρ ω ρₙ ωₙ a b hr hl hrn hln
      (Filter.Eventually.of_forall hρlim.tendsto_at)
      (Filter.Eventually.of_forall hωlim.tendsto_at) hb

end OperatorDerivativeRewrite.Foundation.CorridorBoundarySharpness
