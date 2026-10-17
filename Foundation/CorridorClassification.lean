import Foundation.CorridorOccupation

/-! The actual three-case corridor classifier and its relevant threshold boundary. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology symmDiff
namespace OperatorDerivativeRewrite.Foundation.CorridorClassification
open CorridorOccupation
set_option backward.isDefEq.respectTransparency false

def label (ρ ω a b : ℝ) : Fin 3 := if ρ<a then 0 else if ω<b then 1 else 2

theorem label_zero_iff (ρ ω a b : ℝ) : label ρ ω a b=0 ↔ ρ<a := by
  by_cases hr : ρ<a <;> by_cases hl : ω<b <;> simp [label, hr, hl]

theorem label_one_iff (ρ ω a b : ℝ) : label ρ ω a b=1 ↔ a≤ρ ∧ ω<b := by
  by_cases hr : ρ<a
  · simp [label, hr, not_le.mpr hr]
  · have hre := le_of_not_gt hr
    by_cases hl : ω<b
    · simp [label, hr, hl, hre]
    · simp [label, hr, hl, hre]

theorem label_two_iff (ρ ω a b : ℝ) : label ρ ω a b=2 ↔ a≤ρ ∧ b≤ω := by
  by_cases hr : ρ<a
  · simp [label, hr, not_le.mpr hr]
  · have hre := le_of_not_gt hr
    by_cases hl : ω<b
    · simp [label, hr, hl, hre, not_le.mpr hl]
    · simp [label, hr, hl, hre, le_of_not_gt hl]

def region {α : Type*} (ρ ω : α → ℝ) (a b : ℝ) (j : Fin 3) : Set α :=
  {x | label (ρ x) (ω x) a b=j}

def caseOccupation {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (ρ ω : α → ℝ) (a b : ℝ) (j : Fin 3) : ℝ := μ.real (region ρ ω a b j)

def boundaryBand {α : Type*} (ρ ω : α → ℝ) (a b ερ εω : ℝ) : Set α :=
  strip ρ a ερ ∪ ({x | a≤ρ x} ∩ strip ω b εω)

def relevantBoundary {α : Type*} (ρ ω : α → ℝ) (a b : ℝ) : Set α :=
  {x | ρ x=a ∨ (a≤ρ x ∧ ω x=b)}

theorem threshold_test_stable (r s a ε : ℝ) (hd : |r-s|≤ε) (hg : ¬|r-a|≤ε) :
    (r<a ↔ s<a) := by
  obtain ⟨hl, hu⟩ := abs_le.mp hd
  constructor
  · intro hr
    by_contra hs
    apply hg
    rw [abs_of_neg (sub_neg.mpr hr)]
    linarith [le_of_not_gt hs]
  · intro hs
    by_contra hr
    apply hg
    rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt hr))]
    linarith

theorem disagreement_subset_band {α : Type*} (ρ ω ρ' ω' : α → ℝ) (a b ερ εω : ℝ)
    (hr : ∀ x, |ρ x-ρ' x|≤ερ) (hl : ∀ x, |ω x-ω' x|≤εω) :
    {x | label (ρ x) (ω x) a b≠label (ρ' x) (ω' x) a b} ⊆ boundaryBand ρ ω a b ερ εω := by
  intro x hx
  by_contra hn
  have hrg : ¬|ρ x-a|≤ερ := fun h => hn (Or.inl h)
  have hri := threshold_test_stable _ _ _ _ (hr x) hrg
  by_cases hρ : ρ x<a
  · have hρ' := hri.mp hρ
    exact hx (by simp [label, hρ, hρ'])
  · have hρ' : ¬ρ' x<a := fun h => hρ (hri.mpr h)
    have hlg : ¬|ω x-b|≤εω := fun h => hn (Or.inr ⟨le_of_not_gt hρ, h⟩)
    have hli := threshold_test_stable _ _ _ _ (hl x) hlg
    by_cases hω : ω x<b
    · have hω' := hli.mp hω
      exact hx (by simp [label, hρ, hρ', hω, hω'])
    · have hω' : ¬ω' x<b := fun h => hω (hli.mpr h)
      exact hx (by simp [label, hρ, hρ', hω, hω'])

theorem region_disagreement_subset {α : Type*} (ρ ω ρ' ω' : α → ℝ) (a b : ℝ)
    (j : Fin 3) : region ρ ω a b j ∆ region ρ' ω' a b j ⊆
      {x | label (ρ x) (ω x) a b≠label (ρ' x) (ω' x) a b} := by
  intro x hx he
  rcases hx with hx | hx
  · exact hx.2 (he.symm.trans hx.1)
  · exact hx.2 (he.trans hx.1)

theorem disagreement_measure_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (ρ ω ρ' ω' : α → ℝ) (a b ερ εω : ℝ)
    (hr : ∀ x, |ρ x-ρ' x|≤ερ) (hl : ∀ x, |ω x-ω' x|≤εω) :
    μ {x | label (ρ x) (ω x) a b≠label (ρ' x) (ω' x) a b}≤
      μ (strip ρ a ερ)+μ ({x | a≤ρ x} ∩ strip ω b εω) :=
  (measure_mono (disagreement_subset_band ρ ω ρ' ω' a b ερ εω hr hl)).trans
    (measure_union_le _ _)

theorem caseOccupation_difference_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (ρ ω ρ' ω' : α → ℝ) (a b ερ εω : ℝ) (j : Fin 3)
    (hr : ∀ x, |ρ x-ρ' x|≤ερ) (hl : ∀ x, |ω x-ω' x|≤εω) :
    |caseOccupation μ ρ ω a b j-caseOccupation μ ρ' ω' a b j|≤
      μ.real (strip ρ a ερ)+μ.real ({x | a≤ρ x} ∩ strip ω b εω) := by
  have hs := (region_disagreement_subset ρ ω ρ' ω' a b j).trans
    (disagreement_subset_band ρ ω ρ' ω' a b ερ εω hr hl)
  have hfg := (show region ρ ω a b j \ region ρ' ω' a b j ⊆ boundaryBand ρ ω a b ερ εω from
    fun x hx => hs (Or.inl hx))
  have hgf := (show region ρ' ω' a b j \ region ρ ω a b j ⊆ boundaryBand ρ ω a b ερ εω from
    fun x hx => hs (Or.inr hx))
  have hb : |caseOccupation μ ρ ω a b j-caseOccupation μ ρ' ω' a b j|≤
      μ.real (boundaryBand ρ ω a b ερ εω) := by
    apply abs_le.mpr
    constructor
    · have hh := (le_measureReal_sdiff (μ := μ)
        (s₁ := region ρ' ω' a b j) (s₂ := region ρ ω a b j)).trans (measureReal_mono hgf)
      unfold caseOccupation
      linarith
    · exact (le_measureReal_sdiff (μ := μ)).trans (measureReal_mono hfg)
  exact hb.trans (measureReal_union_le _ _)

theorem label_measurable {α : Type*} [MeasurableSpace α] {ρ ω : α → ℝ}
    (hr : Measurable ρ) (hl : Measurable ω) (a b : ℝ) :
    Measurable (fun x => label (ρ x) (ω x) a b) :=
  Measurable.ite (measurableSet_lt hr measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt hl measurable_const) measurable_const measurable_const)

theorem region_measurable {α : Type*} [MeasurableSpace α] {ρ ω : α → ℝ}
    (hr : Measurable ρ) (hl : Measurable ω) (a b : ℝ) (j : Fin 3) :
    MeasurableSet (region ρ ω a b j) :=
  measurableSet_eq_fun (label_measurable hr hl a b) measurable_const

theorem label_eventually_eq {r l : ℝ} {rₙ lₙ : ℕ → ℝ} (a b : ℝ)
    (hr : Tendsto rₙ atTop (𝓝 r)) (hl : a≤r → Tendsto lₙ atTop (𝓝 l))
    (hne : r≠a) (hrel : r<a ∨ l≠b) :
    ∀ᶠ n in atTop, label (rₙ n) (lₙ n) a b=label r l a b := by
  by_cases hρ : r<a
  · have hh := (tendsto_order.mp hr).2 a hρ
    filter_upwards [hh] with n hn
    simp [label, hρ, hn]
  · have hρgt : a<r := lt_of_le_of_ne (le_of_not_gt hρ) hne.symm
    have hh := (tendsto_order.mp hr).1 a hρgt
    have hl' := hl (le_of_not_gt hρ)
    have hωne : l≠b := hrel.resolve_left hρ
    by_cases hω : l<b
    · have hg := (tendsto_order.mp hl').2 b hω
      filter_upwards [hh, hg] with n hn hg
      simp [label, hρ, not_lt_of_gt hn, hω, hg]
    · have hωgt : b<l := lt_of_le_of_ne (le_of_not_gt hω) hωne.symm
      have hg := (tendsto_order.mp hl').1 b hωgt
      filter_upwards [hh, hg] with n hn hg
      simp [label, hρ, not_lt_of_gt hn, hω, not_lt_of_gt hg]

def caseIndicator {α : Type*} (ρ ω : α → ℝ) (a b : ℝ) (j : Fin 3) : α → ℝ :=
  (region ρ ω a b j).indicator (1 : α → ℝ)

theorem caseIndicator_norm_le {α : Type*} (ρ ω : α → ℝ) (a b : ℝ) (j : Fin 3) (x : α) :
    ‖caseIndicator ρ ω a b j x‖≤1 := by
  classical
  by_cases hx : x∈region ρ ω a b j <;> simp [caseIndicator, hx]

theorem caseIndicator_integrable {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {ρ ω : α → ℝ} (hr : Measurable ρ) (hl : Measurable ω)
    (a b : ℝ) (j : Fin 3) : Integrable (caseIndicator ρ ω a b j) μ :=
  (integrable_const 1).indicator (region_measurable hr hl a b j)

theorem integral_caseIndicator {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {ρ ω : α → ℝ} (hr : Measurable ρ) (hl : Measurable ω) (a b : ℝ) (j : Fin 3) :
    (∫ x, caseIndicator ρ ω a b j x ∂μ)=caseOccupation μ ρ ω a b j :=
  integral_indicator_one (region_measurable hr hl a b j)

theorem caseOccupation_converges {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (ρ ω : α → ℝ) (ρₙ ωₙ : ℕ → α → ℝ) (a b : ℝ) (j : Fin 3)
    (hrm : Measurable ρ) (hlm : Measurable ω)
    (hrnm : ∀ n, Measurable (ρₙ n)) (hlnm : ∀ n, Measurable (ωₙ n))
    (hrlim : ∀ᵐ x ∂μ, Tendsto (fun n => ρₙ n x) atTop (𝓝 (ρ x)))
    (hllim : ∀ᵐ x ∂μ, a≤ρ x → Tendsto (fun n => ωₙ n x) atTop (𝓝 (ω x)))
    (hb : μ (relevantBoundary ρ ω a b)=0) :
    Tendsto (fun n => caseOccupation μ (ρₙ n) (ωₙ n) a b j) atTop
      (𝓝 (caseOccupation μ ρ ω a b j)) := by
  classical
  have hne : ∀ᵐ x ∂μ, x∉relevantBoundary ρ ω a b := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using hb
  have hc : ∀ᵐ x ∂μ, Tendsto (fun n => caseIndicator (ρₙ n) (ωₙ n) a b j x) atTop
      (𝓝 (caseIndicator ρ ω a b j x)) := by
    filter_upwards [hrlim, hllim, hne] with x hr hl hn
    have hρne : ρ x≠a := fun h => hn (Or.inl h)
    have hrel : ρ x<a ∨ ω x≠b := by
      by_cases hh : ρ x<a
      · exact Or.inl hh
      · exact Or.inr (fun hg => hn (Or.inr ⟨le_of_not_gt hh, hg⟩))
    have he := label_eventually_eq a b hr hl hρne hrel
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n he
    simp only [caseIndicator, Set.indicator_apply, region, Set.mem_ofPred_eq, he]
  have hi := tendsto_integral_of_dominated_convergence (fun _ : α => (1:ℝ))
    (fun n => (caseIndicator_integrable μ (hrnm n) (hlnm n) a b j).aestronglyMeasurable)
    (integrable_const 1)
    (fun n => Filter.Eventually.of_forall (caseIndicator_norm_le (ρₙ n) (ωₙ n) a b j)) hc
  simp only [integral_caseIndicator μ (hrnm _) (hlnm _) a b j,
    integral_caseIndicator μ hrm hlm a b j] at hi
  exact hi

theorem caseOccupation_converges_global {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (ρ ω : α → ℝ) (ρₙ ωₙ : ℕ → α → ℝ) (a b : ℝ) (j : Fin 3)
    (hrm : Measurable ρ) (hlm : Measurable ω)
    (hrnm : ∀ n, Measurable (ρₙ n)) (hlnm : ∀ n, Measurable (ωₙ n))
    (hrlim : ∀ᵐ x ∂μ, Tendsto (fun n => ρₙ n x) atTop (𝓝 (ρ x)))
    (hllim : ∀ᵐ x ∂μ, Tendsto (fun n => ωₙ n x) atTop (𝓝 (ω x)))
    (hb : μ (relevantBoundary ρ ω a b)=0) :
    Tendsto (fun n => caseOccupation μ (ρₙ n) (ωₙ n) a b j) atTop
      (𝓝 (caseOccupation μ ρ ω a b j)) := by
  apply caseOccupation_converges μ ρ ω ρₙ ωₙ a b j hrm hlm hrnm hlnm hrlim _ hb
  filter_upwards [hllim] with x hx
  exact fun _ => hx

theorem nonconcentrated_boundary_empty {α : Type*} (ρ ω : α → ℝ) (a b : ℝ)
    (hr : ∀ x, ρ x<a) : relevantBoundary ρ ω a b=∅ := by
  ext x
  have hh := hr x
  simp only [relevantBoundary, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_or, not_and]
  constructor
  · exact ne_of_lt hh
  · intro hc
    linarith

theorem caseZeroOccupation_eq {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (ρ ω : α → ℝ) (a b : ℝ) : caseOccupation μ ρ ω a b 0=occupation μ ρ a := by
  unfold caseOccupation occupation
  congr 1
  ext x
  exact label_zero_iff _ _ _ _

theorem finite_sector_full_case_failure (δ : ℝ) (hδ : 0<δ) :
    ∃ p : ℝ, |p|<δ ∧ (∀ i t, 0<sectorEnergy p i t) ∧
      |caseOccupation unitTime (sectorConcentration p) (fun _ => 1) (1/2) 2 0-
        caseOccupation unitTime (sectorConcentration 0) (fun _ => 1) (1/2) 2 0|=1 := by
  simpa only [caseZeroOccupation_eq] using finite_sector_arbitrarily_close_failure δ hδ

end OperatorDerivativeRewrite.Foundation.CorridorClassification
