import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Process.Filtration

/-! Null augmentation inside a fixed ambient sigma-algebra. Every new event
has a raw measurable version; conditional expectations retain their values.
This is not a claim of full completion or right continuity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
namespace OperatorDerivativeRewrite.Foundation.AmbientNullAugmentation
variable {Ω : Type*} (m : MeasurableSpace Ω) [m₀ : MeasurableSpace Ω] (μ : Measure[m₀] Ω)

@[instance_reducible]
def augment : MeasurableSpace Ω where
  MeasurableSet' s := MeasurableSet[m₀] s ∧
    ∃ A : Set Ω, MeasurableSet[m] A ∧ ∀ᵐ ω ∂μ, ω ∈ s ↔ ω ∈ A
  measurableSet_empty := ⟨MeasurableSet.empty, ∅, m.measurableSet_empty,
    Eventually.of_forall (fun _ => Iff.rfl)⟩
  measurableSet_compl := by
    rintro s ⟨hs, A, hA, he⟩
    refine ⟨hs.compl, Aᶜ, hA.compl, ?_⟩
    exact he.mono (fun _ h => not_congr h)
  measurableSet_iUnion := by
    intro s hs
    classical
    choose A hA he using fun n => (hs n).2
    refine ⟨MeasurableSet.iUnion (fun n => (hs n).1), ⋃ n, A n,
      MeasurableSet.iUnion hA, ?_⟩
    filter_upwards [ae_all_iff.mpr he] with ω hω
    simp only [mem_iUnion]
    exact exists_congr (fun n => hω n)

theorem measurableSet_iff (s : Set Ω) :
    MeasurableSet[augment m μ] s ↔ MeasurableSet[m₀] s ∧
      ∃ A : Set Ω, MeasurableSet[m] A ∧ ∀ᵐ ω ∂μ, ω ∈ s ↔ ω ∈ A := Iff.rfl

theorem le_ambient : augment m μ ≤ m₀ := fun _ hs => hs.1

theorem raw_le (hm : m ≤ m₀) : m ≤ augment m μ := by
  intro s hs
  exact ⟨hm s hs, s, hs, Eventually.of_forall (fun _ => Iff.rfl)⟩

theorem monotone : Monotone (fun r => augment r μ) := by
  intro m n hmn s hs
  obtain ⟨hs, A, hA, he⟩ := hs
  exact ⟨hs, A, hmn A hA, he⟩

theorem measurableSet_null (s : Set Ω)
    (hs : MeasurableSet[m₀] s) (hμ : μ s = 0) : MeasurableSet[augment m μ] s := by
  refine ⟨hs, ∅, m.measurableSet_empty, ?_⟩
  have h : ∀ᵐ ω ∂μ, ω ∉ s := ae_iff.mpr (by simpa using hμ)
  exact h.mono (fun _ hω => by simp [hω])

theorem measurable_of_raw_aestronglyMeasurable {E : Type*}
    [MeasurableSpace E] [PseudoMetricSpace E] [BorelSpace E]
    {f : Ω → E} (hf : Measurable f) (hr : AEStronglyMeasurable[m] f μ) :
    Measurable[augment m μ] f := by
  obtain ⟨g, hg, he⟩ := hr
  intro s hs
  refine ⟨hf hs, g ⁻¹' s, hg.measurable hs, ?_⟩
  exact he.mono (fun _ hω => by simp only [mem_preimage, hω])

def filtration {ι : Type*} [Preorder ι] (𝓕 : Filtration ι m₀) : Filtration ι m₀ :=
  ⟨fun t => augment (𝓕 t) μ, fun _ _ h => monotone μ (𝓕.mono h),
    fun t => le_ambient (𝓕 t) μ⟩

theorem filtration_raw_le {ι : Type*} [Preorder ι] (𝓕 : Filtration ι m₀) (t : ι) :
    𝓕 t ≤ filtration μ 𝓕 t := raw_le (𝓕 t) μ (𝓕.le t)

theorem condExp_invariant [IsFiniteMeasure μ] (hm : m ≤ m₀)
    (f : Ω → ℝ) (hf : Integrable f μ) : μ[f | m] =ᵐ[μ] μ[f | augment m μ] := by
  apply ae_eq_condExp_of_forall_setIntegral_eq (le_ambient m μ) hf
  · exact fun _ _ _ => integrable_condExp.integrableOn
  · intro s hs _
    obtain ⟨_, A, hA, he⟩ := hs
    have he' : s =ᵐ[μ] A := he.set_eq
    calc
      (∫ ω in s, μ[f | m] ω ∂μ) = ∫ ω in A, μ[f | m] ω ∂μ := setIntegral_congr_set he'
      _ = ∫ ω in A, f ω ∂μ := setIntegral_condExp hm hf hA
      _ = ∫ ω in s, f ω ∂μ := (setIntegral_congr_set he').symm
  · have h : StronglyMeasurable[m] (μ[f | m]) := stronglyMeasurable_condExp
    exact (h.mono (raw_le m μ hm)).aestronglyMeasurable

end OperatorDerivativeRewrite.Foundation.AmbientNullAugmentation
