import Foundation.AmbientNullAugmentation
import Mathlib.MeasureTheory.Function.FactorsThrough

/-! Raw measurable versions for functions measurable under ambient null
augmentation. The statement concerns versions, not equality of completions. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.AmbientNullVersions
variable {Ω E : Type*} (m : MeasurableSpace Ω) [m₀ : MeasurableSpace Ω]
  (μ : Measure Ω) [Nonempty E] [TopologicalSpace E] [TopologicalSpace.IsCompletelyMetrizableSpace E]
set_option backward.isDefEq.respectTransparency false

theorem stronglyMeasurable_raw_version (f : Ω → E)
    (hf : StronglyMeasurable[AmbientNullAugmentation.augment m μ] f) :
    AEStronglyMeasurable[m] f μ := by
  classical
  letI : MeasurableSpace Ω := AmbientNullAugmentation.augment m μ
  induction f,hf using StronglyMeasurable.induction' with
  | const c => exact ⟨fun _ => c,stronglyMeasurable_const,EventuallyEq.rfl⟩
  | @pcw f g s hf hg hs ihf ihg =>
    obtain ⟨_,A,hA,he⟩ := hs
    obtain ⟨f',hf',hef⟩ := ihf
    obtain ⟨g',hg',heg⟩ := ihg
    refine ⟨A.piecewise f' g',hf'.piecewise hA hg',?_⟩
    filter_upwards [he,hef,heg] with ω hω hfw hgw
    simp only [Set.piecewise,← hω,hfw,hgw]
  | @lim f g hf hg ih hlim =>
    choose v hv he using ih
    refine ⟨fun ω => limUnder atTop (fun n => v n ω),?_,?_⟩
    · letI : MeasurableSpace Ω := m
      exact StronglyMeasurable.limUnder hv
    · filter_upwards [ae_all_iff.mpr he] with ω hω
      have ht : Tendsto (fun n => v n ω) atTop (𝓝 (g ω)) := by
        simpa only [hω] using hlim ω
      exact ht.limUnder_eq.symm

theorem exists_raw_factor {Y : Type*} [MeasurableSpace Y]
    (X : Ω → Y) (f : Ω → E)
    (hf : StronglyMeasurable[AmbientNullAugmentation.augment
      (MeasurableSpace.comap X inferInstance) μ] f) :
    ∃ F : Y → E, StronglyMeasurable F ∧ f =ᵐ[μ] (fun ω => F (X ω)) := by
  obtain ⟨g,hg,he⟩ := stronglyMeasurable_raw_version _ μ f hf
  obtain ⟨F,hF,hgF⟩ := hg.exists_eq_measurable_comp
  exact ⟨F,hF,by simpa only [hgF,Function.comp_def] using he⟩

end OperatorDerivativeRewrite.Foundation.AmbientNullVersions
