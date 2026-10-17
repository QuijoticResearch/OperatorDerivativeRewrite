import Mathlib.Probability.Independence.Process.Basic

/-! Disjoint coordinate families of a native independent source form independent processes. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.IndependentCoordinateBlocks

theorem disjoint_families {Ω ι S T E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ι → Ω → E}
    (hX : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (f : S → ι) (g : T → ι) (hfg : ∀ s t, f s ≠ g t) :
    IndepFun (fun ω s => X (f s) ω) (fun ω t => X (g t) ω) μ := by
  classical
  apply IndepFun.process_indepFun_process (fun s => hX (f s)) (fun t => hX (g t))
  intro I J
  let A := I.image f
  let B := J.image g
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro k hkA hkB
    rcases Finset.mem_image.mp hkA with ⟨s,hs,hsk⟩
    rcases Finset.mem_image.mp hkB with ⟨t,ht,htk⟩
    exact hfg s t (hsk.trans htk.symm)
  let fa : (A → E) → (I → E) := fun y i => y ⟨f i,Finset.mem_image.mpr ⟨i,i.2,rfl⟩⟩
  let gb : (B → E) → (J → E) := fun y j => y ⟨g j,Finset.mem_image.mpr ⟨j,j.2,rfl⟩⟩
  have hf : Measurable fa := measurable_pi_iff.mpr (fun i => measurable_pi_apply _)
  have hg : Measurable gb := measurable_pi_iff.mpr (fun j => measurable_pi_apply _)
  exact (hi.indepFun_finset A B hd hX).comp hf hg

end OperatorDerivativeRewrite.Foundation.IndependentCoordinateBlocks
