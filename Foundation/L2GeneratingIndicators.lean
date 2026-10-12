import Mathlib.MeasureTheory.Function.ConditionalExpectation.Unique
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! Genuine L2 density from a generating pi-system on a finite measure space. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} {m : MeasurableSpace Ω} [m0 : MeasurableSpace Ω]
  (μ : Measure Ω) [IsFiniteMeasure μ]

def generatingIndicatorSpan (S : Set (Set Ω)) : Submodule ℝ (Lp ℝ 2 μ) :=
  Submodule.span ℝ {F | ∃ s ∈ S, ∃ hs : MeasurableSet s,
    F = indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ)}

/-- Density is in the independently specified measurable subspace, not merely
in the closure of the indicator span itself. -/
theorem generatingIndicatorSpan_closure (hm : m ≤ m0)
    (S : Set (Set Ω)) (hgen : MeasurableSpace.generateFrom S = m)
    (hpi : IsPiSystem S) (hu : univ ∈ S) :
    (generatingIndicatorSpan μ S).topologicalClosure = lpMeas ℝ ℝ m 2 μ := by
  have hsm {s : Set Ω} (hs : s ∈ S) : MeasurableSet[m] s :=
    hgen ▸ MeasurableSpace.measurableSet_generateFrom hs
  have hle : (generatingIndicatorSpan μ S).topologicalClosure ≤ lpMeas ℝ ℝ m 2 μ := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro F ⟨s, hs, hs0, rfl⟩
      exact mem_lpMeas_indicatorConstLp hm (hsm hs) (measure_ne_top μ s)
    · exact isClosed_aestronglyMeasurable hm
  have hz : (generatingIndicatorSpan μ S).topologicalClosureᗮ ⊓ lpMeas ℝ ℝ m 2 μ = ⊥ := by
    apply eq_bot_iff.mpr
    rintro F ⟨hFo, hFm⟩
    have hF : F ∈ (generatingIndicatorSpan μ S)ᗮ :=
      Submodule.orthogonal_le (generatingIndicatorSpan μ S).le_topologicalClosure hFo
    have hi : Integrable F μ := (Lp.memLp F).integrable (by simp)
    have hzero {s : Set Ω} (hs : s ∈ S) : (∫ x in s, F x ∂μ) = 0 := by
      have he := (generatingIndicatorSpan μ S).inner_left_of_mem_orthogonal
        (Submodule.subset_span ⟨s, hs, hm s (hsm hs), rfl⟩ :
          indicatorConstLp 2 (hm s (hsm hs)) (measure_ne_top μ s) (1 : ℝ) ∈
            generatingIndicatorSpan μ S) hF
      rw [real_inner_comm, L2.inner_indicatorConstLp_one] at he
      exact he
    have htotal : (∫ x, F x ∂μ) = 0 := by simpa using hzero hu
    have hall : ∀ s, MeasurableSet[m] s → (∫ x in s, F x ∂μ) = 0 := by
      refine MeasurableSpace.induction_on_inter
        (C := fun s _ => (∫ x in s, F x ∂μ) = 0) hgen.symm hpi (by simp) ?_ ?_ ?_
      · exact fun _ hs => hzero hs
      · intro s hs hzero
        rw [setIntegral_compl (hm s hs) hi, htotal, hzero, sub_self]
      · intro s hd hs hz
        rw [integral_iUnion (fun i => hm _ (hs i)) hd hi.integrableOn]
        simp only [hz, tsum_zero]
    have he := Lp.ae_eq_zero_of_forall_setIntegral_eq_zero' ℝ hm F (by norm_num) (by simp)
      (fun _ _ _ => hi.integrableOn) (fun s hs _ => hall s hs) hFm
    exact Lp.ext (he.trans (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ)).symm)
  simpa only [hz, sup_bot_eq] using Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hle

end OperatorDerivativeRewrite.Foundation
