import Foundation.RootMarkMartingaleRepresentation

/-! Actual finite-horizon centered-terminal representation by the three predictable channels. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace OperatorDerivativeRewrite.Foundation.RootMarkFiniteClark
open RootMarkStochasticIntegral RootMarkMartingaleRepresentation
open MarkedRootRenewalProcess (MarkSample marks)
open RootRenewalWalkMarginal (initialSegment prefix_measurable prefix_preserving)

theorem history_zero : history 0 = ⊥ := by
  change MeasurableSpace.comap (initialSegment 0) inferInstance = ⊥
  have he : initialSegment 0 = (fun _ : MarkSample => (fun i : Fin 0 => Fin.elim0 i : Fin 0 → Fin 4)) := by
    funext η i
    exact Fin.elim0 i
  rw [he, MeasurableSpace.comap_const]

theorem terminal_integrable (N : ℕ) (f : ComplexFourthRootWalk.Sample N → ℂ) :
    Integrable (fun η => f (initialSegment N η)) marks := by
  have hi : Integrable f (marks.map (initialSegment N)) := by
    rw [(prefix_preserving N).map_eq]
    exact Integrable.of_finite
  exact (integrable_map_measure (measurable_of_countable f).aestronglyMeasurable
    (prefix_measurable N).aemeasurable).mp hi

theorem finite_clark (a : ℝ) (ha : a ≠ 0) (N : ℕ) (f : ComplexFourthRootWalk.Sample N → ℂ) :
    ∃ H : Fin 3 → Coefficients,
      (fun η => f (initialSegment N η)-(∫ ξ, f (initialSegment N ξ) ∂marks)) =ᵐ[marks]
        fun η => stochasticIntegral a 0 (H 0) N η+stochasticIntegral a 1 (H 1) N η+
          stochasticIntegral a 2 (H 2) N η := by
  let Y : MarkSample → ℂ := fun η => f (initialSegment N η)
  have hY : Integrable Y marks := terminal_integrable N f
  have hm : StronglyMeasurable[history N] Y :=
    ((measurable_of_countable f).comp (prefix_past N)).stronglyMeasurable
  have hN : marks[Y | history N] = Y :=
    condExp_of_stronglyMeasurable (history.le N) hm hY
  have h₀ : marks[Y | history 0] = (fun _ => ∫ η, Y η ∂marks) := by
    rw [history_zero, condExp_bot]
  obtain ⟨H,hH⟩ := predictable_representation a ha (fun n => marks[Y | history n])
    (martingale_condExp Y history marks)
  refine ⟨H, ?_⟩
  have he := hH N
  rw [hN, h₀] at he
  exact he

end OperatorDerivativeRewrite.Foundation.RootMarkFiniteClark
