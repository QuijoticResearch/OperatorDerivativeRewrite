import Foundation.RootMarkGKWProjection
import Foundation.RootMarkIntegralUniqueness

/-! Identification of the actual finite integration range with centered finite-prefix L2 variables. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal InnerProductSpace
namespace OperatorDerivativeRewrite.Foundation.RootMarkFiniteRange
open RootMarkStochasticIntegral RootMarkItoIsometry RootMarkFiniteOperator RootMarkGKWProjection
open MarkedRootRenewalProcess (MarkSample marks)
open RootRenewalWalkMarginal (initialSegment)

def tableOfCoefficients (N : ℕ) (H : Fin 3 → Coefficients) : Table N :=
  WithLp.toLp 2 (fun p : Node N => H p.2.2 p.1.val p.2.1)

theorem coefficients_recover (N : ℕ) (H : Fin 3 → Coefficients)
    (j : ℕ) (hj : j < N) (r : Fin 3) (ξ : ComplexFourthRootWalk.Sample j) :
    coefficients N (tableOfCoefficients N H) r j ξ = H r j ξ := by
  simp [coefficients, tableOfCoefficients, hj]

theorem integral_recover (a : ℝ) (N : ℕ) (H : Fin 3 → Coefficients) :
    totalIntegral a (coefficients N (tableOfCoefficients N H)) N = totalIntegral a H N := by
  have he (r : Fin 3) :
      stochasticIntegral a r (coefficients N (tableOfCoefficients N H) r) N =
        stochasticIntegral a r (H r) N := by
    funext η
    unfold stochasticIntegral
    apply Finset.sum_congr rfl
    intro j hj
    unfold increment
    rw [coefficients_recover N H j (Finset.mem_range.mp hj) r]
  simp only [totalIntegral, Pi.add_apply]
  rw [he 0,he 1,he 2]

theorem representable_of_prefix (a : ℝ) (ha : a ≠ 0) (N : ℕ) (Y : Lp ℂ 2 marks)
    (f : ComplexFourthRootWalk.Sample N → ℂ)
    (hf : (Y : MarkSample → ℂ) =ᵐ[marks] fun η => f (initialSegment N η))
    (hmean : (∫ η, Y η ∂marks) = 0) :
    ∃ u : Table N, finiteIntegral a N u = Y := by
  have hfm : (∫ η, f (initialSegment N η) ∂marks) = 0 :=
    (integral_congr_ae hf.symm).trans hmean
  obtain ⟨H,hH⟩ := RootMarkFiniteClark.finite_clark a ha N f
  have he : (fun η => stochasticIntegral a 0 (H 0) N η+
      stochasticIntegral a 1 (H 1) N η+stochasticIntegral a 2 (H 2) N η) = totalIntegral a H N := rfl
  rw [hfm, he] at hH
  let u := tableOfCoefficients N H
  refine ⟨u, ?_⟩
  apply Lp.ext
  filter_upwards [finiteIntegral_ae a N u,hH,hf] with η hu hH hf
  rw [integral_recover] at hu
  change f (initialSegment N η)-0 = totalIntegral a H N η at hH
  rw [sub_zero] at hH
  exact hu.trans (hH.symm.trans hf.symm)

theorem finiteIntegral_prefix (a : ℝ) (N : ℕ) (u : Table N) :
    ∃ f : ComplexFourthRootWalk.Sample N → ℂ,
      (finiteIntegral a N u : MarkSample → ℂ) =ᵐ[marks] fun η => f (initialSegment N η) := by
  obtain ⟨F,hF⟩ := RootMarkMartingaleRepresentation.adapted_factors
    (totalIntegral a (coefficients N u)) (totalIntegral_martingale a (coefficients N u)).stronglyAdapted
  refine ⟨F N,(finiteIntegral_ae a N u).trans ?_⟩
  apply EventuallyEq.of_eq
  funext η
  exact congrFun (congrFun hF N) η

theorem range_characterization (a : ℝ) (ha : a ≠ 0) (N : ℕ) (Y : Lp ℂ 2 marks) :
    Y ∈ LinearMap.range (finiteIntegral a N).toLinearMap ↔
      (∫ η, Y η ∂marks) = 0 ∧ ∃ f : ComplexFourthRootWalk.Sample N → ℂ,
        (Y : MarkSample → ℂ) =ᵐ[marks] fun η => f (initialSegment N η) := by
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨finiteIntegral_mean_zero a N u,finiteIntegral_prefix a N u⟩
  · rintro ⟨hmean,f,hf⟩
    exact representable_of_prefix a ha N Y f hf hmean

theorem projection_recovers (a : ℝ) (ha : a ≠ 0) (N : ℕ) (Y : Lp ℂ 2 marks)
    (hmean : (∫ η, Y η ∂marks) = 0)
    (hf : ∃ f : ComplexFourthRootWalk.Sample N → ℂ,
      (Y : MarkSample → ℂ) =ᵐ[marks] fun η => f (initialSegment N η)) :
    projection a N Y = Y := by
  apply Submodule.starProjection_eq_self_iff.mpr
  exact (range_characterization a ha N Y).mpr ⟨hmean,hf⟩

theorem prefix_measurable_iff (N : ℕ) (Y : MarkSample → ℂ) :
    AEStronglyMeasurable[history N] Y marks ↔
      ∃ f : ComplexFourthRootWalk.Sample N → ℂ, Y =ᵐ[marks] fun η => f (initialSegment N η) := by
  constructor
  · rintro ⟨g,hg,hYg⟩
    have hg' : StronglyMeasurable[MeasurableSpace.comap (initialSegment N) inferInstance] g := hg
    obtain ⟨f,_,hgf⟩ := hg'.exists_eq_measurable_comp
    refine ⟨f,?_⟩
    filter_upwards [hYg] with η hη
    exact hη.trans (congrFun hgf η)
  · rintro ⟨f,hf⟩
    exact ⟨fun η => f (initialSegment N η),
      ((measurable_of_countable f).comp (prefix_past N)).stronglyMeasurable,hf⟩

theorem range_measurable (a : ℝ) (ha : a ≠ 0) (N : ℕ) (Y : Lp ℂ 2 marks) :
    Y ∈ LinearMap.range (finiteIntegral a N).toLinearMap ↔
      (∫ η, Y η ∂marks) = 0 ∧ AEStronglyMeasurable[history N] (Y : MarkSample → ℂ) marks := by
  rw [range_characterization a ha N Y, prefix_measurable_iff]

end OperatorDerivativeRewrite.Foundation.RootMarkFiniteRange
