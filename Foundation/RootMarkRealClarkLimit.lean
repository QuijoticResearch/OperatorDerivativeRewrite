import Foundation.RootMarkFiniteClark
import Foundation.RootMarkPrefixLimit
import Foundation.RootMarkItoIsometry

/-! Transfer of genuine real conditional approximation to the complex mark-channel calculus. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.RootMarkRealClarkLimit
open RootMarkStochasticIntegral
open MarkedRootRenewalProcess (MarkSample marks)

def lift (Y : MarkSample → ℝ) : MarkSample → ℂ := Complex.ofRealCLM ∘ Y

theorem lifted_error (Y : MarkSample → ℝ) (hY : Integrable Y marks) (n : ℕ) :
    eLpNorm (marks[lift Y | history n]-lift Y) 1 marks =
      eLpNorm (marks[Y | history n]-Y) 1 marks := by
  unfold lift
  have hc := Complex.ofRealCLM.cont.comp_aestronglyMeasurable hY.aestronglyMeasurable
  apply eLpNorm_congr_norm_ae
    (((stronglyMeasurable_condExp.mono (history.le n)).aestronglyMeasurable).sub hc)
    (((stronglyMeasurable_condExp.mono (history.le n)).aestronglyMeasurable).sub hY.aestronglyMeasurable)
  have he := ContinuousLinearMap.comp_condExp_comm (μ := marks) (m := history n) hY Complex.ofRealCLM
  filter_upwards [he] with η hη
  change (marks[Y | history n] η : ℂ) = marks[Complex.ofRealCLM ∘ Y | history n] η at hη
  change ‖marks[Complex.ofRealCLM ∘ Y | history n] η-(Y η : ℂ)‖ = ‖marks[Y | history n] η-Y η‖
  rw [← hη, ← Complex.ofReal_sub, Complex.norm_real]

theorem lifted_condExp_limit (Y : MarkSample → ℝ) (hY : Integrable Y marks)
    (hm : StronglyMeasurable Y) :
    Tendsto (fun n : ℕ => eLpNorm (marks[lift Y | history n]-lift Y) 1 marks)
      atTop (𝓝 0) := by
  simpa only [lifted_error Y hY] using RootMarkPrefixLimit.real_condExp_limit Y hY hm

theorem coherent_clark (a : ℝ) (ha : a ≠ 0) (Y : MarkSample → ℝ) :
    ∃ H : Fin 3 → Coefficients, ∀ n : ℕ,
      (fun η => marks[lift Y | history n] η-(∫ ξ, (Y ξ : ℂ) ∂marks)) =ᵐ[marks]
        RootMarkItoIsometry.totalIntegral a H n := by
  obtain ⟨H,hH⟩ := RootMarkMartingaleRepresentation.predictable_representation a ha
    (fun n => marks[lift Y | history n]) (martingale_condExp (lift Y) history marks)
  refine ⟨H, fun n => ?_⟩
  have he := hH n
  have h₀ : marks[lift Y | history 0] = (fun _ => ∫ ξ, (Y ξ : ℂ) ∂marks) := by
    rw [RootMarkFiniteClark.history_zero, condExp_bot]
    rfl
  rw [h₀] at he
  exact he

theorem infinite_clark_L1 (a : ℝ) (ha : a ≠ 0) (Y : MarkSample → ℝ)
    (hY : Integrable Y marks) (hm : StronglyMeasurable Y) :
    ∃ H : Fin 3 → Coefficients,
      (∀ n : ℕ, (fun η => marks[lift Y | history n] η-(∫ ξ, (Y ξ : ℂ) ∂marks)) =ᵐ[marks]
        RootMarkItoIsometry.totalIntegral a H n) ∧
      Tendsto (fun n : ℕ => eLpNorm
        (RootMarkItoIsometry.totalIntegral a H n -
          (fun η => (Y η : ℂ)-(∫ ξ, (Y ξ : ℂ) ∂marks))) 1 marks) atTop (𝓝 0) := by
  obtain ⟨H,hH⟩ := coherent_clark a ha Y
  refine ⟨H,hH,?_⟩
  have he (n : ℕ) :
      eLpNorm (RootMarkItoIsometry.totalIntegral a H n -
        (fun η => (Y η : ℂ)-(∫ ξ, (Y ξ : ℂ) ∂marks))) 1 marks =
      eLpNorm (marks[lift Y | history n]-lift Y) 1 marks := by
    apply eLpNorm_congr_ae
    filter_upwards [hH n] with η hη
    simp only [Pi.sub_apply]
    change marks[lift Y | history n] η-(∫ ξ, (Y ξ : ℂ) ∂marks) = _ at hη
    rw [← hη]
    change _ = marks[lift Y | history n] η-(Y η : ℂ)
    ring
  simpa only [he] using lifted_condExp_limit Y hY hm

theorem lifted_condExp_ae_limit (Y : MarkSample → ℝ) (hY : Integrable Y marks)
    (hm : StronglyMeasurable Y) :
    ∀ᵐ η ∂marks, Tendsto (fun n : ℕ => marks[lift Y | history n] η)
      atTop (𝓝 (Y η : ℂ)) := by
  have he : ∀ n : ℕ, (fun η => (marks[Y | history n] η : ℂ)) =ᵐ[marks]
      marks[lift Y | history n] := fun n =>
    ContinuousLinearMap.comp_condExp_comm (μ := marks) (m := history n) hY Complex.ofRealCLM
  filter_upwards [RootMarkPrefixLimit.real_condExp_ae_limit Y hY hm, ae_all_iff.mpr he]
    with η hη heη
  have ht := Complex.continuous_ofReal.continuousAt.tendsto.comp hη
  exact ht.congr (fun n => heη n)

theorem infinite_clark_ae (a : ℝ) (ha : a ≠ 0) (Y : MarkSample → ℝ)
    (hY : Integrable Y marks) (hm : StronglyMeasurable Y) :
    ∃ H : Fin 3 → Coefficients,
      (∀ n : ℕ, (fun η => marks[lift Y | history n] η-(∫ ξ, (Y ξ : ℂ) ∂marks)) =ᵐ[marks]
        RootMarkItoIsometry.totalIntegral a H n) ∧
      ∀ᵐ η ∂marks, Tendsto (fun n : ℕ => RootMarkItoIsometry.totalIntegral a H n η)
        atTop (𝓝 ((Y η : ℂ)-(∫ ξ, (Y ξ : ℂ) ∂marks))) := by
  obtain ⟨H,hH⟩ := coherent_clark a ha Y
  refine ⟨H,hH,?_⟩
  filter_upwards [lifted_condExp_ae_limit Y hY hm, ae_all_iff.mpr hH] with η hη heη
  have ht := hη.sub_const (∫ ξ, (Y ξ : ℂ) ∂marks)
  exact ht.congr (fun n => heη n)

end OperatorDerivativeRewrite.Foundation.RootMarkRealClarkLimit
