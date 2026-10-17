import Foundation.HigherHeatSchwartzSemigroup
import Foundation.HigherHeatBackwardFourier

/-! The actual even heat kernel and its Schwartz transition semigroup in the forward increment convention. -/
noncomputable section
open MeasureTheory FourierTransform Filter
open scoped SchwartzMap NNReal Topology Convolution
namespace OperatorDerivativeRewrite.Foundation.HigherHeatSchwartzTransition
open HigherHeatL2 HigherHeatSignedLaws GaussianSchwartzKernel HigherHeatSchwartzSemigroup
open HigherHeatBackwardFourier

theorem symbol_even (m : ℕ) (t : ℝ≥0) (ξ : ℝ) : symbol m t (-ξ)=symbol m t ξ := by
  simp only [symbol,mul_neg,pow_mul,neg_sq]

theorem kernel_even (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (x : ℝ) :
    evenKernel m hm t ht (-x)=evenKernel m hm t ht x := by
  let q := evenSymbol m hm t ht
  have he (ξ : ℝ) : q (-ξ)=q ξ := by
    simp only [q,evenSymbol_apply,symbol_even]
  change 𝓕⁻ q (-x)=𝓕⁻ q x
  simp only [SchwartzMap.fourierInv_coe,Real.fourierInv_eq]
  calc
    _ = ∫ ξ : ℝ, Real.fourierChar (inner ℝ (-ξ) x) • q (-ξ) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ξ => by simp only [inner_neg_left,inner_neg_right,he]
    _ = _ := integral_neg_eq_self (fun ξ : ℝ => Real.fourierChar (inner ℝ ξ x) • q ξ) volume

theorem realKernel_even (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (x : ℝ) :
    realKernel m hm t ht (-x)=realKernel m hm t ht x := by
  apply Complex.ofReal_injective
  simp only [realKernel_coe]
  exact kernel_even m hm t ht x

theorem transition_integrable (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (f : 𝓢(ℝ,ℂ)) (x : ℝ) :
    Integrable (fun z : ℝ => f (x+z)*(realKernel m hm t ht z:ℂ)) := by
  refine (((realKernel m hm t ht).integrable (μ := volume)).norm.const_mul
    (SchwartzMap.seminorm ℝ 0 0 f)).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · exact Eventually.of_forall fun z => by
      rw [norm_mul,Complex.norm_real]
      exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℝ f (x+z)) (norm_nonneg _)

theorem transition_evolve (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (f : 𝓢(ℝ,ℂ)) (x : ℝ) : transition m hm t ht f x=evolve m hm t f x := by
  unfold transition
  calc
    _ = ∫ z : ℝ, f (x+(-z))*(realKernel m hm t ht (-z):ℂ) :=
      (integral_neg_eq_self (fun z : ℝ => f (x+z)*(realKernel m hm t ht z:ℂ)) volume).symm
    _ = _ := by
      rw [evolve_positive m hm t ht,SchwartzMap.convolution_apply,convolution_def]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        dsimp only
        simp only [realKernel_even,realKernel_coe,ContinuousLinearMap.mul_apply',sub_eq_add_neg]
        ring

theorem transition_composition (m : ℕ) (hm : 0 < m) (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t)
    (f : 𝓢(ℝ,ℂ)) (x : ℝ) :
    transition m hm s hs (evolve m hm t f) x=transition m hm (s+t) (add_pos hs ht) f x := by
  rw [transition_evolve,transition_evolve,evolve_add]

end OperatorDerivativeRewrite.Foundation.HigherHeatSchwartzTransition
