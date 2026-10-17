import Foundation.MarkedConditionalPolynomial

/-! Quartic compensation on the natural filtration of the actual marked renewal process. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.MarkedQuarticCompensation
open MarkedRootRenewalProcess (StateSample probability)
open MarkedRenewalMartingale MarkedConditionalPolynomial

theorem quartic_condExp (a : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    probability[fun ω => process a t ω^4 | history a s] =ᵐ[probability]
      fun ω => process a s ω^4-4*((t-s : ℝ≥0) : ℂ)*(a : ℂ)^4 := by
  classical
  let f : ℕ → StateSample → ℂ := fun j ω =>
    ((Nat.choose 4 j : ℂ)*process a s ω^(4-j))*increment a s t ω^j
  have hi : ∀ j ∈ Finset.range 5, Integrable (f j) probability :=
    fun j _ => power_product_integrable a s t hst _ (4-j) j
  have hs := condExp_finsetSum hi (history a s)
  have hp : (fun ω => process a t ω^4) = ∑ j ∈ Finset.range 5, f j := by
    funext ω
    norm_num [f,Finset.sum_range_succ,increment,Nat.choose]
    ring
  rw [← hp] at hs
  have hall : ∀ᵐ ω ∂probability, ∀ j ∈ Finset.range 5,
      probability[f j | history a s] ω =
        ((Nat.choose 4 j : ℂ)*process a s ω^(4-j))*
          (∫ y : ℂ, y^j ∂ComplexRootPoissonLaw.law (t-s) a) := by
    apply (Finset.eventually_all (Finset.range 5)).mpr
    intro j _
    exact power_product_condExp a s t hst _ (4-j) j
  filter_upwards [hs,hall] with ω hs hall
  rw [hs]
  change (∑ j ∈ Finset.range 5, probability[f j | history a s] ω) = _
  rw [Finset.sum_congr rfl hall]
  norm_num [Finset.sum_range_succ,Nat.choose,compound_mean_zero,
    ComplexRootLowerPolynomialMoments.square_integral,
    ComplexRootLowerPolynomialMoments.cube_integral,
    ComplexRootPoissonQuarticDrift.quartic_integral]
  ring

def compensated (a : ℝ) (t : ℝ≥0) (ω : StateSample) : ℂ :=
  process a t ω^4+4*(t : ℂ)*(a : ℂ)^4

theorem compensated_adapted (a : ℝ) : StronglyAdapted (history a) (compensated a) := by
  intro t
  exact (((process_adapted a t).measurable.pow_const 4).add measurable_const).stronglyMeasurable

theorem compensated_integrable (a : ℝ) (t : ℝ≥0) :
    Integrable (compensated a t) probability :=
  (process_power_integrable a t 4).add (integrable_const _)

theorem compensated_condExp (a : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    probability[compensated a t | history a s] =ᵐ[probability] compensated a s := by
  have he := condExp_add (process_power_integrable a t 4)
    (integrable_const (4*(t : ℂ)*(a : ℂ)^4) :
      Integrable (fun _ : StateSample => 4*(t : ℂ)*(a : ℂ)^4) probability) (history a s)
  rw [condExp_const ((history a).le s)] at he
  have hq := quartic_condExp a s t hst
  have ht : ((t-s : ℝ≥0) : ℂ) = (t : ℂ)-(s : ℂ) := by
    rw [NNReal.coe_sub hst]
    push_cast
    rfl
  filter_upwards [he,hq] with ω he hq
  change probability[compensated a t | history a s] ω = _ at he
  rw [he]
  change probability[fun ω => process a t ω^4 | history a s] ω + _ = _
  rw [hq,ht]
  unfold compensated
  ring

theorem compensated_martingale (a : ℝ) :
    Martingale (compensated a) (history a) probability :=
  ⟨compensated_adapted a,fun s t hst => compensated_condExp a s t hst⟩

end OperatorDerivativeRewrite.Foundation.MarkedQuarticCompensation
