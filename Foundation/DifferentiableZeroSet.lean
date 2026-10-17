import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Transverse zeros are countable; division by a differentiable density cancels almost everywhere. -/
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.DifferentiableZeroSet

theorem transverse_zeros_countable (f f' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x) : {x | f x=0 ∧ f' x≠0}.Countable := by
  have hd : IsDiscrete {x | f x=0 ∧ f' x≠0} := by
    apply isDiscrete_iff_nhdsNE.mpr
    intro x hx
    apply inf_principal_eq_bot.mpr
    have hh : ∀ᶠ y in 𝓝[≠] x, f y≠0 := (hf x).eventually_ne hx.2
    filter_upwards [hh] with y hy
    exact fun h => hy h.1
  exact (IsLindelof.of_coe : IsLindelof {x | f x=0 ∧ f' x≠0}).countable_of_isDiscrete hd

theorem derivative_zero_on_zero_ae (f f' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x) : ∀ᵐ x : ℝ, f x=0 → f' x=0 := by
  have hn := (transverse_zeros_countable f f' hf).measure_zero volume
  have ha : ∀ᵐ x : ℝ, x ∉ {x | f x=0 ∧ f' x≠0} := by
    apply ae_iff.mpr
    simpa only [not_not, mem_setOf_eq] using hn
  filter_upwards [ha] with x hx
  intro hz
  by_contra hne
  exact hx ⟨hz, hne⟩

theorem logarithmic_cancel_ae (f f' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x) :
    (fun x => f x * (-(f' x)/f x)) =ᵐ[volume] (fun x => -(f' x)) := by
  filter_upwards [derivative_zero_on_zero_ae f f' hf] with x hx
  by_cases hz : f x=0
  · simp [hz, hx hz]
  · field_simp

end OperatorDerivativeRewrite.Foundation.DifferentiableZeroSet
