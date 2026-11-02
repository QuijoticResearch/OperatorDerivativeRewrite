import Foundation.RiemannRealOrderQuarticLimitZeros
import Foundation.RiemannRealOrderTransitionRate
import Foundation.RiemannQuadraticXiTransfer

noncomputable section
open Set Filter Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannOrderEndpointAudit
open RiemannRealOrderFlow

/-- For1<a<2 the actual all-real property can hold ONLY at the common zero-time Xi slice. -/
theorem fractional_all_real_iff (a : ℝ) (ha : 1<a) (ha2 : a<2) (t : ℝ) :
    (∀ z : ℂ, flow a t z=0 → z.im=0) ↔
      t=0 ∧ (∀ z : ℂ, RiemannEvenFlow.flow 1 0 z=0 → z.im=0) := by
  constructor
  · intro h
    have ht : t=0 := by
      by_contra ht
      obtain ⟨z,hz,hi⟩ :=
        (RiemannRealOrderQuarticLimitZeros.between_one_two_nonreal_zeros_infinite a t ha ha2 ht).nonempty
      exact hi (h z hz)
    refine ⟨ht,?_⟩
    simpa only [ht,flow_zero_time] using h
  · rintro ⟨rfl,h⟩
    simpa only [flow_zero_time] using h

open scoped Classical in
/-- No real-valued infimum of the empty start set is disguised as an infinite threshold. -/
theorem fractional_all_real_time_set (a : ℝ) (ha : 1<a) (ha2 : a<2) :
    {t : ℝ | ∀ z : ℂ, flow a t z=0 → z.im=0}=
      if (∀ z : ℂ, RiemannEvenFlow.flow 1 0 z=0 → z.im=0) then {0} else ∅ := by
  classical
  ext t
  rw [mem_ofPred_eq,fractional_all_real_iff a ha ha2]
  split_ifs <;> simp_all

/-- A genuine endpoint inequality inherited from the UNIFORM absolute fractional remainder.
It is an upper bound on real-axis magnitude, not zero exclusion. -/
theorem quadratic_scaled_decay (t : ℝ) : ∃ C : ℝ, 0≤C ∧ ∀ x : ℝ, 1≤x →
    ‖((x^3:ℝ):ℂ)*RiemannEvenFlow.flow 1 t (x:ℂ)‖≤C*x^(-(1/2:ℝ)) := by
  obtain ⟨C,hC,h⟩ := RiemannRealOrderTransitionRate.actual_absolute_error_uniform_rate t
  refine ⟨C,hC,?_⟩
  intro x hx
  have hx0 : 0<x := by linarith
  have hc := ((RiemannRealOrderRelativeObstruction.scaledValue_continuousAt_one t x hx0).sub
    (Complex.continuous_ofReal.continuousAt.comp
      (RiemannRealOrderFractionalCoefficient.leading_hasDerivAt_one t).continuousAt)).norm
  have hl : Tendsto (fun a : ℝ =>
      ‖RiemannRealOrderRelativeObstruction.scaledValue a t x-
        (RiemannRealOrderFractionalCoefficient.leading a t:ℂ)‖)
      (𝓝[Ioi (1:ℝ)] 1)
      (𝓝 ‖RiemannRealOrderRelativeObstruction.scaledValue 1 t x‖) := by
    simpa only [Pi.sub_apply,Function.comp_def,RiemannRealOrderFractionalCoefficient.leading_one,
      Complex.ofReal_zero,sub_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have he : ∀ᶠ a : ℝ in 𝓝[Ioi (1:ℝ)] 1,
      ‖RiemannRealOrderRelativeObstruction.scaledValue a t x-
        (RiemannRealOrderFractionalCoefficient.leading a t:ℂ)‖≤C*x^(-(1/2:ℝ)) := by
    have hu : ∀ᶠ a : ℝ in 𝓝 (1:ℝ), a<5/4 := Iio_mem_nhds (by norm_num)
    filter_upwards [self_mem_nhdsWithin,hu.filter_mono nhdsWithin_le_nhds] with a ha hau
    exact h a ha hau.le x hx
  have hb := le_of_tendsto hl he
  have hf : flow (1:ℝ) t (x:ℂ)=RiemannEvenFlow.flow 1 t (x:ℂ) := by
    simpa only [Nat.cast_one] using flow_nat 1 t (x:ℂ)
  simpa only [RiemannRealOrderRelativeObstruction.scaledValue,
    show (2:ℝ)*1+1=3 from by norm_num,show (3:ℝ)=(3:ℕ) from rfl,
    Real.rpow_natCast,hf] using hb

end OperatorDerivativeRewrite.Foundation.RiemannOrderEndpointAudit
