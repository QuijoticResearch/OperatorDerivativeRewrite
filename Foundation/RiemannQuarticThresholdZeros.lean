import Foundation.RealRootedVerticalLimit
import Foundation.RiemannQuarticThresholdEndpoint
import Foundation.RiemannQuarticReality

/-! Actual zero reality at and after the attained eventual threshold, and
nonreal zeros at arbitrarily close earlier times. No endpoint simplicity,
collision or boundedness of the approaching nonreal zeros is assumed. -/
noncomputable section
open Set Filter Metric Complex Polynomial
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticThresholdZeros
open RiemannQuarticFlow RiemannQuarticOpenObstruction RiemannQuarticActualPolynomialLimit
open RiemannQuarticThresholdEndpoint

theorem actual_polynomial_limit_iff_real_zeros (t : ℝ) :
    (∃ P : ℕ → ℝ[X], (∀ n, (P n).Splits) ∧
      TendstoLocallyUniformlyOn
        (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z) (flow t) atTop univ) ↔
    ∀ z : ℂ, flow t z = 0 → z.im = 0 := by
  constructor
  · rintro ⟨P,hP,hlim⟩
    apply RealRootedVerticalLimit.real_zeros_of_locally_uniform_split_polynomials
      P (flow t) (flow_differentiable t) ?_ hP hlim
    exact ⟨0,by simpa using RiemannQuarticReality.flow_ne_zero_on_imaginary_axis t 0⟩
  · exact actual_polynomial_limit_of_real_zeros t

theorem all_zeros_real_at_or_after_threshold (t : ℝ)
    (ht : sInf polynomialLimitStarts ≤ t) :
    ∀ z : ℂ, flow t z = 0 → z.im = 0 :=
  (actual_polynomial_limit_iff_real_zeros t).mp (infimum_mem_actual_starts t ht)

theorem all_zeros_real_at_threshold :
    ∀ z : ℂ, flow (sInf polynomialLimitStarts) z = 0 → z.im = 0 :=
  all_zeros_real_at_or_after_threshold _ le_rfl

theorem nonreal_zeros_arbitrarily_before_threshold (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, sInf polynomialLimitStarts-ε < t ∧ t < sInf polynomialLimitStarts ∧
      ∃ z : ℂ, flow t z = 0 ∧ z.im ≠ 0 := by
  let A := sInf polynomialLimitStarts
  let T := A-ε/2
  have hT : T ∉ polynomialLimitStarts := by
    rw [actual_starts_eq_Ici_infimum]
    simp only [mem_Ici]
    dsimp [T,A]
    linarith
  have hbad : ∃ t : ℝ, T ≤ t ∧ ¬
      (∃ P : ℕ → ℝ[X], (∀ n, (P n).Splits) ∧ TendstoLocallyUniformlyOn
        (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z) (flow t) atTop univ) := by
    simpa only [polynomialLimitStarts,mem_setOf_eq,not_forall,not_imp,exists_prop] using hT
  obtain ⟨t,ht,hbad⟩ := hbad
  have htA : t < A := by
    by_contra h
    exact hbad (infimum_mem_actual_starts t (le_of_not_gt h))
  refine ⟨t,?_,htA,?_⟩
  · dsimp [T] at ht
    dsimp [A] at ht ⊢
    linarith
  · by_contra h
    have hr : ∀ z : ℂ, flow t z = 0 → z.im = 0 := by
      intro z hz
      by_contra hi
      exact h ⟨z,hz,hi⟩
    exact hbad (actual_polynomial_limit_of_real_zeros t hr)

theorem convergent_zeros_at_threshold_are_real (s : ℕ → ℝ) (z : ℕ → ℂ) (w : ℂ)
    (hs : Tendsto s atTop (𝓝 (sInf polynomialLimitStarts)))
    (hz : Tendsto z atTop (𝓝 w)) (hzero : ∀ n, flow (s n) (z n) = 0) :
    flow (sInf polynomialLimitStarts) w = 0 ∧ w.im = 0 := by
  have hc := RiemannQuarticTimeCompact.flow_joint_continuous.continuousAt.tendsto.comp
    (hs.prodMk_nhds hz)
  have he : flow (sInf polynomialLimitStarts) w = 0 := by
    apply tendsto_nhds_unique hc
    change Tendsto (fun n => flow (s n) (z n)) atTop (𝓝 0)
    simpa only [hzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  exact ⟨he,all_zeros_real_at_threshold w he⟩

end OperatorDerivativeRewrite.Foundation.RiemannQuarticThresholdZeros
